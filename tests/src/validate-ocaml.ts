import assert from 'node:assert/strict';
import { createHash } from 'node:crypto';
import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';

import {
  balanceProofShape,
  cbBalanceCommitment,
  cbCanonicalChallenge,
  cbParams,
  cbProve,
  cbRandCommit,
  cbRandCommitKey,
  cbSigmaCommit,
  cbSigmaRespond,
  cbSigmaVerify,
  cbValidMask,
  cbValidParams,
  cbValidResponse,
  cbValidWitness,
  cbVerify,
  ctBignumEncode,
  ctBignumVectorEncode,
  ctMemberProve,
  ctMemberVerify,
  ctMerkleEmpty,
  ctMerkleLeaf,
  ctMerkleMemberProve,
  ctMerkleMemberVerify,
  ctMerkleNode,
  ctMerkleEnvelopeDigest,
  ctMerkleProofDigest,
  ctMerkleProofDigestArgs,
  ctMerkleRoot,
  ctAcceptedRootWindowDigest,
  ctNullifier,
  ctNullifierCanonicalChallenge,
  ctNullifierProve,
  ctNullifierVerify,
  ctProveMerkle,
  ctTransactionContext,
  ctWalletProofRequestDigest,
  ctVerifyScaffold,
  ctVerifyMerkle,
  ctVerifyMerkleArgs,
  ctVerifyMerkleEnvelope,
  ctVerifyMerkleEnvelopeArgs,
  crAmountCommitment,
  crProve,
  listNullifierProof,
  rangeProofShape,
  crVerify,
  nullifierProofShape,
  dilCheckBound,
  dilDecompose,
  dilHighbits,
  dilHintWeight,
  dilLowbits,
  dilMakeHint,
  dilModCentered,
  dilParams,
  dilPower2Round,
  dilUseHint,
  parseCliResult,
  runCli,
} from './isabella-cli.ts';
import { merkleTransactionProofMutations } from './confidential-proof-mutations.ts';

const __filename = fileURLToPath(import.meta.url);
const __dirname = path.dirname(__filename);
const projectRoot = process.env.ISABELLA_PROJECT_ROOT
  ? path.resolve(process.env.ISABELLA_PROJECT_ROOT)
  : path.join(__dirname, '..', '..');
const typeScriptEntry = process.env.ISABELLA_TS_ENTRY
  ? path.resolve(process.env.ISABELLA_TS_ENTRY)
  : path.join(projectRoot, 'isabella.ts', 'dist', 'index.mjs');
const bignumVectorsPath = path.join(projectRoot, 'tests/fixtures/confidential-bignum-vectors.json');
const bignumTransactionVectorsPath = path.join(projectRoot, 'tests/fixtures/confidential-bignum-transaction-vectors.json');
const bigintBalanceVectorsPath = path.join(projectRoot, 'tests/fixtures/confidential-bigint-balance-vectors.json');
const bigintRangeVectorsPath = path.join(projectRoot, 'tests/fixtures/confidential-bigint-range-vectors.json');
const bigintNullifierVectorsPath = path.join(projectRoot, 'tests/fixtures/confidential-bigint-nullifier-vectors.json');

function ensureFileExists(filePath: string, hint: string): void {
  if (!fs.existsSync(filePath)) {
    throw new Error(`${filePath} is missing. ${hint}`);
  }
}

async function loadSdk() {
  ensureFileExists(typeScriptEntry, 'Run `make typescript` before validating the SDKs.');
  return import(pathToFileURL(typeScriptEntry).href);
}

const sdk = await loadSdk();
const trace = process.env.ISABELLA_VALIDATE_TRACE === '1';
const bignumVectors = JSON.parse(fs.readFileSync(bignumVectorsPath, 'utf8')) as {
  scalarCases: Array<{ name: string; decimal: string; encodedHex: string; digest: string }>;
  vectorCases: Array<{ name: string; decimals: string[]; encodedHex: string; digest: string }>;
  rejectedDecimals: string[];
};

type SampleOpening = { msg: number[]; rand: number[] };
type BigintBalanceProofJson = { as: string[][]; zs: string[][] };
type DecimalOpening = { msg: string[]; rand: string[] };
type BigintRangeProofJson = {
  bits: string[][];
  comps: string[][];
  amountAs: string[][];
  amountZs: string[][];
  pairAss: string[][][];
  pairZss: string[][][];
};
type BigintNullifierProofJson = {
  aCommits: string[][];
  aNullifiers: string[][];
  zMsgs: string[][];
  zRands: string[][];
};
type BignumAcceptedRoot = { digest: string; depth: number };
type BignumMerkleMembership = {
  index: number;
  root: string;
  siblings: string[];
  directions: boolean[];
};
type BignumBalanceProofJson = { as: string[][]; zs: string[][] };
type BignumNullifierProofJson = {
  aCommits: string[][];
  aNullifiers: string[][];
  zMsgs: string[][];
  zRands: string[][];
};
type BignumRangeProofJson = {
  bits: string[][];
  comps: string[][];
  amountAs: string[][];
  amountZs: string[][];
  pairAss: string[][][];
  pairZss: string[][][];
};
type BignumMerkleTransactionProofJson = {
  in1Member: BignumMerkleMembership;
  in2Member: BignumMerkleMembership;
  in1Nullifier: BignumNullifierProofJson;
  in2Nullifier: BignumNullifierProofJson;
  balance: BignumBalanceProofJson;
  out1Range: BignumRangeProofJson;
  out2Range: BignumRangeProofJson;
};
type BignumTransactionContextJson = {
  protocolVersion: number;
  networkId: string;
  assetId: number;
  ledgerEpoch: number;
  root: BignumAcceptedRoot;
  publicFee: string;
  cIn1: string[];
  cIn2: string[];
  cOut1: string[];
  cOut2: string[];
  nf1: string[];
  nf2: string[];
};
type BignumAcceptedRootWindowJson = {
  protocolVersion: number;
  networkId: string;
  assetId: number;
  ledgerEpoch: number;
  roots: Array<{ root: BignumAcceptedRoot; validFromEpoch: number; expiresAtEpoch: number }>;
};
type BignumWalletProofRequestJson = {
  context: BignumTransactionContextJson;
  acceptedRoots: BignumAcceptedRoot[];
  spentNullifiers: string[][];
};
type BignumTransactionVectors = {
  ledger: string[][];
  merkleCases: Array<{ name: string; commitment?: string[]; commitments?: string[][]; digest: string }>;
  contextCases: Array<{ name: string; context: BignumTransactionContextJson; digest: string }>;
  merkleProofCases: Array<{ name: string; proof: BignumMerkleTransactionProofJson; digest: string }>;
  envelopeCases: Array<{ name: string; envelope: { context: BignumTransactionContextJson; contextDigest: string; proof: BignumMerkleTransactionProofJson }; digest: string }>;
  acceptedRootWindowCases: Array<{ name: string; window: BignumAcceptedRootWindowJson; digest: string }>;
  walletProofRequestCases: Array<{ name: string; request: BignumWalletProofRequestJson; digest: string }>;
};

function expectOcamlCommandRejected(args: string[], label: string): void {
  const output = runCli(args);
  const parsed = parseCliResult<{ error?: string; result?: unknown }>(output);
  assert.equal(typeof parsed.error, 'string', label);
}

function nonCanonicalIntegerText(value: string): string {
  return value === '0' ? '-0' : `0${value}`;
}

function nonCanonicalFirstInteger(value: string): string {
  return value.replace(/-?\d+/, '-0');
}

const unsafeProtocolInteger = '9007199254740992';

function unsafeFirstInteger(value: string): string {
  return value.replace(/-?\d+/, unsafeProtocolInteger);
}

function integerVecText(values: string[]): string {
  return `[${values.join(',')}]`;
}

function integerMatText(rows: string[][]): string {
  return `[${rows.map(integerVecText).join(',')}]`;
}

function integerCubeText(cubes: string[][][]): string {
  return `[${cubes.map(integerMatText).join(',')}]`;
}

function rangeProofDigest(proof: BigintRangeProofJson): { digest: string; bytes: number } {
  const canonical = JSON.stringify(proof);
  return {
    digest: createHash('sha3-256').update(canonical).digest('hex'),
    bytes: Buffer.byteLength(canonical, 'utf8'),
  };
}

function rangeAmountMask(round: number): string[] {
  return [
    (BigInt((round + 1) % 11) - 5n).toString(),
    (4n - BigInt((round * 3 + 1) % 9)).toString(),
  ];
}

function rangePairMask(round: number, bit: number): string[] {
  return [
    (BigInt((round + bit + 7) % 11) - 5n).toString(),
    (4n - BigInt((round * 3 + bit + 7) % 9)).toString(),
  ];
}

function allBounded(values: number[], bound: number): boolean {
  return values.every(value => Number.isSafeInteger(value) && Math.abs(value) <= bound);
}

function logProgress(message: string): void {
  if (trace) {
    console.log(message);
  }
}

for (const entry of bignumVectors.scalarCases) {
  assert.equal(
    ctBignumEncode(entry.decimal),
    entry.encodedHex,
    `ct-bignum-encode OCaml/fixture parity for ${entry.name}`
  );
  assert.equal(
    sdk.ConfidentialBignum.encodeIntegerHex(entry.decimal),
    entry.encodedHex,
    `ct-bignum-encode TypeScript/fixture parity for ${entry.name}`
  );
}

for (const entry of bignumVectors.vectorCases) {
  assert.equal(
    ctBignumVectorEncode(entry.decimals),
    entry.encodedHex,
    `ct-bignum-vector-encode OCaml/fixture parity for ${entry.name}`
  );
  assert.equal(
    sdk.ConfidentialBignum.encodeIntegerVectorHex(entry.decimals),
    entry.encodedHex,
    `ct-bignum-vector-encode TypeScript/fixture parity for ${entry.name}`
  );
}

for (const decimal of bignumVectors.rejectedDecimals) {
  expectOcamlCommandRejected(['ct-bignum-encode', decimal], `ct-bignum-encode OCaml rejects ${decimal}`);
}

const bignumTransactionVectors = JSON.parse(
  fs.readFileSync(bignumTransactionVectorsPath, 'utf8')
) as BignumTransactionVectors;

function ocamlStringResult(args: string[]): string {
  return parseCliResult<{ result: string }>(runCli(args)).result;
}

function bignumMemberArgs(member: BignumMerkleMembership): string[] {
  return [
    member.index.toString(),
    member.root,
    JSON.stringify(member.siblings),
    integerVecText(member.directions.map((direction) => (direction ? '1' : '0'))),
  ];
}

function bignumProofArgs(proof: BignumMerkleTransactionProofJson): string[] {
  return [
    ...bignumMemberArgs(proof.in1Member),
    ...bignumMemberArgs(proof.in2Member),
    integerMatText(proof.in1Nullifier.aCommits),
    integerMatText(proof.in1Nullifier.aNullifiers),
    integerMatText(proof.in1Nullifier.zMsgs),
    integerMatText(proof.in1Nullifier.zRands),
    integerMatText(proof.in2Nullifier.aCommits),
    integerMatText(proof.in2Nullifier.aNullifiers),
    integerMatText(proof.in2Nullifier.zMsgs),
    integerMatText(proof.in2Nullifier.zRands),
    integerMatText(proof.balance.as),
    integerMatText(proof.balance.zs),
    integerMatText(proof.out1Range.bits),
    integerMatText(proof.out1Range.comps),
    integerMatText(proof.out1Range.amountAs),
    integerMatText(proof.out1Range.amountZs),
    integerCubeText(proof.out1Range.pairAss),
    integerCubeText(proof.out1Range.pairZss),
    integerMatText(proof.out2Range.bits),
    integerMatText(proof.out2Range.comps),
    integerMatText(proof.out2Range.amountAs),
    integerMatText(proof.out2Range.amountZs),
    integerCubeText(proof.out2Range.pairAss),
    integerCubeText(proof.out2Range.pairZss),
  ];
}

function bignumContextArgs(context: BignumTransactionContextJson): string[] {
  return [
    context.protocolVersion.toString(),
    context.networkId,
    context.assetId.toString(),
    context.ledgerEpoch.toString(),
    context.root.digest,
    context.root.depth.toString(),
    context.publicFee,
    integerVecText(context.cIn1),
    integerVecText(context.cIn2),
    integerVecText(context.cOut1),
    integerVecText(context.cOut2),
    integerVecText(context.nf1),
    integerVecText(context.nf2),
  ];
}

function acceptedRootDigests(roots: BignumAcceptedRoot[]): string[] {
  return roots.map((root) => root.digest);
}

function acceptedRootDepths(roots: BignumAcceptedRoot[]): string[] {
  return roots.map((root) => root.depth.toString());
}

function decimalizeBigints(value: unknown): unknown {
  if (typeof value === 'bigint') {
    return value.toString();
  }
  if (Array.isArray(value)) {
    return value.map(decimalizeBigints);
  }
  if (value !== null && typeof value === 'object') {
    return Object.fromEntries(Object.entries(value).map(([key, entry]) => [key, decimalizeBigints(entry)]));
  }
  return value;
}

function bignumOpening(amount: bigint, r0: bigint, r1: bigint): { msg: bigint[]; rand: bigint[] } {
  return { msg: [amount], rand: [r0, r1] };
}

function bignumBitOpenings(amount: bigint, bits: number): Array<{ msg: bigint[]; rand: bigint[] }> {
  return Array.from({ length: bits }, (_, bit) =>
    bignumOpening((amount >> BigInt(bit)) & 1n, BigInt((bit % 3) - 1), BigInt(1 - (bit % 3)))
  );
}

function bignumCompOpenings(bitOpenings: Array<{ msg: bigint[]; rand: bigint[] }>): Array<{ msg: bigint[]; rand: bigint[] }> {
  return bitOpenings.map((opening, index) =>
    bignumOpening(1n - opening.msg[0], BigInt(1 - (index % 2)), BigInt((index % 2) - 1))
  );
}

function bignumOpeningMasks(rounds: number): Array<{ msg: bigint[]; rand: bigint[] }> {
  return Array.from({ length: rounds }, (_, round) =>
    bignumOpening(BigInt((round % 5) - 2), BigInt((round % 7) - 3), BigInt(3 - (round % 7)))
  );
}

function bignumVectorMasks(rounds: number): bigint[][] {
  return Array.from({ length: rounds }, (_, round) => [
    BigInt((round % 7) - 3),
    BigInt(3 - (round % 7)),
  ]);
}

function bignumPairMasks(rounds: number, bits: number): bigint[][][] {
  return Array.from({ length: rounds }, (_, round) =>
    Array.from({ length: bits }, (_, bit) => [
      BigInt(((round + bit) % 7) - 3),
      BigInt(3 - ((round + bit) % 7)),
    ])
  );
}

function makeBignumTransferCase() {
  const tx = sdk.ConfidentialTransactionBigInt;
  const balance = sdk.ConfidentialBalanceBigInt;
  const nullifier = sdk.ConfidentialNullifierBigInt;
  const params = balance.makeParams(2, 2, '4835703278458516765933661', 16n);
  const gamma = 32n;
  const k = 4;
  const rounds = balance.fsRounds();
  const fee = 1n;
  const ck = [
    [3n, 5n, 7n],
    [11n, 13n, 17n],
  ];
  const nk = [
    [19n, 23n, 29n],
    [31n, 37n, 41n],
  ];
  const opIn1 = bignumOpening(9n, 1n, -2n);
  const opIn2 = bignumOpening(7n, -1n, 3n);
  const opOut1 = bignumOpening(10n, 2n, -1n);
  const opOut2 = bignumOpening(5n, -3n, 1n);
  const cIn1 = nullifier.nullifier(params, ck, opIn1);
  const cIn2 = nullifier.nullifier(params, ck, opIn2);
  const cOut1 = nullifier.nullifier(params, ck, opOut1);
  const cOut2 = nullifier.nullifier(params, ck, opOut2);
  const nf1 = nullifier.nullifier(params, nk, opIn1);
  const nf2 = nullifier.nullifier(params, nk, opIn2);
  const out1Bits = bignumBitOpenings(opOut1.msg[0], k);
  const out1Comps = bignumCompOpenings(out1Bits);
  const out2Bits = bignumBitOpenings(opOut2.msg[0], k);
  const out2Comps = bignumCompOpenings(out2Bits);
  const ledger = [cIn1, cIn2, cOut1, cOut2];
  const spent: bigint[][] = [];
  const proof = tx.fsProveMerkleWithFee(
    params,
    gamma,
    k,
    ck,
    nk,
    ledger,
    spent,
    fee,
    cIn1,
    cIn2,
    cOut1,
    cOut2,
    nf1,
    nf2,
    opIn1,
    opIn2,
    opOut1,
    opOut2,
    out1Bits,
    out1Comps,
    out2Bits,
    out2Comps,
    bignumOpeningMasks(rounds),
    bignumOpeningMasks(rounds),
    bignumVectorMasks(rounds),
    bignumVectorMasks(rounds),
    bignumPairMasks(rounds, k),
    bignumVectorMasks(rounds),
    bignumPairMasks(rounds, k)
  );
  assert.ok(proof, 'TypeScript BigInt Merkle proof generation succeeds');
  const root = tx.merkleLedgerRoot(ledger);
  const context = {
    protocolVersion: 1,
    networkId: 'isabella-devnet',
    assetId: 7,
    ledgerEpoch: 42,
    root: { digest: root, depth: proof.in1Member.siblings.length },
    publicFee: fee,
    cIn1,
    cIn2,
    cOut1,
    cOut2,
    nf1,
    nf2,
  };
  return decimalizeBigints({
    params: {
      m: params.m.toString(),
      n2: params.n2.toString(),
      q: params.q,
      beta: params.beta,
      gamma,
      k: k.toString(),
    },
    ck,
    nk,
    ledger,
    spent,
    context,
    contextDigest: tx.transactionContextDigest(context),
    proof,
  }) as {
    params: { m: string; n2: string; q: string; beta: string; gamma: string; k: string };
    ck: string[][];
    nk: string[][];
    ledger: string[][];
    spent: string[][];
    context: BignumTransactionContextJson;
    contextDigest: string;
    proof: BignumMerkleTransactionProofJson;
  };
}

function bignumEnvelopeVerifyArgs(
  testCase: ReturnType<typeof makeBignumTransferCase>,
  options: {
    spent?: string[][];
    expectedFee?: string;
    expectedRootDepth?: string;
    contextDigest?: string;
    proof?: BignumMerkleTransactionProofJson;
  } = {}
): string[] {
  const context = testCase.context;
  return [
    'ct-bignum-verify-merkle-envelope',
    testCase.params.m,
    testCase.params.n2,
    testCase.params.q,
    testCase.params.beta,
    testCase.params.gamma,
    testCase.params.k,
    integerMatText(testCase.ck),
    integerMatText(testCase.nk),
    integerMatText(testCase.ledger),
    integerMatText(options.spent ?? testCase.spent),
    context.protocolVersion.toString(),
    context.networkId,
    context.assetId.toString(),
    context.ledgerEpoch.toString(),
    context.root.digest,
    options.expectedRootDepth ?? context.root.depth.toString(),
    options.expectedFee ?? context.publicFee,
    options.contextDigest ?? testCase.contextDigest,
    ...bignumContextArgs(context),
    ...bignumProofArgs(options.proof ?? testCase.proof),
  ];
}

function ocamlBoolResult(args: string[]): boolean {
  return parseCliResult<{ result: boolean }>(runCli(args)).result;
}

const bignumLeafCase = bignumTransactionVectors.merkleCases.find((entry) => entry.commitment);
assert.ok(bignumLeafCase?.commitment, 'bignum Merkle leaf vector exists');
assert.equal(
  ocamlStringResult(['ct-bignum-merkle-leaf', integerVecText(bignumLeafCase.commitment)]),
  bignumLeafCase.digest,
  'ct-bignum-merkle-leaf OCaml fixture parity'
);
const bignumRootCase = bignumTransactionVectors.merkleCases.find((entry) => entry.commitments);
assert.ok(bignumRootCase?.commitments, 'bignum Merkle root vector exists');
assert.equal(
  ocamlStringResult(['ct-bignum-merkle-root', integerMatText(bignumRootCase.commitments)]),
  bignumRootCase.digest,
  'ct-bignum-merkle-root OCaml fixture parity'
);
const bignumMember = parseCliResult<BignumMerkleMembership>(
  runCli([
    'ct-bignum-merkle-member-prove',
    integerMatText(bignumTransactionVectors.ledger),
    integerVecText(bignumLeafCase.commitment),
  ])
);
assert.equal(bignumMember.root, bignumRootCase.digest, 'ct-bignum-merkle-member-prove OCaml root parity');

for (const entry of bignumTransactionVectors.contextCases) {
  assert.equal(
    ocamlStringResult(['ct-bignum-transaction-context', ...bignumContextArgs(entry.context)]),
    entry.digest,
    `ct-bignum-transaction-context OCaml parity for ${entry.name}`
  );
}

for (const entry of bignumTransactionVectors.merkleProofCases) {
  assert.equal(
    ocamlStringResult(['ct-bignum-merkle-proof-digest', ...bignumProofArgs(entry.proof)]),
    entry.digest,
    `ct-bignum-merkle-proof-digest OCaml parity for ${entry.name}`
  );
}

for (const entry of bignumTransactionVectors.envelopeCases) {
  assert.equal(
    ocamlStringResult([
      'ct-bignum-merkle-envelope-digest',
      entry.envelope.contextDigest,
      ...bignumContextArgs(entry.envelope.context),
      ...bignumProofArgs(entry.envelope.proof),
    ]),
    entry.digest,
    `ct-bignum-merkle-envelope-digest OCaml parity for ${entry.name}`
  );
}

for (const entry of bignumTransactionVectors.acceptedRootWindowCases) {
  const roots = entry.window.roots.map((windowEntry) => windowEntry.root);
  assert.equal(
    ocamlStringResult([
      'ct-bignum-accepted-root-window-digest',
      entry.window.protocolVersion.toString(),
      entry.window.networkId,
      entry.window.assetId.toString(),
      entry.window.ledgerEpoch.toString(),
      JSON.stringify(acceptedRootDigests(roots)),
      integerVecText(acceptedRootDepths(roots)),
      integerVecText(entry.window.roots.map((windowEntry) => windowEntry.validFromEpoch.toString())),
      integerVecText(entry.window.roots.map((windowEntry) => windowEntry.expiresAtEpoch.toString())),
    ]),
    entry.digest,
    `ct-bignum-accepted-root-window-digest OCaml parity for ${entry.name}`
  );
}

for (const entry of bignumTransactionVectors.walletProofRequestCases) {
  assert.equal(
    ocamlStringResult([
      'ct-bignum-wallet-proof-request-digest',
      ...bignumContextArgs(entry.request.context),
      JSON.stringify(acceptedRootDigests(entry.request.acceptedRoots)),
      integerVecText(acceptedRootDepths(entry.request.acceptedRoots)),
      integerMatText(entry.request.spentNullifiers),
    ]),
    entry.digest,
    `ct-bignum-wallet-proof-request-digest OCaml parity for ${entry.name}`
  );
}

const bignumTransferCase = makeBignumTransferCase();
assert.equal(
  ocamlBoolResult(bignumEnvelopeVerifyArgs(bignumTransferCase)),
  true,
  'ct-bignum-verify-merkle-envelope OCaml accepts TypeScript BigInt Merkle proof'
);
assert.equal(
  ocamlBoolResult(bignumEnvelopeVerifyArgs(bignumTransferCase, {
    spent: [bignumTransferCase.context.nf1],
  })),
  false,
  'ct-bignum-verify-merkle-envelope OCaml rejects spent BigInt nullifier'
);
assert.equal(
  ocamlBoolResult(bignumEnvelopeVerifyArgs(bignumTransferCase, {
    expectedFee: (BigInt(bignumTransferCase.context.publicFee) + 1n).toString(),
  })),
  false,
  'ct-bignum-verify-merkle-envelope OCaml rejects wrong bignum fee policy'
);
assert.equal(
  ocamlBoolResult(bignumEnvelopeVerifyArgs(bignumTransferCase, {
    expectedRootDepth: (bignumTransferCase.context.root.depth + 1).toString(),
  })),
  false,
  'ct-bignum-verify-merkle-envelope OCaml rejects wrong bignum root depth policy'
);
assert.equal(
  ocamlBoolResult(bignumEnvelopeVerifyArgs(bignumTransferCase, {
    proof: {
      ...bignumTransferCase.proof,
      in2Member: bignumTransferCase.proof.in1Member,
    },
  })),
  false,
  'ct-bignum-verify-merkle-envelope OCaml rejects reused bignum membership proof'
);

expectOcamlCommandRejected(
  ['ct-bignum-transaction-context', ...bignumContextArgs({
    ...bignumTransactionVectors.contextCases[0].context,
    publicFee: nonCanonicalIntegerText(bignumTransactionVectors.contextCases[0].context.publicFee),
  })],
  'ct-bignum-transaction-context OCaml rejects non-canonical publicFee'
);

const bigintBalanceVectors = JSON.parse(fs.readFileSync(bigintBalanceVectorsPath, 'utf8')) as {
  status: string;
  params: { m: number; n2: number; q: string; beta: string; gamma: string };
  transcript: { fields: string[]; firstRounds: Array<{ round: number; challenge: number }> };
  case: {
    name: string;
    commitmentKey: string[][];
    witness: string[];
    commitment: string[];
    masks: string[][];
    proof: BigintBalanceProofJson;
  };
};

const bigintRangeVectors = JSON.parse(fs.readFileSync(bigintRangeVectorsPath, 'utf8')) as {
  status: string;
  params: { m: number; n2: number; q: string; beta: string; gamma: string; k: number };
  transcript: { fields: string[]; firstRounds: Array<{ round: number; challenge: number }> };
  proofCommitment: {
    digest: string;
    canonicalJsonBytes: number;
    amountRows: number;
    pairRounds: number;
    pairRowsPerRound: number;
    sample: {
      firstAmountAnnouncement: string[];
      firstAmountResponse: string[];
      firstPairAnnouncement: string[];
      firstPairResponse: string[];
    };
  };
  case: {
    name: string;
    commitmentKey: string[][];
    amount: string;
    amountOpening: DecimalOpening;
    amountCommitment: string[];
    bitOpenings: DecimalOpening[];
    compOpenings: DecimalOpening[];
  };
};

const bigintNullifierVectors = JSON.parse(fs.readFileSync(bigintNullifierVectorsPath, 'utf8')) as {
  status: string;
  params: { m: number; n2: number; q: string; beta: string; gamma: string };
  transcript: { fields: string[]; firstRounds: Array<{ round: number; challenge: number }> };
  case: {
    name: string;
    commitmentKey: string[][];
    nullifierKey: string[][];
    opening: DecimalOpening;
    commitment: string[];
    nullifier: string[];
    masks: DecimalOpening[];
    proof: BigintNullifierProofJson;
  };
};

const bigParamsArgs = [
  bigintBalanceVectors.params.m.toString(),
  bigintBalanceVectors.params.n2.toString(),
  bigintBalanceVectors.params.q,
  bigintBalanceVectors.params.beta,
];
const bigGamma = bigintBalanceVectors.params.gamma;
const bigCommitmentKey = integerMatText(bigintBalanceVectors.case.commitmentKey);
const bigCommitment = integerVecText(bigintBalanceVectors.case.commitment);
const bigWitness = integerVecText(bigintBalanceVectors.case.witness);
const bigMasks = integerMatText(bigintBalanceVectors.case.masks);
const bigProofAs = integerMatText(bigintBalanceVectors.case.proof.as);
const bigProofZs = integerMatText(bigintBalanceVectors.case.proof.zs);

assert.equal(bigintBalanceVectors.status, 'typescript-reference-with-native-preview-parity');
assert.deepEqual(
  parseCliResult<{ result: string[] }>(runCli([
    'ct-balance-bigint-rand-commit',
    ...bigParamsArgs,
    bigCommitmentKey,
    bigWitness,
  ])).result,
  bigintBalanceVectors.case.commitment,
  `ct-balance-bigint-rand-commit OCaml/fixture parity for ${bigintBalanceVectors.case.name}`
);
assert.deepEqual(
  parseCliResult<{ result: string[] }>(runCli([
    'ct-balance-bigint-fs-fields',
    bigCommitmentKey,
    bigCommitment,
    bigProofAs,
  ])).result,
  bigintBalanceVectors.transcript.fields,
  `ct-balance-bigint-fs-fields OCaml/fixture parity for ${bigintBalanceVectors.case.name}`
);
assert.deepEqual(
  parseCliResult<{ result: number[] }>(runCli([
    'ct-balance-bigint-fs-challenges',
    ...bigParamsArgs,
    bigCommitmentKey,
    bigCommitment,
    bigProofAs,
    bigintBalanceVectors.transcript.firstRounds.length.toString(),
  ])).result,
  bigintBalanceVectors.transcript.firstRounds.map((entry) => entry.challenge),
  `ct-balance-bigint-fs-challenges OCaml/fixture parity for ${bigintBalanceVectors.case.name}`
);
assert.equal(
  parseCliResult<{ result: boolean }>(runCli([
    'ct-balance-bigint-verify',
    ...bigParamsArgs,
    bigGamma,
    bigCommitmentKey,
    bigCommitment,
    bigProofAs,
    bigProofZs,
  ])).result,
  true,
  `ct-balance-bigint-verify OCaml accepts ${bigintBalanceVectors.case.name}`
);
assert.deepEqual(
  parseCliResult<{ result: BigintBalanceProofJson }>(runCli([
    'ct-balance-bigint-prove',
    ...bigParamsArgs,
    bigGamma,
    bigCommitmentKey,
    bigCommitment,
    bigWitness,
    bigMasks,
  ])).result,
  bigintBalanceVectors.case.proof,
  `ct-balance-bigint-prove OCaml/fixture parity for ${bigintBalanceVectors.case.name}`
);
assert.equal(
  parseCliResult<{ result: boolean }>(runCli([
    'ct-balance-bigint-verify',
    ...bigParamsArgs,
    bigGamma,
    bigCommitmentKey,
    integerVecText([
      (BigInt(bigintBalanceVectors.case.commitment[0]) + 1n).toString(),
      ...bigintBalanceVectors.case.commitment.slice(1),
    ]),
    bigProofAs,
    bigProofZs,
  ])).result,
  false,
  `ct-balance-bigint-verify OCaml rejects tampered q83 commitment for ${bigintBalanceVectors.case.name}`
);
console.log('validate-ocaml: confidential BigInt balance q83 preview surface passed');

const bigRangeParamsArgs = [
  bigintRangeVectors.params.m.toString(),
  bigintRangeVectors.params.n2.toString(),
  bigintRangeVectors.params.q,
  bigintRangeVectors.params.beta,
];
const bigRangeGamma = bigintRangeVectors.params.gamma;
const bigRangeK = bigintRangeVectors.params.k.toString();
const bigRangeCommitmentKey = integerMatText(bigintRangeVectors.case.commitmentKey);
const bigRangeAmountCommitment = integerVecText(bigintRangeVectors.case.amountCommitment);
const bigRangeAmountRand = integerVecText(bigintRangeVectors.case.amountOpening.rand);
const bigRangeBits = integerVecText(bigintRangeVectors.case.bitOpenings.map((entry) => entry.msg[0]));
const bigRangeBitRands = integerMatText(bigintRangeVectors.case.bitOpenings.map((entry) => entry.rand));
const bigRangeComps = integerVecText(bigintRangeVectors.case.compOpenings.map((entry) => entry.msg[0]));
const bigRangeCompRands = integerMatText(bigintRangeVectors.case.compOpenings.map((entry) => entry.rand));
const bigRangeAmountMasks = Array.from(
  { length: bigintRangeVectors.transcript.firstRounds.length === 0 ? 128 : bigintRangeVectors.proofCommitment.amountRows },
  (_, round) => rangeAmountMask(round)
);
const bigRangePairMasks = Array.from({ length: bigintRangeVectors.proofCommitment.pairRounds }, (_, round) =>
  Array.from({ length: bigintRangeVectors.params.k }, (_, bit) => rangePairMask(round, bit))
);
const bigRangeAmountMasksText = integerMatText(bigRangeAmountMasks);
const bigRangePairMasksText = integerCubeText(bigRangePairMasks);

assert.equal(bigintRangeVectors.status, 'typescript-reference-with-native-preview-parity');
const bigRangeProof = parseCliResult<{ result: BigintRangeProofJson }>(runCli([
  'ct-range-bigint-prove',
  ...bigRangeParamsArgs,
  bigRangeGamma,
  bigRangeK,
  bigRangeCommitmentKey,
  bigRangeAmountCommitment,
  bigintRangeVectors.case.amount,
  bigRangeAmountRand,
  bigRangeBits,
  bigRangeBitRands,
  bigRangeComps,
  bigRangeCompRands,
  bigRangeAmountMasksText,
  bigRangePairMasksText,
])).result;
const bigRangeProofDigest = rangeProofDigest(bigRangeProof);
assert.equal(bigRangeProofDigest.digest, bigintRangeVectors.proofCommitment.digest);
assert.equal(bigRangeProofDigest.bytes, bigintRangeVectors.proofCommitment.canonicalJsonBytes);
assert.equal(bigRangeProof.amountAs.length, bigintRangeVectors.proofCommitment.amountRows);
assert.equal(bigRangeProof.pairAss.length, bigintRangeVectors.proofCommitment.pairRounds);
assert.equal(bigRangeProof.pairAss[0].length, bigintRangeVectors.proofCommitment.pairRowsPerRound);
assert.deepEqual(bigRangeProof.amountAs[0], bigintRangeVectors.proofCommitment.sample.firstAmountAnnouncement);
assert.deepEqual(bigRangeProof.amountZs[0], bigintRangeVectors.proofCommitment.sample.firstAmountResponse);
assert.deepEqual(bigRangeProof.pairAss[0][0], bigintRangeVectors.proofCommitment.sample.firstPairAnnouncement);
assert.deepEqual(bigRangeProof.pairZss[0][0], bigintRangeVectors.proofCommitment.sample.firstPairResponse);
assert.deepEqual(
  parseCliResult<{ result: string[] }>(runCli([
    'ct-range-bigint-fs-fields',
    bigRangeCommitmentKey,
    bigRangeAmountCommitment,
    integerMatText(bigRangeProof.bits),
    integerMatText(bigRangeProof.comps),
    integerMatText(bigRangeProof.amountAs),
    integerCubeText(bigRangeProof.pairAss),
  ])).result,
  bigintRangeVectors.transcript.fields,
  `ct-range-bigint-fs-fields OCaml/fixture parity for ${bigintRangeVectors.case.name}`
);
assert.deepEqual(
  parseCliResult<{ result: number[] }>(runCli([
    'ct-range-bigint-fs-challenges',
    ...bigRangeParamsArgs,
    bigRangeCommitmentKey,
    bigRangeAmountCommitment,
    integerMatText(bigRangeProof.bits),
    integerMatText(bigRangeProof.comps),
    integerMatText(bigRangeProof.amountAs),
    integerCubeText(bigRangeProof.pairAss),
    bigintRangeVectors.transcript.firstRounds.length.toString(),
  ])).result,
  bigintRangeVectors.transcript.firstRounds.map((entry) => entry.challenge),
  `ct-range-bigint-fs-challenges OCaml/fixture parity for ${bigintRangeVectors.case.name}`
);
assert.equal(
  parseCliResult<{ result: boolean }>(runCli([
    'ct-range-bigint-verify',
    ...bigRangeParamsArgs,
    bigRangeGamma,
    bigRangeK,
    bigRangeCommitmentKey,
    bigRangeAmountCommitment,
    integerMatText(bigRangeProof.bits),
    integerMatText(bigRangeProof.comps),
    integerMatText(bigRangeProof.amountAs),
    integerMatText(bigRangeProof.amountZs),
    integerCubeText(bigRangeProof.pairAss),
    integerCubeText(bigRangeProof.pairZss),
  ])).result,
  true,
  `ct-range-bigint-verify OCaml accepts ${bigintRangeVectors.case.name}`
);
assert.equal(
  parseCliResult<{ result: boolean }>(runCli([
    'ct-range-bigint-verify',
    ...bigRangeParamsArgs,
    bigRangeGamma,
    bigRangeK,
    bigRangeCommitmentKey,
    integerVecText([
      (BigInt(bigintRangeVectors.case.amountCommitment[0]) + 1n).toString(),
      ...bigintRangeVectors.case.amountCommitment.slice(1),
    ]),
    integerMatText(bigRangeProof.bits),
    integerMatText(bigRangeProof.comps),
    integerMatText(bigRangeProof.amountAs),
    integerMatText(bigRangeProof.amountZs),
    integerCubeText(bigRangeProof.pairAss),
    integerCubeText(bigRangeProof.pairZss),
  ])).result,
  false,
  `ct-range-bigint-verify OCaml rejects tampered q83 amount commitment for ${bigintRangeVectors.case.name}`
);
console.log('validate-ocaml: confidential BigInt range q83 preview surface passed');

const bigNullifierParamsArgs = [
  bigintNullifierVectors.params.m.toString(),
  bigintNullifierVectors.params.n2.toString(),
  bigintNullifierVectors.params.q,
  bigintNullifierVectors.params.beta,
];
const bigNullifierGamma = bigintNullifierVectors.params.gamma;
const bigNullifierCommitmentKey = integerMatText(bigintNullifierVectors.case.commitmentKey);
const bigNullifierKey = integerMatText(bigintNullifierVectors.case.nullifierKey);
const bigNullifierCommitment = integerVecText(bigintNullifierVectors.case.commitment);
const bigNullifier = integerVecText(bigintNullifierVectors.case.nullifier);
const bigNullifierAmount = bigintNullifierVectors.case.opening.msg[0];
const bigNullifierRand = integerVecText(bigintNullifierVectors.case.opening.rand);
const bigNullifierYMsgs = integerVecText(bigintNullifierVectors.case.masks.map((entry) => entry.msg[0]));
const bigNullifierYRands = integerMatText(bigintNullifierVectors.case.masks.map((entry) => entry.rand));
const bigNullifierProof = bigintNullifierVectors.case.proof;
const bigNullifierACommits = integerMatText(bigNullifierProof.aCommits);
const bigNullifierANullifiers = integerMatText(bigNullifierProof.aNullifiers);
const bigNullifierZMsgs = integerMatText(bigNullifierProof.zMsgs);
const bigNullifierZRands = integerMatText(bigNullifierProof.zRands);

assert.equal(bigintNullifierVectors.status, 'typescript-reference-with-native-preview-parity');
assert.deepEqual(
  parseCliResult<{ result: string[] }>(runCli([
    'ct-nullifier-bigint',
    ...bigNullifierParamsArgs,
    bigNullifierKey,
    bigNullifierAmount,
    bigNullifierRand,
  ])).result,
  bigintNullifierVectors.case.nullifier,
  `ct-nullifier-bigint OCaml/fixture parity for ${bigintNullifierVectors.case.name}`
);
assert.deepEqual(
  parseCliResult<{ result: string[] }>(runCli([
    'ct-nullifier-bigint-fs-fields',
    bigNullifierCommitmentKey,
    bigNullifierKey,
    bigNullifierCommitment,
    bigNullifier,
    bigNullifierACommits,
    bigNullifierANullifiers,
  ])).result,
  bigintNullifierVectors.transcript.fields,
  `ct-nullifier-bigint-fs-fields OCaml/fixture parity for ${bigintNullifierVectors.case.name}`
);
assert.deepEqual(
  parseCliResult<{ result: number[] }>(runCli([
    'ct-nullifier-bigint-fs-challenges',
    ...bigNullifierParamsArgs,
    bigNullifierCommitmentKey,
    bigNullifierKey,
    bigNullifierCommitment,
    bigNullifier,
    bigNullifierACommits,
    bigNullifierANullifiers,
    bigintNullifierVectors.transcript.firstRounds.length.toString(),
  ])).result,
  bigintNullifierVectors.transcript.firstRounds.map((entry) => entry.challenge),
  `ct-nullifier-bigint-fs-challenges OCaml/fixture parity for ${bigintNullifierVectors.case.name}`
);
assert.deepEqual(
  parseCliResult<{ result: BigintNullifierProofJson }>(runCli([
    'ct-nullifier-bigint-prove',
    ...bigNullifierParamsArgs,
    bigNullifierGamma,
    bigNullifierCommitmentKey,
    bigNullifierKey,
    bigNullifierCommitment,
    bigNullifier,
    bigNullifierAmount,
    bigNullifierRand,
    bigNullifierYMsgs,
    bigNullifierYRands,
  ])).result,
  bigNullifierProof,
  `ct-nullifier-bigint-prove OCaml/fixture parity for ${bigintNullifierVectors.case.name}`
);
assert.equal(
  parseCliResult<{ result: boolean }>(runCli([
    'ct-nullifier-bigint-verify',
    ...bigNullifierParamsArgs,
    bigNullifierGamma,
    bigNullifierCommitmentKey,
    bigNullifierKey,
    bigNullifierCommitment,
    bigNullifier,
    bigNullifierACommits,
    bigNullifierANullifiers,
    bigNullifierZMsgs,
    bigNullifierZRands,
  ])).result,
  true,
  `ct-nullifier-bigint-verify OCaml accepts ${bigintNullifierVectors.case.name}`
);
assert.equal(
  parseCliResult<{ result: boolean }>(runCli([
    'ct-nullifier-bigint-verify',
    ...bigNullifierParamsArgs,
    bigNullifierGamma,
    bigNullifierCommitmentKey,
    bigNullifierKey,
    integerVecText([
      (BigInt(bigintNullifierVectors.case.commitment[0]) + 1n).toString(),
      ...bigintNullifierVectors.case.commitment.slice(1),
    ]),
    bigNullifier,
    bigNullifierACommits,
    bigNullifierANullifiers,
    bigNullifierZMsgs,
    bigNullifierZRands,
  ])).result,
  false,
  `ct-nullifier-bigint-verify OCaml rejects tampered q83 commitment for ${bigintNullifierVectors.case.name}`
);
assert.equal(
  parseCliResult<{ result: boolean }>(runCli([
    'ct-nullifier-bigint-verify',
    ...bigNullifierParamsArgs,
    bigNullifierGamma,
    bigNullifierCommitmentKey,
    bigNullifierKey,
    bigNullifierCommitment,
    integerVecText([
      (BigInt(bigintNullifierVectors.case.nullifier[0]) + 1n).toString(),
      ...bigintNullifierVectors.case.nullifier.slice(1),
    ]),
    bigNullifierACommits,
    bigNullifierANullifiers,
    bigNullifierZMsgs,
    bigNullifierZRands,
  ])).result,
  false,
  `ct-nullifier-bigint-verify OCaml rejects tampered q83 nullifier for ${bigintNullifierVectors.case.name}`
);
console.log('validate-ocaml: confidential BigInt nullifier q83 preview surface passed');

const modCenteredCases = [
  { x: 7, q: 5 },
  { x: 8, q: 5 },
  { x: -3, q: 5 },
  { x: 130, q: 256 },
];

for (const { x, q } of modCenteredCases) {
  const actual = parseCliResult<{ result: number }>(runCli(['mod-centered', x.toString(), q.toString()])).result;
  assert.equal(actual, sdk.Zq.modCentered(x, q), `mod-centered(${x}, ${q})`);
}

const distCases = [
  { q: 17, x: 0 },
  { q: 17, x: 9 },
  { q: 256, x: 130 },
];

for (const { q, x } of distCases) {
  const actual = parseCliResult<{ result: number }>(runCli(['dist0', q.toString(), x.toString()])).result;
  assert.equal(actual, sdk.Zq.dist0(q, x), `dist0(${q}, ${x})`);
}

for (const q of [17, 97, 256]) {
  for (const bit of [false, true]) {
    const encoded = parseCliResult<{ result: number }>(runCli(['encode-bit', q.toString(), bit ? '1' : '0'])).result;
    assert.equal(encoded, sdk.Zq.encodeBit(q, bit), `encode-bit(${q}, ${bit})`);

    const decoded = parseCliResult<{ result: boolean }>(runCli(['decode-bit', q.toString(), encoded.toString()])).result;
    assert.equal(decoded, sdk.Zq.decodeBit(q, encoded), `decode-bit(${q}, ${encoded})`);
  }
}

const dotCases = [
  { left: [1, 2, 3], right: [4, 5, 6] },
  { left: [2, -1, 5], right: [3, 0, -2] },
];

for (const { left, right } of dotCases) {
  const actual = parseCliResult<{ result: number }>(
    runCli(['inner-prod', JSON.stringify(left), JSON.stringify(right)])
  ).result;
  assert.equal(actual, sdk.Vec.dot(left, right), `inner-prod(${left}, ${right})`);
}

const addCases = [
  { left: [1, 2, 3], right: [4, 5, 6] },
  { left: [0, -2, 9], right: [7, 3, -1] },
];

for (const { left, right } of addCases) {
  const actual = parseCliResult<{ result: number[] }>(
    runCli(['vec-add', JSON.stringify(left), JSON.stringify(right)])
  ).result;
  assert.deepEqual(actual, sdk.Vec.add(left, right), `vec-add(${left}, ${right})`);
}

const transposeCases = [
  [
    [1, 2, 3],
    [4, 5, 6],
  ],
  [
    [7, 8],
    [9, 10],
    [11, 12],
  ],
  [[42, -1, 0]],
];

for (const matrix of transposeCases) {
  const actual = parseCliResult<{ result: number[][] }>(
    runCli(['transpose', JSON.stringify(matrix)])
  ).result;
  assert.deepEqual(actual, sdk.Mat.transpose(matrix), `transpose(${JSON.stringify(matrix)})`);
}

const matrixCase = {
  matrix: [
    [1, 2],
    [3, 4],
  ],
  vector: [5, 6],
  q: 10,
};

const matrixActual = parseCliResult<{ result: number[] }>(
  runCli([
    'mat-vec-mult',
    JSON.stringify(matrixCase.matrix),
    JSON.stringify(matrixCase.vector),
    matrixCase.q.toString(),
  ])
).result;
assert.deepEqual(
  matrixActual,
  sdk.Zq.matVecMultMod(matrixCase.matrix, matrixCase.vector, matrixCase.q),
  'mat-vec-mult shared surface'
);

for (const variant of ['44', '65', '87'] as const) {
  assert.deepEqual(dilParams(variant), sdk.Dilithium.params(variant), `dil-params(${variant})`);
}

const dilithiumModCases = [
  { r: 8, m: 16 },
  { r: 9, m: 16 },
  { r: -3, m: 16 },
  { r: 1234567, m: 190464 },
];

for (const { r, m } of dilithiumModCases) {
  assert.equal(dilModCentered(r, m), sdk.Dilithium.modCentered(r, m), `dil-mod-centered(${r}, ${m})`);
}

const power2RoundCases = [
  { r: 0, d: 13 },
  { r: 100000, d: 13 },
  { r: 1234567, d: 13 },
];

for (const { r, d } of power2RoundCases) {
  const expected = dilPower2Round(r, d);
  assert.deepEqual(
    sdk.Dilithium.power2Round(r, d),
    { r1: expected.r1, r0: expected.r0 },
    `dil-power2round(${r}, ${d})`
  );
}

const alpha44 = 2 * sdk.Dilithium.params('44').gamma2;
const decomposeCases = [0, 1000, 100000, 500000, 1234567, sdk.Dilithium.params('44').q - 1];

for (const r of decomposeCases) {
  const expected = dilDecompose(r, alpha44);
  const actual = sdk.Dilithium.decompose(r, alpha44);
  assert.deepEqual(actual, { r1: expected.r1, r0: expected.r0 }, `dil-decompose(${r}, ${alpha44})`);
  assert.equal(sdk.Dilithium.highBits(r, alpha44), dilHighbits(r, alpha44), `dil-highbits(${r}, ${alpha44})`);
  assert.equal(sdk.Dilithium.lowBits(r, alpha44), dilLowbits(r, alpha44), `dil-lowbits(${r}, ${alpha44})`);
}

const hintCases = [
  { z: 0, r: 100000, alpha: alpha44 },
  { z: 2000, r: 100000, alpha: alpha44 },
  { z: -5000, r: 765432, alpha: alpha44 },
];

for (const { z, r, alpha } of hintCases) {
  const expectedHint = dilMakeHint(z, r, alpha);
  assert.equal(sdk.Dilithium.makeHint(z, r, alpha), expectedHint, `dil-makehint(${z}, ${r}, ${alpha})`);
  assert.equal(
    sdk.Dilithium.useHint(expectedHint, r, alpha),
    dilUseHint(expectedHint, r, alpha),
    `dil-usehint(${expectedHint}, ${r}, ${alpha})`
  );
}

const boundCases = [
  { value: 77, bound: 78 },
  { value: 78, bound: 78 },
  { value: -120, bound: 121 },
];

for (const { value, bound } of boundCases) {
  assert.equal(
    sdk.Dilithium.checkBound(value, bound),
    dilCheckBound(value, bound),
    `dil-check-bound(${value}, ${bound})`
  );
}

const hints = [
  [1, 0, 1],
  [0, 1, 0],
  [1, 1],
];
assert.equal(sdk.Dilithium.hintWeight(hints), dilHintWeight(hints), 'dil-hint-weight shared surface');

console.log('validate-ocaml: base arithmetic, linear algebra, and Dilithium shared surfaces passed');

const cbParamsCase = { m: 2, n2: 2, q: 17, beta: 3, gamma: 5 };
const cbKey = [
  [1, 0, 0],
  [0, 1, 0],
];
const cbWitness = [1, 2];
const cbMask = [0, 1];
const cbMasks = Array.from({ length: sdk.ConfidentialBalance.fsRounds() }, () => cbMask);
const cbCommitment = sdk.ConfidentialBalance.randCommit(
  sdk.ConfidentialBalance.makeParams(cbParamsCase.m, cbParamsCase.n2, cbParamsCase.q, cbParamsCase.beta),
  cbKey,
  cbWitness
);

assert.deepEqual(
  cbParams(cbParamsCase.m, cbParamsCase.n2, cbParamsCase.q, cbParamsCase.beta),
  sdk.ConfidentialBalance.makeParams(cbParamsCase.m, cbParamsCase.n2, cbParamsCase.q, cbParamsCase.beta),
  'cb-params shared surface'
);
assert.equal(
  cbValidParams(cbParamsCase.m, cbParamsCase.n2, cbParamsCase.q, cbParamsCase.beta),
  sdk.ConfidentialBalance.validScalarParams(
    sdk.ConfidentialBalance.makeParams(cbParamsCase.m, cbParamsCase.n2, cbParamsCase.q, cbParamsCase.beta)
  ),
  'cb-valid-params shared surface'
);
assert.deepEqual(
  cbRandCommitKey(cbParamsCase.m, cbParamsCase.n2, cbParamsCase.q, cbParamsCase.beta, cbKey),
  sdk.ConfidentialBalance.randCommitKey(
    sdk.ConfidentialBalance.makeParams(cbParamsCase.m, cbParamsCase.n2, cbParamsCase.q, cbParamsCase.beta),
    cbKey
  ),
  'cb-rand-commit-key shared surface'
);
assert.deepEqual(
  cbRandCommit(cbParamsCase.m, cbParamsCase.n2, cbParamsCase.q, cbParamsCase.beta, cbKey, cbWitness),
  cbCommitment,
  'cb-rand-commit shared surface'
);
assert.equal(
  cbValidWitness(cbParamsCase.m, cbParamsCase.n2, cbParamsCase.q, cbParamsCase.beta, cbWitness),
  sdk.ConfidentialBalance.validWitness(
    sdk.ConfidentialBalance.makeParams(cbParamsCase.m, cbParamsCase.n2, cbParamsCase.q, cbParamsCase.beta),
    cbWitness
  ),
  'cb-valid-witness shared surface'
);
assert.equal(
  cbValidMask(cbParamsCase.m, cbParamsCase.n2, cbParamsCase.q, cbParamsCase.beta, cbParamsCase.gamma, cbMask),
  sdk.ConfidentialBalance.validMask(
    sdk.ConfidentialBalance.makeParams(cbParamsCase.m, cbParamsCase.n2, cbParamsCase.q, cbParamsCase.beta),
    cbParamsCase.gamma,
    cbMask
  ),
  'cb-valid-mask shared surface'
);

const ocamlSampleBalanceMask = parseCliResult<{ result: number[] }>(
  runCli([
    'cb-sample-mask',
    cbParamsCase.m.toString(),
    cbParamsCase.n2.toString(),
    cbParamsCase.q.toString(),
    cbParamsCase.beta.toString(),
    cbParamsCase.gamma.toString(),
  ])
).result;
assert.equal(ocamlSampleBalanceMask.length, cbParamsCase.n2, 'cb-sample-mask length');
assert.ok(allBounded(ocamlSampleBalanceMask, cbParamsCase.gamma), 'cb-sample-mask bound');
assert.ok(
  sdk.ConfidentialBalance.validMask(
    sdk.ConfidentialBalance.makeParams(cbParamsCase.m, cbParamsCase.n2, cbParamsCase.q, cbParamsCase.beta),
    cbParamsCase.gamma,
    ocamlSampleBalanceMask
  ),
  'cb-sample-mask valid mask'
);

const ocamlSampleBalanceMasks = parseCliResult<{ result: number[][] }>(
  runCli([
    'cb-sample-masks',
    cbParamsCase.m.toString(),
    cbParamsCase.n2.toString(),
    cbParamsCase.q.toString(),
    cbParamsCase.beta.toString(),
    cbParamsCase.gamma.toString(),
    '4',
  ])
).result;
assert.equal(ocamlSampleBalanceMasks.length, 4, 'cb-sample-masks count');
assert.ok(
  ocamlSampleBalanceMasks.every(mask => mask.length === cbParamsCase.n2 && allBounded(mask, cbParamsCase.gamma)),
  'cb-sample-masks shape and bound'
);

const ocamlSampleOpening = parseCliResult<{ result: SampleOpening }>(
  runCli(['ct-sample-opening', '1', cbParamsCase.n2.toString(), cbParamsCase.gamma.toString()])
).result;
assert.equal(ocamlSampleOpening.msg.length, 1, 'ct-sample-opening msg length');
assert.equal(ocamlSampleOpening.rand.length, cbParamsCase.n2, 'ct-sample-opening rand length');
assert.ok(allBounded(ocamlSampleOpening.msg, cbParamsCase.gamma), 'ct-sample-opening msg bound');
assert.ok(allBounded(ocamlSampleOpening.rand, cbParamsCase.gamma), 'ct-sample-opening rand bound');

const ocamlSampleOpenings = parseCliResult<{ result: SampleOpening[] }>(
  runCli([
    'ct-sample-openings',
    '4',
    '1',
    cbParamsCase.n2.toString(),
    cbParamsCase.gamma.toString(),
  ])
).result;
assert.equal(ocamlSampleOpenings.length, 4, 'ct-sample-openings count');
assert.ok(
  ocamlSampleOpenings.every(mask =>
    mask.msg.length === 1 &&
    mask.rand.length === cbParamsCase.n2 &&
    allBounded(mask.msg, cbParamsCase.gamma) &&
    allBounded(mask.rand, cbParamsCase.gamma)
  ),
  'ct-sample-openings shape and bound'
);

const ocamlSampleNullifierMask = parseCliResult<{ result: SampleOpening }>(
  runCli([
    'ct-sample-nullifier-mask',
    cbParamsCase.m.toString(),
    cbParamsCase.n2.toString(),
    cbParamsCase.q.toString(),
    cbParamsCase.beta.toString(),
    cbParamsCase.gamma.toString(),
  ])
).result;
assert.equal(ocamlSampleNullifierMask.msg.length, 1, 'ct-sample-nullifier-mask msg length');
assert.equal(ocamlSampleNullifierMask.rand.length, cbParamsCase.n2, 'ct-sample-nullifier-mask rand length');
assert.ok(allBounded(ocamlSampleNullifierMask.msg, cbParamsCase.gamma), 'ct-sample-nullifier-mask msg bound');
assert.ok(allBounded(ocamlSampleNullifierMask.rand, cbParamsCase.gamma), 'ct-sample-nullifier-mask rand bound');

const ocamlSampleNullifierMasks = parseCliResult<{ result: SampleOpening[] }>(
  runCli([
    'ct-sample-nullifier-masks',
    cbParamsCase.m.toString(),
    cbParamsCase.n2.toString(),
    cbParamsCase.q.toString(),
    cbParamsCase.beta.toString(),
    cbParamsCase.gamma.toString(),
    '4',
  ])
).result;
assert.equal(ocamlSampleNullifierMasks.length, 4, 'ct-sample-nullifier-masks count');
assert.ok(
  ocamlSampleNullifierMasks.every(mask =>
    mask.msg.length === 1 &&
    mask.rand.length === cbParamsCase.n2 &&
    allBounded(mask.msg, cbParamsCase.gamma) &&
    allBounded(mask.rand, cbParamsCase.gamma)
  ),
  'ct-sample-nullifier-masks shape and bound'
);

const cbExpectedChallenge = sdk.ConfidentialBalance.canonicalChallenge(
  sdk.ConfidentialBalance.makeParams(cbParamsCase.m, cbParamsCase.n2, cbParamsCase.q, cbParamsCase.beta),
  cbKey,
  cbCommitment,
  sdk.ConfidentialBalance.sigmaCommit(
    sdk.ConfidentialBalance.makeParams(cbParamsCase.m, cbParamsCase.n2, cbParamsCase.q, cbParamsCase.beta),
    cbKey,
    cbMask
  )
);
const cbSigmaA = cbSigmaCommit(cbParamsCase.m, cbParamsCase.n2, cbParamsCase.q, cbParamsCase.beta, cbKey, cbMask);
const cbSigmaZ = cbSigmaRespond(cbWitness, cbMask, cbExpectedChallenge);
assert.equal(
  cbValidResponse(
    cbParamsCase.m,
    cbParamsCase.n2,
    cbParamsCase.q,
    cbParamsCase.beta,
    cbParamsCase.gamma,
    cbExpectedChallenge,
    cbSigmaZ
  ),
  sdk.ConfidentialBalance.validResponse(
    sdk.ConfidentialBalance.makeParams(cbParamsCase.m, cbParamsCase.n2, cbParamsCase.q, cbParamsCase.beta),
    cbParamsCase.gamma,
    cbExpectedChallenge,
    cbSigmaZ
  ),
  'cb-valid-response shared surface'
);
assert.deepEqual(
  cbBalanceCommitment([8, 3], [4, 6], [5, 1], [7, 2], cbParamsCase.q),
  sdk.ConfidentialBalance.balanceCommitment([8, 3], [4, 6], [5, 1], [7, 2], cbParamsCase.q),
  'cb-balance-commitment shared surface'
);
assert.equal(
  cbCanonicalChallenge(
    cbParamsCase.m,
    cbParamsCase.n2,
    cbParamsCase.q,
    cbParamsCase.beta,
    cbKey,
    cbCommitment,
    cbSigmaA
  ),
  cbExpectedChallenge,
  'cb-canonical-challenge shared surface'
);
assert.deepEqual(
  cbSigmaA,
  sdk.ConfidentialBalance.sigmaCommit(
    sdk.ConfidentialBalance.makeParams(cbParamsCase.m, cbParamsCase.n2, cbParamsCase.q, cbParamsCase.beta),
    cbKey,
    cbMask
  ),
  'cb-sigma-commit shared surface'
);
assert.deepEqual(
  cbSigmaZ,
  sdk.ConfidentialBalance.sigmaRespond(cbWitness, cbMask, cbExpectedChallenge),
  'cb-sigma-respond shared surface'
);
assert.equal(
  cbSigmaVerify(
    cbParamsCase.m,
    cbParamsCase.n2,
    cbParamsCase.q,
    cbParamsCase.beta,
    cbParamsCase.gamma,
    cbKey,
    cbCommitment,
    cbSigmaA,
    cbExpectedChallenge,
    cbSigmaZ
  ),
  sdk.ConfidentialBalance.sigmaVerify(
    sdk.ConfidentialBalance.makeParams(cbParamsCase.m, cbParamsCase.n2, cbParamsCase.q, cbParamsCase.beta),
    cbParamsCase.gamma,
    cbKey,
    cbCommitment,
    cbSigmaA,
    cbExpectedChallenge,
    cbSigmaZ
  ),
  'cb-sigma-verify shared surface'
);
const cbProof = cbProve(
  cbParamsCase.m,
  cbParamsCase.n2,
  cbParamsCase.q,
  cbParamsCase.beta,
  cbParamsCase.gamma,
  cbKey,
  cbCommitment,
  cbWitness,
  cbMasks
);
const cbSdkProof = sdk.ConfidentialBalance.fsProve(
  sdk.ConfidentialBalance.makeParams(cbParamsCase.m, cbParamsCase.n2, cbParamsCase.q, cbParamsCase.beta),
  cbParamsCase.gamma,
  cbKey,
  cbCommitment,
  cbWitness,
  cbMasks
);
assert.deepEqual(
  cbProof,
  cbSdkProof,
  'cb-prove shared surface'
);
assert.equal(balanceProofShape(cbProof!), balanceProofShape(cbSdkProof!), 'cb-proof-shape shared surface');
assert.equal(
  cbVerify(
    cbParamsCase.m,
    cbParamsCase.n2,
    cbParamsCase.q,
    cbParamsCase.beta,
    cbParamsCase.gamma,
    cbKey,
    cbCommitment,
    cbProof!
  ),
  sdk.ConfidentialBalance.fsVerify(
    sdk.ConfidentialBalance.makeParams(cbParamsCase.m, cbParamsCase.n2, cbParamsCase.q, cbParamsCase.beta),
    cbParamsCase.gamma,
    cbKey,
    cbCommitment,
    cbProof!
  ),
  'cb-verify shared surface'
);

console.log('validate-ocaml: confidential balance shared surface passed');

const crParamsCase = { m: 2, n2: 2, q: 17, beta: 6, gamma: 5 };
const crParamsExpected = sdk.ConfidentialBalance.makeParams(
  crParamsCase.m,
  crParamsCase.n2,
  crParamsCase.q,
  crParamsCase.beta
);
const crKey = [
  [1, 0, 0],
  [0, 1, 0],
];
const crAmountOpening = { msg: [5], rand: [1, 2] };
const crBitOpenings = [
  { msg: [1], rand: [1, 0] },
  { msg: [0], rand: [0, 1] },
  { msg: [1], rand: [1, 1] },
];
const crCompOpenings = [
  { msg: [0], rand: [0, 1] },
  { msg: [1], rand: [1, 0] },
  { msg: [0], rand: [0, -1] },
];
const crRounds = sdk.ConfidentialBalance.fsRounds();
const crYAmount = Array.from({ length: crRounds }, () => [0, 1]);
const crYPairs = Array.from({ length: crRounds }, () => [
  [1, 0],
  [0, 0],
  [1, -1],
]);
const crAmountCommit = sdk.Zq.matVecMultMod(
  crKey,
  sdk.Vec.concat(crAmountOpening.msg, crAmountOpening.rand),
  crParamsExpected.q
);
const crBitCommitments = crBitOpenings.map((opening: { msg: number[]; rand: number[] }) =>
  sdk.Zq.matVecMultMod(crKey, sdk.Vec.concat(opening.msg, opening.rand), crParamsExpected.q)
);
const crRangeK = crBitOpenings.length;

assert.deepEqual(
  crAmountCommitment(
    crParamsCase.m,
    crParamsCase.n2,
    crParamsCase.q,
    crParamsCase.beta,
    crKey,
    crAmountCommit,
    crBitCommitments
  ),
  sdk.ConfidentialRange.amountCommitment(crParamsExpected, crKey, crAmountCommit, crBitCommitments),
  'cr-amount-commitment shared surface'
);
const crProof = sdk.ConfidentialRange.fsProve(
  crParamsExpected,
  crParamsCase.gamma,
  crRangeK,
  crKey,
  crAmountCommit,
  crAmountOpening,
  crBitOpenings,
  crCompOpenings,
  crYAmount,
  crYPairs
);
assert.ok(crProof);
assert.ok(
  ['legacy', 'rounds', 'lists'].includes(rangeProofShape(crProof)),
  `unexpected range proof shape: ${rangeProofShape(crProof)}`
);
assert.equal(
  sdk.ConfidentialRange.fsVerify(
    crParamsExpected,
    crParamsCase.gamma,
    crRangeK,
    crKey,
    crAmountCommit,
    crProof!
  ),
  true,
  'cr-verify shared surface'
);
assert.equal(
  crVerify(
    crParamsCase.m,
    crParamsCase.n2,
    crParamsCase.q,
    crParamsCase.beta,
    crParamsCase.gamma,
    crRangeK,
    crKey,
    crAmountCommit,
    crProof!
  ),
  true,
  'cr-verify CLI accepts SDK range proofs'
);
const crBadAmountOpening = { msg: [6], rand: [1, 2] };
const crBadAmountCommit = sdk.Zq.matVecMultMod(
  crKey,
  sdk.Vec.concat(crBadAmountOpening.msg, crBadAmountOpening.rand),
  crParamsExpected.q
);
assert.equal(
  sdk.ConfidentialRange.fsProve(
    crParamsExpected,
    crParamsCase.gamma,
    crRangeK,
    crKey,
    crBadAmountCommit,
    crBadAmountOpening,
    crBitOpenings,
    crCompOpenings,
    crYAmount,
    crYPairs
  ),
  null,
  'cr-prove invalid shared surface'
);

console.log('validate-ocaml: confidential range shared surface passed');

const ctParamsCase = { m: 2, n2: 2, q: 17, beta: 6, gamma: 5 };
logProgress('validate-ocaml: entering confidential transaction shared surface');
const ctParamsExpected = sdk.ConfidentialBalance.makeParams(
  ctParamsCase.m,
  ctParamsCase.n2,
  ctParamsCase.q,
  ctParamsCase.beta
);
const ctCk = [
  [1, 0, 0],
  [0, 1, 0],
];
const ctNk = [
  [0, 1, 0],
  [1, 0, 0],
];
const ctOpIn1 = { msg: [1], rand: [1, 0] };
const ctOpIn2 = { msg: [1], rand: [0, 1] };
const ctOpOut1 = { msg: [1], rand: [1, 1] };
const ctOpOut2 = { msg: [1], rand: [0, 0] };
const ctOut1Bits = [
  { msg: [1], rand: [1, 1] },
];
const ctOut1Comps = [
  { msg: [0], rand: [0, 0] },
];
const ctOut2Bits = [
  { msg: [1], rand: [0, 0] },
];
const ctOut2Comps = [
  { msg: [0], rand: [0, 0] },
];
const ctIn1Bits = [
  { msg: [1], rand: [1, 0] },
];
const ctIn1Comps = [
  { msg: [0], rand: [0, 0] },
];
const ctIn2Bits = [
  { msg: [1], rand: [0, 1] },
];
const ctIn2Comps = [
  { msg: [0], rand: [0, 0] },
];
const ctYIn1 = { msg: [0], rand: [1, 0] };
const ctYIn2 = { msg: [1], rand: [0, 1] };
const ctYIn1Rounds = Array.from({ length: sdk.ConfidentialBalance.fsRounds() }, () => ctYIn1);
const ctYIn2Rounds = Array.from({ length: sdk.ConfidentialBalance.fsRounds() }, () => ctYIn2);
const ctYBalance = Array.from({ length: sdk.ConfidentialBalance.fsRounds() }, () => [0, 1]);
const ctYOut1 = Array.from({ length: crRounds }, () => [0, 1]);
const ctYOut1Pairs = Array.from({ length: crRounds }, () => [[0, 0]]);
const ctYOut2 = Array.from({ length: crRounds }, () => [1, 0]);
const ctYOut2Pairs = Array.from({ length: crRounds }, () => [[0, 0]]);
const ctCommitOfOpening = (opening: { msg: number[]; rand: number[] }) =>
  sdk.Zq.matVecMultMod(ctCk, sdk.Vec.concat(opening.msg, opening.rand), ctParamsExpected.q);
const ctCIn1 = ctCommitOfOpening(ctOpIn1);
const ctCIn2 = ctCommitOfOpening(ctOpIn2);
const ctCOut1 = ctCommitOfOpening(ctOpOut1);
const ctCOut2 = ctCommitOfOpening(ctOpOut2);
const ctNf1 = sdk.ConfidentialTransaction.nullifier(ctParamsExpected, ctNk, ctOpIn1);
const ctNf2 = sdk.ConfidentialTransaction.nullifier(ctParamsExpected, ctNk, ctOpIn2);
const ctLedger = [ctCIn1, ctCIn2];
const ctSpent: number[][] = [];

assert.deepEqual(
  ctNullifier(
    ctParamsCase.m,
    ctParamsCase.n2,
    ctParamsCase.q,
    ctParamsCase.beta,
    ctNk,
    ctOpIn1.msg[0],
    ctOpIn1.rand
  ),
  sdk.ConfidentialTransaction.nullifier(ctParamsExpected, ctNk, ctOpIn1),
  'ct-nullifier shared surface'
);
const ctNullifierProof = sdk.ConfidentialTransaction.nullifierFsProve(
  ctParamsExpected,
  ctParamsCase.gamma,
  ctCk,
  ctNk,
  ctCIn1,
  ctNf1,
  ctOpIn1,
  ctYIn1Rounds
);
assert.ok(ctNullifierProof);
assert.ok(
  ['legacy', 'rounds', 'lists'].includes(nullifierProofShape(ctNullifierProof)),
  `unexpected nullifier proof shape: ${nullifierProofShape(ctNullifierProof)}`
);
const ctListedNullifierProof = listNullifierProof(ctNullifierProof);
const ctExpectedNullifierChallenge = sdk.ConfidentialTransaction.canonicalNullifierChallenge(
  ctParamsExpected,
  ctCk,
  ctNk,
  ctCIn1,
  ctNf1,
  ctListedNullifierProof.aCommits[0],
  ctListedNullifierProof.aNullifiers[0]
);
assert.equal(
  ctNullifierCanonicalChallenge(
    ctParamsCase.m,
    ctParamsCase.n2,
    ctParamsCase.q,
    ctParamsCase.beta,
    ctCk,
    ctNk,
    ctCIn1,
    ctNf1,
    ctListedNullifierProof.aCommits[0],
    ctListedNullifierProof.aNullifiers[0]
  ),
  ctExpectedNullifierChallenge,
  'ct-nullifier-canonical-challenge shared surface'
);
assert.equal(
  sdk.ConfidentialTransaction.nullifierFsVerify(
    ctParamsExpected,
    ctParamsCase.gamma,
    ctCk,
    ctNk,
    ctCIn1,
    ctNf1,
    ctNullifierProof!
  ),
  true,
  'ct-nullifier-verify shared surface'
);
logProgress('validate-ocaml: nullifier proof checks passed');
assert.equal(
  ctNullifierVerify(
    ctParamsCase.m,
    ctParamsCase.n2,
    ctParamsCase.q,
    ctParamsCase.beta,
    ctParamsCase.gamma,
    ctCk,
    ctNk,
    ctCIn1,
    ctNf1,
    ctNullifierProof!
  ),
  true,
  'ct-nullifier-verify CLI accepts SDK proofs'
);
const ctRoot = sdk.ConfidentialTransaction.ledgerRoot(ctParamsExpected, ctLedger);
const ctMemberProof = ctMemberProve(ctParamsExpected, ctLedger, ctCIn2);
assert.deepEqual(
  ctMemberProof,
  sdk.ConfidentialTransaction.membershipProve(ctParamsExpected, ctLedger, ctCIn2),
  'ct-member-prove shared surface'
);
assert.equal(
  ctMemberVerify(ctParamsExpected, ctCIn2, ctMemberProof!),
  sdk.ConfidentialTransaction.membershipVerify(ctParamsExpected, ctCIn2, ctMemberProof!),
  'ct-member-verify shared surface'
);
logProgress('validate-ocaml: membership checks passed');
const merkleVectors = JSON.parse(
  fs.readFileSync(path.join(projectRoot, 'tests/fixtures/confidential-merkle-vectors.json'), 'utf8')
);
const [merkleLeaf0, merkleLeaf1] = merkleVectors.leaves;
const [merkleEmpty0] = merkleVectors.empty;
const [merkleParent01] = merkleVectors.nodes;
const merkleLedger = [merkleLeaf0.commitment, merkleLeaf1.commitment, merkleLeaf0.commitment];
assert.equal(
  ctMerkleLeaf(merkleLeaf0.commitment),
  sdk.ConfidentialMerkle.leaf(merkleLeaf0.commitment),
  'ct-merkle-leaf OCaml/TypeScript parity'
);
assert.equal(ctMerkleLeaf(merkleLeaf0.commitment), merkleLeaf0.digest, 'ct-merkle-leaf vector');
assert.equal(
  ctMerkleEmpty(merkleEmpty0.width),
  sdk.ConfidentialMerkle.empty(merkleEmpty0.width),
  'ct-merkle-empty OCaml/TypeScript parity'
);
assert.equal(
  ctMerkleNode(merkleParent01.left, merkleParent01.right),
  sdk.ConfidentialMerkle.node(merkleParent01.left, merkleParent01.right),
  'ct-merkle-node OCaml/TypeScript parity'
);
assert.equal(
  ctMerkleRoot(merkleLedger),
  sdk.ConfidentialMerkle.root(merkleLedger),
  'ct-merkle-root OCaml/TypeScript parity'
);
const ocamlMerkleProof = ctMerkleMemberProve(merkleLedger, merkleLeaf1.commitment);
assert.deepEqual(
  ocamlMerkleProof,
  sdk.ConfidentialMerkle.membershipProve(merkleLedger, merkleLeaf1.commitment),
  'ct-merkle-member-prove OCaml/TypeScript parity'
);
assert.equal(
  ctMerkleMemberVerify(merkleLedger, merkleLeaf1.commitment),
  true,
  'ct-merkle-member-verify OCaml accepts generated path'
);
const transactionVectors = JSON.parse(
  fs.readFileSync(path.join(projectRoot, 'tests/fixtures/confidential-transaction-vectors.json'), 'utf8')
);
const [transactionContextVector] = transactionVectors.cases;
const [transactionMerkleProofVector] = transactionVectors.merkleProofCases;
const [transactionEnvelopeVector] = transactionVectors.envelopeCases;
const [transactionAcceptedRootWindowVector] = transactionVectors.acceptedRootWindowCases;
const [transactionWalletProofRequestVector] = transactionVectors.walletProofRequestCases;
const transactionContext = transactionContextVector.context;
assert.equal(
  ctTransactionContext(
    transactionContext.protocolVersion,
    transactionContext.networkId,
    transactionContext.assetId,
    transactionContext.ledgerEpoch,
    transactionContext.root,
    transactionContext.publicFee,
    transactionContext.cIn1,
    transactionContext.cIn2,
    transactionContext.cOut1,
    transactionContext.cOut2,
    transactionContext.nf1,
    transactionContext.nf2
  ),
  sdk.ConfidentialTransaction.transactionContextDigest(transactionContext),
  'ct-transaction-context OCaml/TypeScript parity'
);
assert.equal(
  sdk.ConfidentialTransaction.transactionContextDigest(transactionContext),
  transactionContextVector.digest,
  'ct-transaction-context vector'
);
const transactionContextArgs = [
  'ct-transaction-context',
  transactionContext.protocolVersion.toString(),
  transactionContext.networkId,
  transactionContext.assetId.toString(),
  transactionContext.ledgerEpoch.toString(),
  transactionContext.root.digest,
  transactionContext.root.depth.toString(),
  transactionContext.publicFee.toString(),
  JSON.stringify(transactionContext.cIn1),
  JSON.stringify(transactionContext.cIn2),
  JSON.stringify(transactionContext.cOut1),
  JSON.stringify(transactionContext.cOut2),
  JSON.stringify(transactionContext.nf1),
  JSON.stringify(transactionContext.nf2),
];
for (const { name, args } of [
  {
    name: 'negative-zero public fee',
    args: transactionContextArgs.map((arg, index) => (index === 7 ? '-0' : arg)),
  },
  {
    name: 'plus-signed asset id',
    args: transactionContextArgs.map((arg, index) => (index === 3 ? `+${arg}` : arg)),
  },
  {
    name: 'unsafe asset id',
    args: transactionContextArgs.map((arg, index) =>
      index === 3 ? unsafeProtocolInteger : arg
    ),
  },
  {
    name: 'leading-zero input vector element',
    args: transactionContextArgs.map((arg, index) =>
      index === 8 ? nonCanonicalFirstInteger(arg) : arg
    ),
  },
  {
    name: 'unsafe input vector element',
    args: transactionContextArgs.map((arg, index) =>
      index === 8 ? unsafeFirstInteger(arg) : arg
    ),
  },
]) {
  expectOcamlCommandRejected(args, `ct-transaction-context OCaml rejects ${name}`);
}
const ocamlWalletProofRequestDigest = ctWalletProofRequestDigest(
  transactionWalletProofRequestVector.request
);
assert.equal(
  ocamlWalletProofRequestDigest,
  sdk.ConfidentialTransaction.transactionWalletProofRequestDigest(
    transactionWalletProofRequestVector.request
  ),
  'ct-wallet-proof-request-digest OCaml/TypeScript parity'
);
assert.equal(
  ocamlWalletProofRequestDigest,
  transactionWalletProofRequestVector.digest,
  'ct-wallet-proof-request-digest vector'
);
const acceptedRootWindow = transactionAcceptedRootWindowVector.window;
const ocamlAcceptedRootWindowDigest = ctAcceptedRootWindowDigest(acceptedRootWindow);
assert.equal(
  ocamlAcceptedRootWindowDigest,
  sdk.ConfidentialTransaction.transactionAcceptedRootWindowDigest(acceptedRootWindow),
  'ct-accepted-root-window-digest OCaml/TypeScript parity'
);
assert.equal(
  ocamlAcceptedRootWindowDigest,
  transactionAcceptedRootWindowVector.digest,
  'ct-accepted-root-window-digest vector'
);
function ctAcceptedRootWindowDigestArgs(window: any): string[] {
  return [
    window.protocolVersion.toString(),
    window.networkId,
    window.assetId.toString(),
    window.ledgerEpoch.toString(),
    JSON.stringify(window.roots.map((entry: any) => entry.root.digest)),
    JSON.stringify(window.roots.map((entry: any) => entry.root.depth)),
    JSON.stringify(window.roots.map((entry: any) => entry.validFromEpoch)),
    JSON.stringify(window.roots.map((entry: any) => entry.expiresAtEpoch)),
  ];
}
function expectOcamlAcceptedRootWindowRejected(window: any, label: string): void {
  expectOcamlCommandRejected(
    ['ct-accepted-root-window-digest', ...ctAcceptedRootWindowDigestArgs(window)],
    label
  );
}
const reversedRootWindow = acceptedRootWindow.roots.slice().reverse();
const acceptedRootWindowRejectionCases = [
  {
    name: 'empty root window',
    window: { ...acceptedRootWindow, roots: [] },
  },
  {
    name: 'duplicate root window entry',
    window: { ...acceptedRootWindow, roots: [acceptedRootWindow.roots[0], acceptedRootWindow.roots[0]] },
  },
  ...(reversedRootWindow.map((entry: any) => `${entry.root.digest}:${entry.root.depth}`).join('|') ===
    acceptedRootWindow.roots.map((entry: any) => `${entry.root.digest}:${entry.root.depth}`).join('|')
    ? []
    : [{
        name: 'unsorted root window',
        window: { ...acceptedRootWindow, roots: reversedRootWindow },
      }]),
  {
    name: 'future root window entry',
    window: {
      ...acceptedRootWindow,
      roots: acceptedRootWindow.roots.map((entry: any, index: number) =>
        index === 0 ? { ...entry, validFromEpoch: acceptedRootWindow.ledgerEpoch + 1 } : entry
      ),
    },
  },
  {
    name: 'expired root window entry',
    window: {
      ...acceptedRootWindow,
      roots: acceptedRootWindow.roots.map((entry: any, index: number) =>
        index === 0 ? { ...entry, expiresAtEpoch: acceptedRootWindow.ledgerEpoch } : entry
      ),
    },
  },
];
for (const { name, window } of acceptedRootWindowRejectionCases) {
  expectOcamlAcceptedRootWindowRejected(window, `ct-accepted-root-window-digest OCaml rejects ${name}`);
}
const acceptedRootWindowArgs = [
  'ct-accepted-root-window-digest',
  ...ctAcceptedRootWindowDigestArgs(acceptedRootWindow),
];
for (const { name, args } of [
  {
    name: 'negative-zero ledger epoch',
    args: acceptedRootWindowArgs.map((arg, index) => (index === 4 ? '-0' : arg)),
  },
  {
    name: 'leading-zero root depth',
    args: acceptedRootWindowArgs.map((arg, index) =>
      index === 6 ? nonCanonicalFirstInteger(arg) : arg
    ),
  },
  {
    name: 'unsafe expiry epoch',
    args: acceptedRootWindowArgs.map((arg, index) =>
      index === 8 ? unsafeFirstInteger(arg) : arg
    ),
  },
]) {
  expectOcamlCommandRejected(args, `ct-accepted-root-window-digest OCaml rejects ${name}`);
}
function ctWalletProofRequestDigestArgs(request: any): string[] {
  const context = request.context;
  const acceptedRootDigests = request.acceptedRoots.map((root: any) => root.digest);
  const acceptedRootDepths = request.acceptedRoots.map((root: any) => root.depth);
  return [
    context.protocolVersion.toString(),
    context.networkId,
    context.assetId.toString(),
    context.ledgerEpoch.toString(),
    context.root.digest,
    context.root.depth.toString(),
    context.publicFee.toString(),
    JSON.stringify(context.cIn1),
    JSON.stringify(context.cIn2),
    JSON.stringify(context.cOut1),
    JSON.stringify(context.cOut2),
    JSON.stringify(context.nf1),
    JSON.stringify(context.nf2),
    JSON.stringify(acceptedRootDigests),
    JSON.stringify(acceptedRootDepths),
    JSON.stringify(request.spentNullifiers),
  ];
}
function expectOcamlWalletProofRequestRejected(request: any, label: string): void {
  expectOcamlCommandRejected(
    ['ct-wallet-proof-request-digest', ...ctWalletProofRequestDigestArgs(request)],
    label
  );
}
const walletProofRequest = transactionWalletProofRequestVector.request;
const reversedAcceptedRoots = walletProofRequest.acceptedRoots.slice().reverse();
const reversedSpentNullifiers = walletProofRequest.spentNullifiers.slice().reverse();
const walletProofRequestRejectionCases = [
  {
    name: 'empty accepted root window',
    request: { ...walletProofRequest, acceptedRoots: [] },
  },
  {
    name: 'context root missing from accepted window',
    request: {
      ...walletProofRequest,
      acceptedRoots: walletProofRequest.acceptedRoots.filter(
        (root: any) =>
          root.digest !== walletProofRequest.context.root.digest ||
          root.depth !== walletProofRequest.context.root.depth
      ),
    },
  },
  {
    name: 'context root depth missing from accepted window',
    request: {
      ...walletProofRequest,
      acceptedRoots: walletProofRequest.acceptedRoots
        .map((root: any) =>
          root.digest === walletProofRequest.context.root.digest &&
          root.depth === walletProofRequest.context.root.depth
            ? { ...root, depth: root.depth + 1 }
            : root
        )
        .sort((left: any, right: any) =>
          `${left.digest}:${left.depth}`.localeCompare(`${right.digest}:${right.depth}`)
        ),
    },
  },
  {
    name: 'duplicate accepted roots',
    request: {
      ...walletProofRequest,
      acceptedRoots: [walletProofRequest.context.root, walletProofRequest.context.root],
    },
  },
  ...(reversedAcceptedRoots.map((root: any) => `${root.digest}:${root.depth}`).join('|') ===
    walletProofRequest.acceptedRoots.map((root: any) => `${root.digest}:${root.depth}`).join('|')
    ? []
    : [{
        name: 'unsorted accepted roots',
        request: { ...walletProofRequest, acceptedRoots: reversedAcceptedRoots },
      }]),
  ...(reversedSpentNullifiers.length < 2
    ? []
    : [{
        name: 'unsorted spent nullifiers',
        request: { ...walletProofRequest, spentNullifiers: reversedSpentNullifiers },
      }]),
  {
    name: 'duplicate spent nullifiers',
    request: {
      ...walletProofRequest,
      spentNullifiers: [
        walletProofRequest.spentNullifiers[0],
        walletProofRequest.spentNullifiers[0],
      ],
    },
  },
  {
    name: 'requested nullifier already spent',
    request: { ...walletProofRequest, spentNullifiers: [walletProofRequest.context.nf1] },
  },
  {
    name: 'duplicate requested nullifiers',
    request: {
      ...walletProofRequest,
      context: { ...walletProofRequest.context, nf2: walletProofRequest.context.nf1 },
    },
  },
];
for (const { name, request } of walletProofRequestRejectionCases) {
  expectOcamlWalletProofRequestRejected(request, `ct-wallet-proof-request-digest OCaml rejects ${name}`);
}
const walletProofRequestArgs = [
  'ct-wallet-proof-request-digest',
  ...ctWalletProofRequestDigestArgs(walletProofRequest),
];
for (const { name, args } of [
  {
    name: 'negative-zero public fee',
    args: walletProofRequestArgs.map((arg, index) => (index === 7 ? '-0' : arg)),
  },
  {
    name: 'leading-zero protocol version',
    args: walletProofRequestArgs.map((arg, index) =>
      index === 1 ? nonCanonicalIntegerText(arg) : arg
    ),
  },
  {
    name: 'unsafe protocol version',
    args: walletProofRequestArgs.map((arg, index) =>
      index === 1 ? unsafeProtocolInteger : arg
    ),
  },
  {
    name: 'non-canonical spent-nullifier integer',
    args: walletProofRequestArgs.map((arg, index) =>
      index === 16 ? nonCanonicalFirstInteger(arg) : arg
    ),
  },
  {
    name: 'unsafe spent-nullifier integer',
    args: walletProofRequestArgs.map((arg, index) =>
      index === 16 ? unsafeFirstInteger(arg) : arg
    ),
  },
]) {
  expectOcamlCommandRejected(args, `ct-wallet-proof-request-digest OCaml rejects ${name}`);
}
logProgress('validate-ocaml: cryptographic Merkle shared surface passed');
assert.equal(typeof sdk.ConfidentialTransaction.semanticStepValid, 'function', 'Merkle semantic step export');
assert.equal(typeof sdk.ConfidentialTransaction.semanticStepValidMerkle, 'function', 'Merkle semantic step explicit export');
assert.equal(typeof sdk.ConfidentialTransaction.ledgerStepValid, 'function', 'Merkle ledger-step export');
assert.equal(typeof sdk.ConfidentialTransaction.ledgerStepValidScaffold, 'function', 'explicit scaffold ledger-step export');
assert.equal(typeof sdk.ConfidentialTransaction.semanticStepValidScaffold, 'function', 'explicit scaffold semantic-step export');
const ocamlScaffoldDefault = parseCliResult<{ error?: string }>(runCli(['ct-verify-scaffold']));
assert.match(
  ocamlScaffoldDefault.error ?? '',
  /ISABELLA_ENABLE_SCAFFOLD_COMPAT/,
  'ct-verify-scaffold OCaml default launch mode requires explicit scaffold opt-in'
);

console.log('validate-ocaml: confidential nullifier and membership shared surfaces passed');

const ctProof = sdk.ConfidentialTransaction.fsProve(
  ctParamsExpected,
  ctParamsCase.gamma,
  ctOut1Bits.length,
  ctCk,
  ctNk,
  ctLedger,
  ctSpent,
  ctCIn1,
  ctCIn2,
  ctCOut1,
  ctCOut2,
  ctNf1,
  ctNf2,
  ctOpIn1,
  ctOpIn2,
  ctOpOut1,
  ctOpOut2,
  ctOut1Bits,
  ctOut1Comps,
  ctOut2Bits,
  ctOut2Comps,
  ctYIn1Rounds,
  ctYIn2Rounds,
  ctYBalance,
  ctYOut1,
  ctYOut1Pairs,
  ctYOut2,
  ctYOut2Pairs
);
assert.ok(ctProof);
logProgress('validate-ocaml: transaction proof constructed');
assert.ok(
  ['legacy', 'rounds', 'lists'].includes(rangeProofShape(ctProof.out1Range)),
  `unexpected out1 range proof shape: ${rangeProofShape(ctProof.out1Range)}`
);
assert.ok(
  ['legacy', 'rounds', 'lists'].includes(rangeProofShape(ctProof.out2Range)),
  `unexpected out2 range proof shape: ${rangeProofShape(ctProof.out2Range)}`
);
assert.equal(
  sdk.ConfidentialTransaction.fsVerify(
    ctParamsExpected,
    ctParamsCase.gamma,
    ctOut1Bits.length,
    ctCk,
    ctNk,
    ctRoot,
    ctSpent,
    ctCIn1,
    ctCIn2,
    ctCOut1,
    ctCOut2,
    ctNf1,
    ctNf2,
    ctProof!
  ),
  true,
  'transaction scaffold shared surface'
);
assert.equal(
  ctVerifyScaffold(
    ctParamsCase.m,
    ctParamsCase.n2,
    ctParamsCase.q,
    ctParamsCase.beta,
    ctParamsCase.gamma,
    ctOut1Bits.length,
    ctCk,
    ctNk,
    ctLedger,
    ctSpent,
    ctCIn1,
    ctCIn2,
    ctCOut1,
    ctCOut2,
    ctNf1,
    ctNf2,
    ctProof!
  ),
  true,
  'ct-verify-scaffold OCaml CLI accepts SDK proofs'
);
logProgress('validate-ocaml: transaction verification passed');

const ctMerkleLedgerRoot = sdk.ConfidentialTransaction.merkleLedgerRoot(ctLedger);
const ctMerkleProof = sdk.ConfidentialTransaction.fsProveMerkle(
  ctParamsExpected,
  ctParamsCase.gamma,
  ctOut1Bits.length,
  ctCk,
  ctNk,
  ctLedger,
  ctSpent,
  ctCIn1,
  ctCIn2,
  ctCOut1,
  ctCOut2,
  ctNf1,
  ctNf2,
  ctOpIn1,
  ctOpIn2,
  ctOpOut1,
  ctOpOut2,
  ctOut1Bits,
  ctOut1Comps,
  ctOut2Bits,
  ctOut2Comps,
  ctYIn1Rounds,
  ctYIn2Rounds,
  ctYBalance,
  ctYOut1,
  ctYOut1Pairs,
  ctYOut2,
  ctYOut2Pairs
);
assert.ok(ctMerkleProof);
const ctFee = 1;
const ctFeeOpOut2 = { msg: [0], rand: [0, 0] };
const ctFeeOut2Bits = [
  { msg: [0], rand: [0, 0] },
];
const ctFeeOut2Comps = [
  { msg: [1], rand: [0, 0] },
];
const ctFeeCOut2 = ctCommitOfOpening(ctFeeOpOut2);
const ctFeeMerkleProof = sdk.ConfidentialTransaction.fsProveMerkleWithFee(
  ctParamsExpected,
  ctParamsCase.gamma,
  ctOut1Bits.length,
  ctCk,
  ctNk,
  ctLedger,
  ctSpent,
  ctFee,
  ctCIn1,
  ctCIn2,
  ctCOut1,
  ctFeeCOut2,
  ctNf1,
  ctNf2,
  ctOpIn1,
  ctOpIn2,
  ctOpOut1,
  ctFeeOpOut2,
  ctOut1Bits,
  ctOut1Comps,
  ctFeeOut2Bits,
  ctFeeOut2Comps,
  ctYIn1Rounds,
  ctYIn2Rounds,
  ctYBalance,
  ctYOut1,
  ctYOut1Pairs,
  ctYOut2,
  ctYOut2Pairs
);
assert.ok(ctFeeMerkleProof);
const ctOut1BitValues = ctOut1Bits.map((opening: { msg: number[] }) => opening.msg[0]);
const ctOut1BitRands = ctOut1Bits.map((opening: { rand: number[] }) => opening.rand);
const ctOut1CompValues = ctOut1Comps.map((opening: { msg: number[] }) => opening.msg[0]);
const ctOut1CompRands = ctOut1Comps.map((opening: { rand: number[] }) => opening.rand);
const ctOut2BitValues = ctOut2Bits.map((opening: { msg: number[] }) => opening.msg[0]);
const ctOut2BitRands = ctOut2Bits.map((opening: { rand: number[] }) => opening.rand);
const ctOut2CompValues = ctOut2Comps.map((opening: { msg: number[] }) => opening.msg[0]);
const ctOut2CompRands = ctOut2Comps.map((opening: { rand: number[] }) => opening.rand);
const ctYIn1Msgs = ctYIn1Rounds.map((opening: { msg: number[] }) => opening.msg[0]);
const ctYIn1Rands = ctYIn1Rounds.map((opening: { rand: number[] }) => opening.rand);
const ctYIn2Msgs = ctYIn2Rounds.map((opening: { msg: number[] }) => opening.msg[0]);
const ctYIn2Rands = ctYIn2Rounds.map((opening: { rand: number[] }) => opening.rand);
assert.deepEqual(
  ctProveMerkle(
    ctParamsCase.m,
    ctParamsCase.n2,
    ctParamsCase.q,
    ctParamsCase.beta,
    ctParamsCase.gamma,
    ctOut1Bits.length,
    ctCk,
    ctNk,
    ctLedger,
    ctSpent,
    ctCIn1,
    ctCIn2,
    ctCOut1,
    ctCOut2,
    ctNf1,
    ctNf2,
    ctOpIn1.msg[0],
    ctOpIn1.rand,
    ctOpIn2.msg[0],
    ctOpIn2.rand,
    ctOpOut1.msg[0],
    ctOpOut1.rand,
    ctOpOut2.msg[0],
    ctOpOut2.rand,
    ctOut1BitValues,
    ctOut1BitRands,
    ctOut1CompValues,
    ctOut1CompRands,
    ctOut2BitValues,
    ctOut2BitRands,
    ctOut2CompValues,
    ctOut2CompRands,
    ctYIn1Msgs,
    ctYIn1Rands,
    ctYIn2Msgs,
    ctYIn2Rands,
    ctYBalance,
    ctYOut1,
    ctYOut1Pairs,
    ctYOut2,
    ctYOut2Pairs
  ),
  ctMerkleProof,
  'ct-prove-merkle OCaml/TypeScript parity'
);
assert.equal(
  sdk.ConfidentialTransaction.fsVerifyMerkle(
    ctParamsExpected,
    ctParamsCase.gamma,
    ctOut1Bits.length,
    ctCk,
    ctNk,
    ctMerkleLedgerRoot,
    ctSpent,
    ctCIn1,
    ctCIn2,
    ctCOut1,
    ctCOut2,
    ctNf1,
    ctNf2,
    ctMerkleProof!
  ),
  true,
  'ct-verify-merkle SDK accepts generated proof'
);
assert.equal(
  ctVerifyMerkle(
    ctParamsCase.m,
    ctParamsCase.n2,
    ctParamsCase.q,
    ctParamsCase.beta,
    ctParamsCase.gamma,
    ctOut1Bits.length,
    ctCk,
    ctNk,
    ctLedger,
    ctSpent,
    ctCIn1,
    ctCIn2,
    ctCOut1,
    ctCOut2,
    ctNf1,
    ctNf2,
    ctMerkleProof!
  ),
  true,
  'ct-verify-merkle OCaml/TypeScript parity'
);
const merkleVerifyArgs = [
  'ct-verify-merkle',
  ...ctVerifyMerkleArgs(
    ctParamsCase.m,
    ctParamsCase.n2,
    ctParamsCase.q,
    ctParamsCase.beta,
    ctParamsCase.gamma,
    ctOut1Bits.length,
    ctCk,
    ctNk,
    ctLedger,
    ctSpent,
    ctCIn1,
    ctCIn2,
    ctCOut1,
    ctCOut2,
    ctNf1,
    ctNf2,
    ctMerkleProof!
  ),
];
for (const { name, args } of [
  {
    name: 'non-canonical parameter',
    args: merkleVerifyArgs.map((arg, index) =>
      index === 1 ? nonCanonicalIntegerText(arg) : arg
    ),
  },
  {
    name: 'unsafe parameter',
    args: merkleVerifyArgs.map((arg, index) =>
      index === 1 ? unsafeProtocolInteger : arg
    ),
  },
  {
    name: 'plus-signed gamma',
    args: merkleVerifyArgs.map((arg, index) => (index === 5 ? `+${arg}` : arg)),
  },
  {
    name: 'non-canonical key matrix integer',
    args: merkleVerifyArgs.map((arg, index) =>
      index === 7 ? nonCanonicalFirstInteger(arg) : arg
    ),
  },
  {
    name: 'unsafe key matrix integer',
    args: merkleVerifyArgs.map((arg, index) =>
      index === 7 ? unsafeFirstInteger(arg) : arg
    ),
  },
  {
    name: 'non-canonical public vector integer',
    args: merkleVerifyArgs.map((arg, index) =>
      index === 11 ? nonCanonicalFirstInteger(arg) : arg
    ),
  },
  {
    name: 'unsafe public vector integer',
    args: merkleVerifyArgs.map((arg, index) =>
      index === 11 ? unsafeFirstInteger(arg) : arg
    ),
  },
]) {
  expectOcamlCommandRejected(args, `ct-verify-merkle OCaml rejects ${name}`);
}
const ocamlMerkleProofDigest = ctMerkleProofDigest(ctMerkleProof!);
assert.equal(
  ocamlMerkleProofDigest,
  sdk.ConfidentialTransaction.transactionMerkleProofDigest(ctMerkleProof!),
  'ct-merkle-proof-digest OCaml/TypeScript parity'
);
assert.equal(
  ocamlMerkleProofDigest,
  transactionMerkleProofVector.digest,
  'ct-merkle-proof-digest vector'
);
const merkleProofDigestArgs = ['ct-merkle-proof-digest', ...ctMerkleProofDigestArgs(ctMerkleProof!)];
for (const { name, args } of [
  {
    name: 'non-canonical membership index',
    args: merkleProofDigestArgs.map((arg, index) =>
      index === 1 ? nonCanonicalIntegerText(arg) : arg
    ),
  },
  {
    name: 'unsafe membership index',
    args: merkleProofDigestArgs.map((arg, index) =>
      index === 1 ? unsafeProtocolInteger : arg
    ),
  },
  {
    name: 'non-canonical directions vector',
    args: merkleProofDigestArgs.map((arg, index) =>
      index === 4 ? nonCanonicalFirstInteger(arg) : arg
    ),
  },
  {
    name: 'unsafe directions vector',
    args: merkleProofDigestArgs.map((arg, index) =>
      index === 4 ? unsafeFirstInteger(arg) : arg
    ),
  },
  {
    name: 'non-canonical proof matrix integer',
    args: merkleProofDigestArgs.map((arg, index) =>
      index === 9 ? nonCanonicalFirstInteger(arg) : arg
    ),
  },
  {
    name: 'unsafe proof matrix integer',
    args: merkleProofDigestArgs.map((arg, index) =>
      index === 9 ? unsafeFirstInteger(arg) : arg
    ),
  },
]) {
  expectOcamlCommandRejected(args, `ct-merkle-proof-digest OCaml rejects ${name}`);
}
const ocamlVectorEnvelopeDigest = ctMerkleEnvelopeDigest(
  transactionEnvelopeVector.contextDigest,
  transactionEnvelopeVector.context,
  ctMerkleProof!
);
assert.equal(
  ocamlVectorEnvelopeDigest,
  sdk.ConfidentialTransaction.transactionEnvelopeDigest({
    context: transactionEnvelopeVector.context,
    contextDigest: transactionEnvelopeVector.contextDigest,
    proof: ctMerkleProof!,
  }),
  'ct-merkle-envelope-digest OCaml/TypeScript parity'
);
assert.equal(
  ocamlVectorEnvelopeDigest,
  transactionEnvelopeVector.digest,
  'ct-merkle-envelope-digest vector'
);
const merkleEnvelopeDigestArgs = [
  'ct-merkle-envelope-digest',
  transactionEnvelopeVector.contextDigest,
  transactionEnvelopeVector.context.protocolVersion.toString(),
  transactionEnvelopeVector.context.networkId,
  transactionEnvelopeVector.context.assetId.toString(),
  transactionEnvelopeVector.context.ledgerEpoch.toString(),
  transactionEnvelopeVector.context.root.digest,
  transactionEnvelopeVector.context.root.depth.toString(),
  transactionEnvelopeVector.context.publicFee.toString(),
  JSON.stringify(transactionEnvelopeVector.context.cIn1),
  JSON.stringify(transactionEnvelopeVector.context.cIn2),
  JSON.stringify(transactionEnvelopeVector.context.cOut1),
  JSON.stringify(transactionEnvelopeVector.context.cOut2),
  JSON.stringify(transactionEnvelopeVector.context.nf1),
  JSON.stringify(transactionEnvelopeVector.context.nf2),
  ...ctMerkleProofDigestArgs(ctMerkleProof!),
];
for (const { name, args } of [
  {
    name: 'plus-signed protocol version',
    args: merkleEnvelopeDigestArgs.map((arg, index) => (index === 2 ? `+${arg}` : arg)),
  },
  {
    name: 'negative-zero public fee',
    args: merkleEnvelopeDigestArgs.map((arg, index) => (index === 8 ? '-0' : arg)),
  },
  {
    name: 'unsafe public fee',
    args: merkleEnvelopeDigestArgs.map((arg, index) =>
      index === 8 ? unsafeProtocolInteger : arg
    ),
  },
  {
    name: 'non-canonical context vector integer',
    args: merkleEnvelopeDigestArgs.map((arg, index) =>
      index === 9 ? nonCanonicalFirstInteger(arg) : arg
    ),
  },
  {
    name: 'unsafe context vector integer',
    args: merkleEnvelopeDigestArgs.map((arg, index) =>
      index === 9 ? unsafeFirstInteger(arg) : arg
    ),
  },
]) {
  expectOcamlCommandRejected(args, `ct-merkle-envelope-digest OCaml rejects ${name}`);
}
const ocamlEnvelopeContext = {
  protocolVersion: 1,
  networkId: 'isabella-ocaml-conformance',
  assetId: 7,
  ledgerEpoch: 42,
  root: {
    digest: ctMerkleLedgerRoot,
    depth: ctMerkleProof!.in1Member.siblings.length,
  },
  publicFee: 0,
  cIn1: ctCIn1,
  cIn2: ctCIn2,
  cOut1: ctCOut1,
  cOut2: ctCOut2,
  nf1: ctNf1,
  nf2: ctNf2,
};
const ocamlEnvelopePolicy = {
  protocolVersion: ocamlEnvelopeContext.protocolVersion,
  networkId: ocamlEnvelopeContext.networkId,
  assetId: ocamlEnvelopeContext.assetId,
  ledgerEpoch: ocamlEnvelopeContext.ledgerEpoch,
  root: ocamlEnvelopeContext.root,
  publicFee: 0,
};
const ocamlEnvelopeContextDigest = ctTransactionContext(
  ocamlEnvelopeContext.protocolVersion,
  ocamlEnvelopeContext.networkId,
  ocamlEnvelopeContext.assetId,
  ocamlEnvelopeContext.ledgerEpoch,
  ocamlEnvelopeContext.root,
  ocamlEnvelopeContext.publicFee,
  ocamlEnvelopeContext.cIn1,
  ocamlEnvelopeContext.cIn2,
  ocamlEnvelopeContext.cOut1,
  ocamlEnvelopeContext.cOut2,
  ocamlEnvelopeContext.nf1,
  ocamlEnvelopeContext.nf2
);
assert.equal(
  ocamlEnvelopeContextDigest,
  sdk.ConfidentialTransaction.transactionContextDigest(ocamlEnvelopeContext),
  'ct-merkle-envelope context digest OCaml/TypeScript parity'
);
const ocamlEnvelope = {
  context: ocamlEnvelopeContext,
  contextDigest: ocamlEnvelopeContextDigest,
  proof: ctMerkleProof!,
};
assert.equal(
  ctVerifyMerkleEnvelope(
    ctParamsCase.m,
    ctParamsCase.n2,
    ctParamsCase.q,
    ctParamsCase.beta,
    ctParamsCase.gamma,
    ctOut1Bits.length,
    ctCk,
    ctNk,
    ctLedger,
    ctSpent,
    ocamlEnvelopePolicy,
    ocamlEnvelopeContextDigest,
    ocamlEnvelopeContext,
    ctMerkleProof!
  ),
  true,
  'ct-verify-merkle-envelope OCaml accepts native context digest and Merkle proof'
);
const merkleEnvelopeVerifyArgs = [
  'ct-verify-merkle-envelope',
  ...ctVerifyMerkleEnvelopeArgs(
    ctParamsCase.m,
    ctParamsCase.n2,
    ctParamsCase.q,
    ctParamsCase.beta,
    ctParamsCase.gamma,
    ctOut1Bits.length,
    ctCk,
    ctNk,
    ctLedger,
    ctSpent,
    ocamlEnvelopePolicy,
    ocamlEnvelopeContextDigest,
    ocamlEnvelopeContext,
    ctMerkleProof!
  ),
];
for (const { name, args } of [
  {
    name: 'non-canonical expected public fee',
    args: merkleEnvelopeVerifyArgs.map((arg, index) => (index === 17 ? '-0' : arg)),
  },
  {
    name: 'unsafe expected public fee',
    args: merkleEnvelopeVerifyArgs.map((arg, index) =>
      index === 17 ? unsafeProtocolInteger : arg
    ),
  },
  {
    name: 'plus-signed context protocol version',
    args: merkleEnvelopeVerifyArgs.map((arg, index) => (index === 19 ? `+${arg}` : arg)),
  },
  {
    name: 'non-canonical context vector integer',
    args: merkleEnvelopeVerifyArgs.map((arg, index) =>
      index === 26 ? nonCanonicalFirstInteger(arg) : arg
    ),
  },
  {
    name: 'unsafe context vector integer',
    args: merkleEnvelopeVerifyArgs.map((arg, index) =>
      index === 26 ? unsafeFirstInteger(arg) : arg
    ),
  },
]) {
  expectOcamlCommandRejected(args, `ct-verify-merkle-envelope OCaml rejects ${name}`);
}
assert.equal(
  sdk.ConfidentialTransaction.fsVerifyMerkleEnvelope(
    ctParamsExpected,
    ctParamsCase.gamma,
    ctOut1Bits.length,
    ctCk,
    ctNk,
    ctSpent,
    ocamlEnvelope,
    ocamlEnvelopePolicy
  ),
  true,
  'ct-merkle-envelope accepts OCaml context digest and Merkle proof'
);
assert.equal(
  sdk.ConfidentialTransaction.fsVerifyMerkleEnvelope(
    ctParamsExpected,
    ctParamsCase.gamma,
    ctOut1Bits.length,
    ctCk,
    ctNk,
    ctSpent,
    { ...ocamlEnvelope, contextDigest: ocamlEnvelopeContextDigest.replace(/^./, '0') },
    ocamlEnvelopePolicy
  ),
  false,
  'ct-merkle-envelope rejects stale OCaml context digest'
);
assert.equal(
  ctVerifyMerkleEnvelope(
    ctParamsCase.m,
    ctParamsCase.n2,
    ctParamsCase.q,
    ctParamsCase.beta,
    ctParamsCase.gamma,
    ctOut1Bits.length,
    ctCk,
    ctNk,
    ctLedger,
    ctSpent,
    ocamlEnvelopePolicy,
    ocamlEnvelopeContextDigest.replace(/^./, '0'),
    ocamlEnvelopeContext,
    ctMerkleProof!
  ),
  false,
  'ct-verify-merkle-envelope OCaml rejects stale context digest'
);
assert.equal(
  sdk.ConfidentialTransaction.fsVerifyMerkleEnvelope(
    ctParamsExpected,
    ctParamsCase.gamma,
    ctOut1Bits.length,
    ctCk,
    ctNk,
    ctSpent,
    ocamlEnvelope,
    { ...ocamlEnvelopePolicy, assetId: ocamlEnvelopePolicy.assetId + 1 }
  ),
  false,
  'ct-merkle-envelope rejects wrong verifier policy'
);
assert.equal(
  ctVerifyMerkleEnvelope(
    ctParamsCase.m,
    ctParamsCase.n2,
    ctParamsCase.q,
    ctParamsCase.beta,
    ctParamsCase.gamma,
    ctOut1Bits.length,
    ctCk,
    ctNk,
    ctLedger,
    ctSpent,
    { ...ocamlEnvelopePolicy, assetId: ocamlEnvelopePolicy.assetId + 1 },
    ocamlEnvelopeContextDigest,
    ocamlEnvelopeContext,
    ctMerkleProof!
  ),
  false,
  'ct-verify-merkle-envelope OCaml rejects wrong verifier policy'
);
const ocamlFeeEnvelopeContext = {
  ...ocamlEnvelopeContext,
  publicFee: ctFee,
  cOut2: ctFeeCOut2,
};
const ocamlFeeEnvelopeContextDigest = ctTransactionContext(
  ocamlFeeEnvelopeContext.protocolVersion,
  ocamlFeeEnvelopeContext.networkId,
  ocamlFeeEnvelopeContext.assetId,
  ocamlFeeEnvelopeContext.ledgerEpoch,
  ocamlFeeEnvelopeContext.root,
  ocamlFeeEnvelopeContext.publicFee,
  ocamlFeeEnvelopeContext.cIn1,
  ocamlFeeEnvelopeContext.cIn2,
  ocamlFeeEnvelopeContext.cOut1,
  ocamlFeeEnvelopeContext.cOut2,
  ocamlFeeEnvelopeContext.nf1,
  ocamlFeeEnvelopeContext.nf2
);
assert.equal(
  ocamlFeeEnvelopeContextDigest,
  sdk.ConfidentialTransaction.transactionContextDigest(ocamlFeeEnvelopeContext),
  'ct-merkle-envelope fee context digest OCaml/TypeScript parity'
);
assert.equal(
  sdk.ConfidentialTransaction.fsVerifyMerkleEnvelope(
    ctParamsExpected,
    ctParamsCase.gamma,
    ctOut1Bits.length,
    ctCk,
    ctNk,
    ctSpent,
    {
      context: ocamlFeeEnvelopeContext,
      contextDigest: ocamlFeeEnvelopeContextDigest,
      proof: ctFeeMerkleProof!,
    },
    { ...ocamlEnvelopePolicy, publicFee: ctFee }
  ),
  true,
  'ct-merkle-envelope accepts fee-aware public-fee proof'
);
assert.equal(
  ctVerifyMerkleEnvelope(
    ctParamsCase.m,
    ctParamsCase.n2,
    ctParamsCase.q,
    ctParamsCase.beta,
    ctParamsCase.gamma,
    ctOut1Bits.length,
    ctCk,
    ctNk,
    ctLedger,
    ctSpent,
    { ...ocamlEnvelopePolicy, publicFee: ctFee },
    ocamlFeeEnvelopeContextDigest,
    ocamlFeeEnvelopeContext,
    ctFeeMerkleProof!
  ),
  true,
  'ct-verify-merkle-envelope OCaml accepts fee-aware public-fee proof'
);
assert.equal(
  ctVerifyMerkleEnvelope(
    ctParamsCase.m,
    ctParamsCase.n2,
    ctParamsCase.q,
    ctParamsCase.beta,
    ctParamsCase.gamma,
    ctOut1Bits.length,
    ctCk,
    ctNk,
    ctLedger,
    ctSpent,
    ocamlEnvelopePolicy,
    ocamlFeeEnvelopeContextDigest,
    ocamlFeeEnvelopeContext,
    ctFeeMerkleProof!
  ),
  false,
  'ct-verify-merkle-envelope OCaml rejects mismatched fee policy'
);
assert.equal(
  ctVerifyMerkleEnvelope(
    ctParamsCase.m,
    ctParamsCase.n2,
    ctParamsCase.q,
    ctParamsCase.beta,
    ctParamsCase.gamma,
    ctOut1Bits.length,
    ctCk,
    ctNk,
    ctLedger,
    ctSpent,
    { ...ocamlEnvelopePolicy, root: { ...ocamlEnvelopePolicy.root, depth: ocamlEnvelopePolicy.root.depth + 1 } },
    ocamlEnvelopeContextDigest,
    ocamlEnvelopeContext,
    ctMerkleProof!
  ),
  false,
  'ct-verify-merkle-envelope OCaml rejects wrong verifier root depth'
);
const ocamlWrongDepthContext = {
  ...ocamlEnvelopeContext,
  root: { ...ocamlEnvelopeContext.root, depth: ocamlEnvelopeContext.root.depth + 1 },
};
const ocamlWrongDepthDigest = ctTransactionContext(
  ocamlWrongDepthContext.protocolVersion,
  ocamlWrongDepthContext.networkId,
  ocamlWrongDepthContext.assetId,
  ocamlWrongDepthContext.ledgerEpoch,
  ocamlWrongDepthContext.root,
  ocamlWrongDepthContext.publicFee,
  ocamlWrongDepthContext.cIn1,
  ocamlWrongDepthContext.cIn2,
  ocamlWrongDepthContext.cOut1,
  ocamlWrongDepthContext.cOut2,
  ocamlWrongDepthContext.nf1,
  ocamlWrongDepthContext.nf2
);
assert.equal(
  ctVerifyMerkleEnvelope(
    ctParamsCase.m,
    ctParamsCase.n2,
    ctParamsCase.q,
    ctParamsCase.beta,
    ctParamsCase.gamma,
    ctOut1Bits.length,
    ctCk,
    ctNk,
    ctLedger,
    ctSpent,
    { ...ocamlEnvelopePolicy, root: ocamlWrongDepthContext.root },
    ocamlWrongDepthDigest,
    ocamlWrongDepthContext,
    ctMerkleProof!
  ),
  false,
  'ct-verify-merkle-envelope OCaml rejects context root depth not matched by the Merkle proof'
);
const ocamlWrongRootContext = {
  ...ocamlEnvelopeContext,
  root: {
    ...ocamlEnvelopeContext.root,
    digest: ocamlEnvelopeContext.root.digest.replace(
      /^./,
      ocamlEnvelopeContext.root.digest[0] === '0' ? '1' : '0'
    ),
  },
};
const ocamlWrongRootDigest = ctTransactionContext(
  ocamlWrongRootContext.protocolVersion,
  ocamlWrongRootContext.networkId,
  ocamlWrongRootContext.assetId,
  ocamlWrongRootContext.ledgerEpoch,
  ocamlWrongRootContext.root,
  ocamlWrongRootContext.publicFee,
  ocamlWrongRootContext.cIn1,
  ocamlWrongRootContext.cIn2,
  ocamlWrongRootContext.cOut1,
  ocamlWrongRootContext.cOut2,
  ocamlWrongRootContext.nf1,
  ocamlWrongRootContext.nf2
);
assert.equal(
  ctVerifyMerkleEnvelope(
    ctParamsCase.m,
    ctParamsCase.n2,
    ctParamsCase.q,
    ctParamsCase.beta,
    ctParamsCase.gamma,
    ctOut1Bits.length,
    ctCk,
    ctNk,
    ctLedger,
    ctSpent,
    { ...ocamlEnvelopePolicy, root: ocamlWrongRootContext.root },
    ocamlWrongRootDigest,
    ocamlWrongRootContext,
    ctMerkleProof!
  ),
  false,
  'ct-verify-merkle-envelope OCaml rejects context roots not matched by the Merkle proof'
);
for (const mutation of merkleTransactionProofMutations(
  ctMerkleProof!,
  ctSpent,
  ocamlEnvelopeContext.root.digest,
  ctNf1
)) {
  const mutatedContext =
    mutation.root === ocamlEnvelopeContext.root.digest
      ? ocamlEnvelopeContext
      : {
          ...ocamlEnvelopeContext,
          root: { ...ocamlEnvelopeContext.root, digest: mutation.root },
        };
  const mutatedPolicy =
    mutation.root === ocamlEnvelopePolicy.root.digest
      ? ocamlEnvelopePolicy
      : {
          ...ocamlEnvelopePolicy,
          root: { ...ocamlEnvelopePolicy.root, digest: mutation.root },
        };
  const mutatedContextDigest =
    mutatedContext === ocamlEnvelopeContext
      ? ocamlEnvelopeContextDigest
      : ctTransactionContext(
          mutatedContext.protocolVersion,
          mutatedContext.networkId,
          mutatedContext.assetId,
          mutatedContext.ledgerEpoch,
          mutatedContext.root,
          mutatedContext.publicFee,
          mutatedContext.cIn1,
          mutatedContext.cIn2,
          mutatedContext.cOut1,
          mutatedContext.cOut2,
          mutatedContext.nf1,
          mutatedContext.nf2
        );
  assert.equal(
    sdk.ConfidentialTransaction.fsVerifyMerkleEnvelope(
      ctParamsExpected,
      ctParamsCase.gamma,
      ctOut1Bits.length,
      ctCk,
      ctNk,
      mutation.spent,
      {
        context: mutatedContext,
        contextDigest: mutatedContextDigest,
        proof: mutation.proof,
      },
      mutatedPolicy
    ),
    false,
    `ct-merkle-envelope rejects mutated proof case ${mutation.name}`
  );
  assert.equal(
    ctVerifyMerkleEnvelope(
      ctParamsCase.m,
      ctParamsCase.n2,
      ctParamsCase.q,
      ctParamsCase.beta,
      ctParamsCase.gamma,
      ctOut1Bits.length,
      ctCk,
      ctNk,
      ctLedger,
      mutation.spent,
      mutatedPolicy,
      mutatedContextDigest,
      mutatedContext,
      mutation.proof
    ),
    false,
    `ct-verify-merkle-envelope OCaml rejects mutated proof case ${mutation.name}`
  );
}
logProgress('validate-ocaml: Merkle transaction CLI parity passed');

console.log('validate-ocaml: confidential transaction proof verification passed');

const ctIn1RangeProof = sdk.ConfidentialRange.fsProve(
  ctParamsExpected,
  ctParamsCase.gamma,
  ctOut1Bits.length,
  ctCk,
  ctCIn1,
  ctOpIn1,
  ctIn1Bits,
  ctIn1Comps,
  ctYOut1,
  ctYOut1Pairs
);
const ctIn2RangeProof = sdk.ConfidentialRange.fsProve(
  ctParamsExpected,
  ctParamsCase.gamma,
  ctOut1Bits.length,
  ctCk,
  ctCIn2,
  ctOpIn2,
  ctIn2Bits,
  ctIn2Comps,
  ctYOut2,
  ctYOut2Pairs
);
assert.ok(ctIn1RangeProof);
assert.ok(ctIn2RangeProof);
logProgress('validate-ocaml: verified input notes constructed');

console.log('validate-ocaml: confidential transaction shared surface passed');

console.log(
  'Validated the TypeScript SDK against the OCaml surface on deterministic shared-surface cases plus native bignum transaction preview parity, accepted-root-window and wallet-request digest/rejection parity, native non-canonical/out-of-range transaction encoding rejection, expanded Merkle envelope mutation rejection including membership index/path and root-depth mismatches, and randomized sampler bound checks.'
);
