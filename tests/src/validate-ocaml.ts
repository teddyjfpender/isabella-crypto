import assert from 'node:assert/strict';
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

type SampleOpening = { msg: number[]; rand: number[] };

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

function allBounded(values: number[], bound: number): boolean {
  return values.every(value => Number.isSafeInteger(value) && Math.abs(value) <= bound);
}

function logProgress(message: string): void {
  if (trace) {
    console.log(message);
  }
}

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
  transactionContext.root,
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
    args: transactionContextArgs.map((arg, index) => (index === 6 ? '-0' : arg)),
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
      index === 7 ? nonCanonicalFirstInteger(arg) : arg
    ),
  },
  {
    name: 'unsafe input vector element',
    args: transactionContextArgs.map((arg, index) =>
      index === 7 ? unsafeFirstInteger(arg) : arg
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
function ctWalletProofRequestDigestArgs(request: any): string[] {
  const context = request.context;
  return [
    context.protocolVersion.toString(),
    context.networkId,
    context.assetId.toString(),
    context.ledgerEpoch.toString(),
    context.root,
    context.publicFee.toString(),
    JSON.stringify(context.cIn1),
    JSON.stringify(context.cIn2),
    JSON.stringify(context.cOut1),
    JSON.stringify(context.cOut2),
    JSON.stringify(context.nf1),
    JSON.stringify(context.nf2),
    JSON.stringify(request.acceptedRoots),
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
        (root: string) => root !== walletProofRequest.context.root
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
  ...(reversedAcceptedRoots.join('|') === walletProofRequest.acceptedRoots.join('|')
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
    args: walletProofRequestArgs.map((arg, index) => (index === 6 ? '-0' : arg)),
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
      index === 14 ? nonCanonicalFirstInteger(arg) : arg
    ),
  },
  {
    name: 'unsafe spent-nullifier integer',
    args: walletProofRequestArgs.map((arg, index) =>
      index === 14 ? unsafeFirstInteger(arg) : arg
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
  transactionEnvelopeVector.context.root,
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
    args: merkleEnvelopeDigestArgs.map((arg, index) => (index === 7 ? '-0' : arg)),
  },
  {
    name: 'unsafe public fee',
    args: merkleEnvelopeDigestArgs.map((arg, index) =>
      index === 7 ? unsafeProtocolInteger : arg
    ),
  },
  {
    name: 'non-canonical context vector integer',
    args: merkleEnvelopeDigestArgs.map((arg, index) =>
      index === 8 ? nonCanonicalFirstInteger(arg) : arg
    ),
  },
  {
    name: 'unsafe context vector integer',
    args: merkleEnvelopeDigestArgs.map((arg, index) =>
      index === 8 ? unsafeFirstInteger(arg) : arg
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
  root: ctMerkleLedgerRoot,
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
    args: merkleEnvelopeVerifyArgs.map((arg, index) => (index === 16 ? '-0' : arg)),
  },
  {
    name: 'unsafe expected public fee',
    args: merkleEnvelopeVerifyArgs.map((arg, index) =>
      index === 16 ? unsafeProtocolInteger : arg
    ),
  },
  {
    name: 'plus-signed context protocol version',
    args: merkleEnvelopeVerifyArgs.map((arg, index) => (index === 18 ? `+${arg}` : arg)),
  },
  {
    name: 'non-canonical context vector integer',
    args: merkleEnvelopeVerifyArgs.map((arg, index) =>
      index === 24 ? nonCanonicalFirstInteger(arg) : arg
    ),
  },
  {
    name: 'unsafe context vector integer',
    args: merkleEnvelopeVerifyArgs.map((arg, index) =>
      index === 24 ? unsafeFirstInteger(arg) : arg
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
const ocamlWrongRootContext = {
  ...ocamlEnvelopeContext,
  root: ocamlEnvelopeContext.root.replace(/^./, ocamlEnvelopeContext.root[0] === '0' ? '1' : '0'),
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
  ocamlEnvelopeContext.root,
  ctNf1
)) {
  const mutatedContext =
    mutation.root === ocamlEnvelopeContext.root
      ? ocamlEnvelopeContext
      : { ...ocamlEnvelopeContext, root: mutation.root };
  const mutatedPolicy =
    mutation.root === ocamlEnvelopePolicy.root
      ? ocamlEnvelopePolicy
      : { ...ocamlEnvelopePolicy, root: mutation.root };
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
  'Validated the TypeScript SDK against the OCaml surface on deterministic shared-surface cases plus native wallet-request digest/rejection parity, native non-canonical/out-of-range transaction encoding rejection, Merkle envelope mutation, and randomized sampler bound checks.'
);
