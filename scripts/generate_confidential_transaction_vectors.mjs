#!/usr/bin/env node
import fs from 'node:fs';
import path from 'node:path';
import { createHash } from 'node:crypto';
import { fileURLToPath, pathToFileURL } from 'node:url';

const __filename = fileURLToPath(import.meta.url);
const __dirname = path.dirname(__filename);
const projectRoot = path.resolve(__dirname, '..');
const out = process.env.OUT ?? path.join(projectRoot, 'tests/fixtures/confidential-transaction-vectors.json');
const merkleVectorsPath = path.join(projectRoot, 'tests/fixtures/confidential-merkle-vectors.json');
const typeScriptEntry = path.join(projectRoot, 'isabella.ts/dist/index.mjs');

const dst = Buffer.from('ISABELLA-CT-TX-v1', 'ascii');
const protocolId = 'ISABELLA-CT-SIS-NOTE';
const tags = {
  context: 0,
  merkleProof: 1,
  envelope: 2,
  walletProofRequest: 3,
};

function i64le(value) {
  if (!Number.isSafeInteger(value)) {
    throw new RangeError(`non-canonical integer: ${value}`);
  }
  if (Object.is(value, -0)) {
    throw new RangeError('non-canonical integer: negative zero');
  }
  const out = Buffer.alloc(8);
  out.writeBigInt64LE(BigInt(value), 0);
  return out;
}

function nonNegativeI64le(value, label) {
  if (value < 0) {
    throw new RangeError(`${label} must be non-negative`);
  }
  return i64le(value);
}

function encodeAscii(value, label) {
  const bytes = [];
  for (let index = 0; index < value.length; index += 1) {
    const code = value.charCodeAt(index);
    if (code < 0x20 || code > 0x7e) {
      throw new Error(`${label}[${index}] must be printable ASCII`);
    }
    bytes.push(code);
  }
  return Buffer.concat([i64le(bytes.length), Buffer.from(bytes)]);
}

function encodeIntVec(values) {
  return Buffer.concat([i64le(values.length), ...values.map(i64le)]);
}

function encodeIntMatrix(rows) {
  return Buffer.concat([i64le(rows.length), ...rows.map(encodeIntVec)]);
}

function encodeDigest(digest) {
  if (!/^[0-9a-f]{64}$/.test(digest)) {
    throw new Error('digest must be a canonical lowercase SHA3-256 digest');
  }
  const bytes = Buffer.from(digest, 'hex');
  return Buffer.concat([i64le(bytes.length), bytes]);
}

function encodeDigestVector(digests) {
  return Buffer.concat([i64le(digests.length), ...digests.map(encodeDigest)]);
}

function contextPreimage(context) {
  return Buffer.concat([
    dst,
    i64le(tags.context),
    encodeAscii(protocolId, 'protocolId'),
    nonNegativeI64le(context.protocolVersion, 'protocolVersion'),
    encodeAscii(context.networkId, 'networkId'),
    nonNegativeI64le(context.assetId, 'assetId'),
    nonNegativeI64le(context.ledgerEpoch, 'ledgerEpoch'),
    encodeDigest(context.root),
    nonNegativeI64le(context.publicFee, 'publicFee'),
    encodeIntVec(context.cIn1),
    encodeIntVec(context.cIn2),
    encodeIntVec(context.cOut1),
    encodeIntVec(context.cOut2),
    encodeIntVec(context.nf1),
    encodeIntVec(context.nf2),
  ]);
}

function taggedPreimage(tag, body) {
  return Buffer.concat([
    dst,
    i64le(tag),
    encodeAscii(protocolId, 'protocolId'),
    body,
  ]);
}

function compareIntVec(left, right) {
  const width = Math.min(left.length, right.length);
  for (let index = 0; index < width; index += 1) {
    if (left[index] < right[index]) {
      return -1;
    }
    if (left[index] > right[index]) {
      return 1;
    }
  }
  return Math.sign(left.length - right.length);
}

function assertCanonicalDigestSet(digests, label) {
  if (digests.length === 0) {
    throw new Error(`${label} must not be empty`);
  }
  let previous = null;
  for (let index = 0; index < digests.length; index += 1) {
    const digest = digests[index];
    encodeDigest(digest);
    if (previous !== null && previous >= digest) {
      throw new Error(`${label} must be sorted lexicographically with no duplicates`);
    }
    previous = digest;
  }
}

function assertCanonicalIntMatrixSet(rows, label) {
  let previous = null;
  for (let index = 0; index < rows.length; index += 1) {
    const row = rows[index];
    for (const value of row) {
      i64le(value);
    }
    if (previous !== null && compareIntVec(previous, row) >= 0) {
      throw new Error(`${label} must be sorted lexicographically with no duplicates`);
    }
    previous = row;
  }
}

function sameVec(left, right) {
  return JSON.stringify(left) === JSON.stringify(right);
}

function containsVec(rows, value) {
  return rows.some((row) => sameVec(row, value));
}

function walletProofRequestPreimage(request) {
  assertCanonicalDigestSet(request.acceptedRoots, 'acceptedRoots');
  assertCanonicalIntMatrixSet(request.spentNullifiers, 'spentNullifiers');
  const contextDigest = digestHex(contextPreimage(request.context));
  if (!request.acceptedRoots.includes(request.context.root)) {
    throw new Error('context.root must be inside acceptedRoots');
  }
  if (sameVec(request.context.nf1, request.context.nf2)) {
    throw new Error('context nullifiers must be distinct');
  }
  if (
    containsVec(request.spentNullifiers, request.context.nf1) ||
    containsVec(request.spentNullifiers, request.context.nf2)
  ) {
    throw new Error('context nullifiers must be absent from spentNullifiers');
  }
  return taggedPreimage(
    tags.walletProofRequest,
    Buffer.concat([
      encodeDigest(contextDigest),
      encodeDigestVector(request.acceptedRoots),
      encodeIntMatrix(request.spentNullifiers),
    ])
  );
}

function digestHex(buffer) {
  return createHash('sha3-256').update(buffer).digest('hex');
}

async function buildMerkleTransactionFixture() {
  const sdk = await import(pathToFileURL(typeScriptEntry).href);
  const params = sdk.ConfidentialBalance.makeParams(2, 2, 17, 6);
  const ck = [
    [1, 0, 0],
    [0, 1, 0],
  ];
  const nk = [
    [0, 1, 0],
    [1, 0, 0],
  ];
  const gamma = 5;
  const k = 1;
  const rounds = sdk.ConfidentialBalance.fsRounds();
  const opIn1 = { msg: [1], rand: [1, 0] };
  const opIn2 = { msg: [1], rand: [0, 1] };
  const opOut1 = { msg: [1], rand: [1, 1] };
  const opOut2 = { msg: [1], rand: [0, 0] };
  const bit1 = [{ msg: [1], rand: [1, 1] }];
  const comp1 = [{ msg: [0], rand: [0, 0] }];
  const bit2 = [{ msg: [1], rand: [0, 0] }];
  const comp2 = [{ msg: [0], rand: [0, 0] }];
  const yIn1 = Array.from({ length: rounds }, () => ({ msg: [0], rand: [1, 0] }));
  const yIn2 = Array.from({ length: rounds }, () => ({ msg: [1], rand: [0, 1] }));
  const yBalance = Array.from({ length: rounds }, () => [0, 1]);
  const yOut1 = Array.from({ length: rounds }, () => [0, 1]);
  const yOut1Pairs = Array.from({ length: rounds }, () => [[0, 0]]);
  const yOut2 = Array.from({ length: rounds }, () => [1, 0]);
  const yOut2Pairs = Array.from({ length: rounds }, () => [[0, 0]]);
  const commitOf = (opening) =>
    sdk.Zq.matVecMultMod(ck, sdk.Vec.concat(opening.msg, opening.rand), params.q);
  const cIn1 = commitOf(opIn1);
  const cIn2 = commitOf(opIn2);
  const cOut1 = commitOf(opOut1);
  const cOut2 = commitOf(opOut2);
  const nf1 = sdk.ConfidentialTransaction.nullifier(params, nk, opIn1);
  const nf2 = sdk.ConfidentialTransaction.nullifier(params, nk, opIn2);
  const ledger = [cIn1, cIn2];
  const spent = [];
  const proof = sdk.ConfidentialTransaction.fsProveMerkle(
    params,
    gamma,
    k,
    ck,
    nk,
    ledger,
    spent,
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
    bit1,
    comp1,
    bit2,
    comp2,
    yIn1,
    yIn2,
    yBalance,
    yOut1,
    yOut1Pairs,
    yOut2,
    yOut2Pairs
  );
  if (proof === null) {
    throw new Error('failed to build Merkle transaction fixture');
  }
  return {
    sdk,
    root: sdk.ConfidentialTransaction.merkleLedgerRoot(ledger),
    cIn1,
    cIn2,
    cOut1,
    cOut2,
    nf1,
    nf2,
    proof,
  };
}

const merkleVectors = JSON.parse(fs.readFileSync(merkleVectorsPath, 'utf8'));
const [leaf0, leaf1] = merkleVectors.leaves;
const baseContext = {
  protocolVersion: 1,
  networkId: 'isabella-local-devnet',
  assetId: 7,
  ledgerEpoch: 42,
  root: merkleVectors.sampleRoot,
  publicFee: 3,
  cIn1: leaf0.commitment,
  cIn2: leaf1.commitment,
  cOut1: [7, 8, 9],
  cOut2: [-1, 0, 1],
  nf1: [3, 2, 1],
  nf2: [-3, -2, -1],
};
const basePreimage = contextPreimage(baseContext);
const proofFixture = await buildMerkleTransactionFixture();
const envelopeContext = {
  protocolVersion: 1,
  networkId: 'isabella-local-devnet',
  assetId: 7,
  ledgerEpoch: 42,
  root: proofFixture.root,
  publicFee: 0,
  cIn1: proofFixture.cIn1,
  cIn2: proofFixture.cIn2,
  cOut1: proofFixture.cOut1,
  cOut2: proofFixture.cOut2,
  nf1: proofFixture.nf1,
  nf2: proofFixture.nf2,
};
const tx = proofFixture.sdk.ConfidentialTransaction;
const envelopeContextDigest = tx.transactionContextDigest(envelopeContext);
const proofPreimageHex = tx.transactionMerkleProofPreimageHex(proofFixture.proof);
const proofDigest = tx.transactionMerkleProofDigest(proofFixture.proof);
const envelope = {
  context: envelopeContext,
  contextDigest: envelopeContextDigest,
  proof: proofFixture.proof,
};
const envelopePreimageHex = tx.transactionEnvelopePreimageHex(envelope);
const envelopeDigest = tx.transactionEnvelopeDigest(envelope);
const extraAcceptedRoot = digestHex(Buffer.from('isabella-accepted-root-window-extra', 'ascii'));
const walletProofRequest = {
  context: envelopeContext,
  acceptedRoots: [proofFixture.root, extraAcceptedRoot].sort(),
  spentNullifiers: [
    [-9, 0, 9],
    [10, 11, 12],
  ],
};
const walletProofRequestPreimageHex = walletProofRequestPreimage(walletProofRequest).toString('hex');
const walletProofRequestDigest = digestHex(Buffer.from(walletProofRequestPreimageHex, 'hex'));
if (tx.transactionWalletProofRequestPreimageHex(walletProofRequest) !== walletProofRequestPreimageHex) {
  throw new Error('wallet proof request preimage implementation mismatch');
}
if (tx.transactionWalletProofRequestDigest(walletProofRequest) !== walletProofRequestDigest) {
  throw new Error('wallet proof request digest implementation mismatch');
}

const vectors = {
  version: 1,
  algorithm: 'SHA3-256',
  dst: dst.toString('ascii'),
  protocolId,
  integerEncoding: 'signed-64-bit-little-endian',
  stringEncoding: 'len_i64_le || printable_ascii_bytes',
  digestEncoding: 'len_i64_le || 32 raw digest bytes',
  vectorEncoding: 'len_i64_le || values_i64_le...',
  tags,
  cases: [
    {
      name: 'sis-note-context-basic',
      context: baseContext,
      preimageHex: basePreimage.toString('hex'),
      digest: digestHex(basePreimage),
    },
  ],
  merkleProofCases: [
    {
      name: 'sis-note-merkle-proof-basic',
      preimageHex: proofPreimageHex,
      digest: proofDigest,
    },
  ],
  envelopeCases: [
    {
      name: 'sis-note-envelope-basic',
      context: envelopeContext,
      contextDigest: envelopeContextDigest,
      proofDigest,
      preimageHex: envelopePreimageHex,
      digest: envelopeDigest,
    },
  ],
  walletProofRequestCases: [
    {
      name: 'sis-note-wallet-proof-request-basic',
      request: walletProofRequest,
      contextDigest: envelopeContextDigest,
      preimageHex: walletProofRequestPreimageHex,
      digest: walletProofRequestDigest,
    },
  ],
};

fs.mkdirSync(path.dirname(out), { recursive: true });
fs.writeFileSync(out, `${JSON.stringify(vectors, null, 2)}\n`);
console.log(JSON.stringify({
  version: vectors.version,
  algorithm: vectors.algorithm,
  dst: vectors.dst,
  tags: vectors.tags,
  cases: vectors.cases.map((entry) => ({
    name: entry.name,
    digest: entry.digest,
    preimageBytes: entry.preimageHex.length / 2,
  })),
  merkleProofCases: vectors.merkleProofCases.map((entry) => ({
    name: entry.name,
    digest: entry.digest,
    preimageBytes: entry.preimageHex.length / 2,
  })),
  envelopeCases: vectors.envelopeCases.map((entry) => ({
    name: entry.name,
    digest: entry.digest,
    preimageBytes: entry.preimageHex.length / 2,
  })),
  walletProofRequestCases: vectors.walletProofRequestCases.map((entry) => ({
    name: entry.name,
    digest: entry.digest,
    preimageBytes: entry.preimageHex.length / 2,
  })),
}, null, 2));
