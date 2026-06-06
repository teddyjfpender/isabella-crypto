#!/usr/bin/env node
import fs from 'node:fs';
import path from 'node:path';
import { createHash } from 'node:crypto';
import { fileURLToPath, pathToFileURL } from 'node:url';

const __filename = fileURLToPath(import.meta.url);
const __dirname = path.dirname(__filename);
const projectRoot = path.resolve(__dirname, '..');
const out = process.env.OUT ?? path.join(projectRoot, 'tests/fixtures/confidential-bignum-transaction-vectors.json');
const typeScriptEntry = path.join(projectRoot, 'isabella.ts/dist/index.mjs');
const balanceVectors = JSON.parse(
  fs.readFileSync(path.join(projectRoot, 'tests/fixtures/confidential-bigint-balance-vectors.json'), 'utf8')
);
const rangeVectors = JSON.parse(
  fs.readFileSync(path.join(projectRoot, 'tests/fixtures/confidential-bigint-range-vectors.json'), 'utf8')
);
const nullifierVectors = JSON.parse(
  fs.readFileSync(path.join(projectRoot, 'tests/fixtures/confidential-bigint-nullifier-vectors.json'), 'utf8')
);

const merkleDst = Buffer.from('ISABELLA-CT-MERKLE-BIGNUM-v1', 'ascii');
const transactionDst = Buffer.from('ISABELLA-CT-TX-BIGNUM-v1', 'ascii');
const protocolId = 'ISABELLA-CT-SIS-NOTE';
const integerEncoding = 'sign_u8 || len_i64_le || magnitude_le_minimal';
const tags = {
  context: 0,
  merkleProof: 1,
  envelope: 2,
  walletProofRequest: 3,
  acceptedRootWindow: 4,
};
const merkleTags = {
  leaf: 0,
  node: 1,
  empty: 2,
};

function i64le(value, label = 'integer') {
  if (!Number.isSafeInteger(value) || Object.is(value, -0)) {
    throw new RangeError(`${label} must be a canonical signed-64 integer`);
  }
  const out = Buffer.alloc(8);
  out.writeBigInt64LE(BigInt(value), 0);
  return out;
}

function nonNegativeI64le(value, label) {
  if (value < 0) {
    throw new RangeError(`${label} must be non-negative`);
  }
  return i64le(value, label);
}

function parseDecimal(value, label = 'integer') {
  if (typeof value === 'bigint') {
    return value;
  }
  if (typeof value === 'number') {
    if (!Number.isSafeInteger(value) || Object.is(value, -0)) {
      throw new RangeError(`${label} must be a safe signed integer`);
    }
    return BigInt(value);
  }
  if (typeof value === 'string' && /^(0|-?[1-9][0-9]*)$/.test(value)) {
    return BigInt(value);
  }
  throw new Error(`${label} must be bigint, safe number, or canonical decimal string`);
}

function encodeBignum(value, label = 'integer') {
  const normalized = parseDecimal(value, label);
  const negative = normalized < 0n;
  let magnitude = negative ? -normalized : normalized;
  const bytes = [];
  while (magnitude > 0n) {
    bytes.push(Number(magnitude & 0xffn));
    magnitude >>= 8n;
  }
  return Buffer.concat([
    Buffer.from([negative ? 1 : 0]),
    nonNegativeI64le(bytes.length, `${label}.magnitude_length`),
    Buffer.from(bytes),
  ]);
}

function encodeBignumVector(values, label = 'vector') {
  return Buffer.concat([
    nonNegativeI64le(values.length, `${label}.length`),
    ...values.map((value, index) => encodeBignum(value, `${label}[${index}]`)),
  ]);
}

function encodeBignumMatrix(rows, label = 'matrix') {
  return Buffer.concat([
    nonNegativeI64le(rows.length, `${label}.length`),
    ...rows.map((row, index) => encodeBignumVector(row, `${label}[${index}]`)),
  ]);
}

function encodeBignumMatrixArray(mats, label = 'matrixArray') {
  return Buffer.concat([
    nonNegativeI64le(mats.length, `${label}.length`),
    ...mats.map((mat, index) => encodeBignumMatrix(mat, `${label}[${index}]`)),
  ]);
}

function encodeBoolVector(values, label = 'boolVector') {
  return Buffer.concat([
    nonNegativeI64le(values.length, `${label}.length`),
    ...values.map((value, index) => i64le(value ? 1 : 0, `${label}[${index}]`)),
  ]);
}

function encodeAscii(value, label = 'ascii') {
  const bytes = [];
  for (let index = 0; index < value.length; index += 1) {
    const code = value.charCodeAt(index);
    if (code < 0x20 || code > 0x7e) {
      throw new Error(`${label}[${index}] must be printable ASCII`);
    }
    bytes.push(code);
  }
  return Buffer.concat([nonNegativeI64le(bytes.length, `${label}.length`), Buffer.from(bytes)]);
}

function encodeDigest(digest, label = 'digest') {
  if (!/^[0-9a-f]{64}$/.test(digest)) {
    throw new Error(`${label} must be a canonical lowercase SHA3-256 digest`);
  }
  const bytes = Buffer.from(digest, 'hex');
  return Buffer.concat([nonNegativeI64le(bytes.length, `${label}.length`), bytes]);
}

function encodeDigestVector(digests, label = 'digests') {
  return Buffer.concat([
    nonNegativeI64le(digests.length, `${label}.length`),
    ...digests.map((digest, index) => encodeDigest(digest, `${label}[${index}]`)),
  ]);
}

function encodeAcceptedRoot(root, label = 'root') {
  return Buffer.concat([
    encodeDigest(root.digest, `${label}.digest`),
    nonNegativeI64le(root.depth, `${label}.depth`),
  ]);
}

function encodeAcceptedRootVector(roots, label = 'roots') {
  return Buffer.concat([
    nonNegativeI64le(roots.length, `${label}.length`),
    ...roots.map((root, index) => encodeAcceptedRoot(root, `${label}[${index}]`)),
  ]);
}

function encodeAcceptedRootWindowEntry(entry, label = 'entry') {
  if (entry.expiresAtEpoch <= entry.validFromEpoch) {
    throw new Error(`${label}.expiresAtEpoch must be greater than validFromEpoch`);
  }
  return Buffer.concat([
    encodeAcceptedRoot(entry.root, `${label}.root`),
    nonNegativeI64le(entry.validFromEpoch, `${label}.validFromEpoch`),
    nonNegativeI64le(entry.expiresAtEpoch, `${label}.expiresAtEpoch`),
  ]);
}

function encodeAcceptedRootWindowEntryVector(entries, label = 'entries') {
  return Buffer.concat([
    nonNegativeI64le(entries.length, `${label}.length`),
    ...entries.map((entry, index) => encodeAcceptedRootWindowEntry(entry, `${label}[${index}]`)),
  ]);
}

function digestHex(preimage) {
  return createHash('sha3-256').update(preimage).digest('hex');
}

function merklePreimage(tag, body) {
  return Buffer.concat([merkleDst, i64le(tag, 'merkle.tag'), body]);
}

function merkleLeafPreimage(commitment) {
  return merklePreimage(merkleTags.leaf, encodeBignumVector(commitment, 'commitment'));
}

function merkleEmptyPreimage(width) {
  return merklePreimage(merkleTags.empty, nonNegativeI64le(width, 'width'));
}

function merkleNodePreimage(left, right) {
  return merklePreimage(merkleTags.node, Buffer.concat([
    encodeDigest(left, 'left'),
    encodeDigest(right, 'right'),
  ]));
}

function merkleLeaf(commitment) {
  return digestHex(merkleLeafPreimage(commitment));
}

function merkleEmpty(width) {
  return digestHex(merkleEmptyPreimage(width));
}

function merkleNode(left, right) {
  return digestHex(merkleNodePreimage(left, right));
}

function merkleRoot(commitments, emptyWidth = commitments[0]?.length ?? 0) {
  if (commitments.length === 0) {
    return merkleEmpty(emptyWidth);
  }
  let level = commitments.map(merkleLeaf);
  while (level.length > 1) {
    const empty = merkleEmpty(emptyWidth);
    const next = [];
    for (let index = 0; index < level.length; index += 2) {
      next.push(merkleNode(level[index], index + 1 < level.length ? level[index + 1] : empty));
    }
    level = next;
  }
  return level[0];
}

function transactionTaggedPreimage(tag, body) {
  return Buffer.concat([
    transactionDst,
    i64le(tag, 'transaction.tag'),
    encodeAscii(protocolId, 'protocolId'),
    body,
  ]);
}

function transactionContextPreimage(context) {
  return Buffer.concat([
    transactionDst,
    i64le(tags.context, 'transaction.tag'),
    encodeAscii(protocolId, 'protocolId'),
    nonNegativeI64le(context.protocolVersion, 'protocolVersion'),
    encodeAscii(context.networkId, 'networkId'),
    nonNegativeI64le(context.assetId, 'assetId'),
    nonNegativeI64le(context.ledgerEpoch, 'ledgerEpoch'),
    encodeAcceptedRoot(context.root, 'root'),
    encodeBignum(context.publicFee, 'publicFee'),
    encodeBignumVector(context.cIn1, 'cIn1'),
    encodeBignumVector(context.cIn2, 'cIn2'),
    encodeBignumVector(context.cOut1, 'cOut1'),
    encodeBignumVector(context.cOut2, 'cOut2'),
    encodeBignumVector(context.nf1, 'nf1'),
    encodeBignumVector(context.nf2, 'nf2'),
  ]);
}

function membershipPreimage(proof, label) {
  return Buffer.concat([
    nonNegativeI64le(proof.index, `${label}.index`),
    encodeDigest(proof.root, `${label}.root`),
    encodeDigestVector(proof.siblings, `${label}.siblings`),
    encodeBoolVector(proof.directions, `${label}.directions`),
  ]);
}

function nullifierProofPreimage(proof, label) {
  return Buffer.concat([
    encodeBignumMatrix(proof.aCommits, `${label}.aCommits`),
    encodeBignumMatrix(proof.aNullifiers, `${label}.aNullifiers`),
    encodeBignumMatrix(proof.zMsgs, `${label}.zMsgs`),
    encodeBignumMatrix(proof.zRands, `${label}.zRands`),
  ]);
}

function balanceProofPreimage(proof, label) {
  return Buffer.concat([
    encodeBignumMatrix(proof.as, `${label}.as`),
    encodeBignumMatrix(proof.zs, `${label}.zs`),
  ]);
}

function rangeProofPreimage(proof, label) {
  return Buffer.concat([
    encodeBignumMatrix(proof.bits, `${label}.bits`),
    encodeBignumMatrix(proof.comps, `${label}.comps`),
    encodeBignumMatrix(proof.amountAs, `${label}.amountAs`),
    encodeBignumMatrix(proof.amountZs, `${label}.amountZs`),
    encodeBignumMatrixArray(proof.pairAss, `${label}.pairAss`),
    encodeBignumMatrixArray(proof.pairZss, `${label}.pairZss`),
  ]);
}

function transactionMerkleProofPreimage(proof) {
  return transactionTaggedPreimage(tags.merkleProof, Buffer.concat([
    membershipPreimage(proof.in1Member, 'in1Member'),
    membershipPreimage(proof.in2Member, 'in2Member'),
    nullifierProofPreimage(proof.in1Nullifier, 'in1Nullifier'),
    nullifierProofPreimage(proof.in2Nullifier, 'in2Nullifier'),
    balanceProofPreimage(proof.balance, 'balance'),
    rangeProofPreimage(proof.out1Range, 'out1Range'),
    rangeProofPreimage(proof.out2Range, 'out2Range'),
  ]));
}

function transactionEnvelopePreimage(envelope) {
  const contextDigest = digestHex(transactionContextPreimage(envelope.context));
  if (contextDigest !== envelope.contextDigest) {
    throw new Error('context digest mismatch');
  }
  return transactionTaggedPreimage(tags.envelope, Buffer.concat([
    encodeDigest(contextDigest, 'contextDigest'),
    encodeDigest(digestHex(transactionMerkleProofPreimage(envelope.proof)), 'proofDigest'),
  ]));
}

function acceptedRootWindowPreimage(window) {
  return transactionTaggedPreimage(tags.acceptedRootWindow, Buffer.concat([
    nonNegativeI64le(window.protocolVersion, 'acceptedRootWindow.protocolVersion'),
    encodeAscii(window.networkId, 'acceptedRootWindow.networkId'),
    nonNegativeI64le(window.assetId, 'acceptedRootWindow.assetId'),
    nonNegativeI64le(window.ledgerEpoch, 'acceptedRootWindow.ledgerEpoch'),
    encodeAcceptedRootWindowEntryVector(window.roots, 'acceptedRootWindow.roots'),
  ]));
}

function walletProofRequestPreimage(request) {
  return transactionTaggedPreimage(tags.walletProofRequest, Buffer.concat([
    encodeDigest(digestHex(transactionContextPreimage(request.context)), 'contextDigest'),
    encodeAcceptedRootVector(request.acceptedRoots, 'acceptedRoots'),
    encodeBignumMatrix(request.spentNullifiers, 'spentNullifiers'),
  ]));
}

function addDecimal(value, delta) {
  return (BigInt(value) + BigInt(delta)).toString();
}

const sdk = await import(pathToFileURL(typeScriptEntry).href);
const balance = balanceVectors.case;
const range = rangeVectors.case;
const nullifier = nullifierVectors.case;
const q83 = rangeVectors.params.q;
const balanceProofJson = {
  as: [
    [q83, '1'],
    ['2', addDecimal(q83, -1)],
  ],
  zs: [
    ['33816576', '-33816576'],
    [addDecimal(q83, -2), '3'],
  ],
};
const rangeProofJson = {
  bits: [
    range.amountCommitment,
    [q83, '15'],
  ],
  comps: [
    [addDecimal(q83, -1), '16'],
    ['17', addDecimal(q83, -2)],
  ],
  amountAs: [
    [q83, '18'],
    ['19', addDecimal(q83, -3)],
  ],
  amountZs: [
    [rangeVectors.bounds.amountResponseBoundChallenge1, `-${rangeVectors.bounds.amountResponseBoundChallenge1}`],
    ['20', '-21'],
  ],
  pairAss: [
    [
      [q83, '22'],
      ['23', addDecimal(q83, -4)],
    ],
  ],
  pairZss: [
    [
      [rangeVectors.bounds.pairResponseBoundChallenge1, `-${rangeVectors.bounds.pairResponseBoundChallenge1}`],
      ['24', '-25'],
    ],
  ],
};
const nullifierProofJson = {
  aCommits: [
    [q83, '26'],
    ['27', addDecimal(q83, -5)],
  ],
  aNullifiers: [
    [addDecimal(q83, -6), '28'],
    ['29', q83],
  ],
  zMsgs: [
    ['16842752'],
    ['-16842752'],
  ],
  zRands: [
    ['30', addDecimal(q83, -7)],
    [addDecimal(q83, -8), '-31'],
  ],
};

const cIn1 = nullifier.commitment;
const cIn2 = range.amountCommitment;
const cOut1 = balance.commitment;
const cOut2 = [
  addDecimal(range.amountCommitment[0], rangeVectors.params.q),
  addDecimal(balance.commitment[1], -7),
];
const nf1 = nullifier.nullifier;
const nf2 = [addDecimal(nullifier.nullifier[0], 1), nullifier.nullifier[1]];
const ledger = [cIn1, cIn2, cOut1, cOut2];
const rootDigest = merkleRoot(ledger);
const sdkRootDigest = sdk.ConfidentialMerkleBigInt.root(ledger);
if (sdkRootDigest !== rootDigest) {
  throw new Error('bignum Merkle root implementation mismatch');
}
const in1Member = sdk.ConfidentialMerkleBigInt.membershipProve(ledger, cIn1);
const in2Member = sdk.ConfidentialMerkleBigInt.membershipProve(ledger, cIn2);
if (!in1Member || !in2Member) {
  throw new Error('failed to build bignum Merkle memberships');
}
if (in1Member.root !== rootDigest || in2Member.root !== rootDigest) {
  throw new Error('membership roots disagree with bignum Merkle root');
}

const proof = {
  in1Member,
  in2Member,
  in1Nullifier: nullifierProofJson,
  in2Nullifier: nullifierProofJson,
  balance: balanceProofJson,
  out1Range: rangeProofJson,
  out2Range: rangeProofJson,
};
const context = {
  protocolVersion: 1,
  networkId: 'isabella-local-devnet',
  assetId: 7,
  ledgerEpoch: 42,
  root: {
    digest: rootDigest,
    depth: in1Member.siblings.length,
  },
  publicFee: '18446744073709551615',
  cIn1,
  cIn2,
  cOut1,
  cOut2,
  nf1,
  nf2,
};
const contextPreimageHex = transactionContextPreimage(context).toString('hex');
const contextDigest = digestHex(Buffer.from(contextPreimageHex, 'hex'));
const proofPreimageHex = transactionMerkleProofPreimage(proof).toString('hex');
const proofDigest = digestHex(Buffer.from(proofPreimageHex, 'hex'));
const envelope = {
  context,
  contextDigest,
  proof,
};
const envelopePreimageHex = transactionEnvelopePreimage(envelope).toString('hex');
const envelopeDigest = digestHex(Buffer.from(envelopePreimageHex, 'hex'));
const acceptedRootWindow = {
  protocolVersion: context.protocolVersion,
  networkId: context.networkId,
  assetId: context.assetId,
  ledgerEpoch: context.ledgerEpoch,
  roots: [
    {
      root: context.root,
      validFromEpoch: 40,
      expiresAtEpoch: 45,
    },
    {
      root: {
        digest: digestHex(Buffer.from('alternate-root', 'ascii')),
        depth: context.root.depth,
      },
      validFromEpoch: 41,
      expiresAtEpoch: 46,
    },
  ].sort((left, right) =>
    `${left.root.digest}:${left.root.depth}`.localeCompare(`${right.root.digest}:${right.root.depth}`)
  ),
};
const acceptedRootWindowPreimageHex = acceptedRootWindowPreimage(acceptedRootWindow).toString('hex');
const acceptedRootWindowDigest = digestHex(Buffer.from(acceptedRootWindowPreimageHex, 'hex'));
const walletProofRequest = {
  context,
  acceptedRoots: acceptedRootWindow.roots.map((entry) => entry.root),
  spentNullifiers: [
    ['-9', '0'],
    ['10', '11'],
  ],
};
const walletProofRequestPreimageHex = walletProofRequestPreimage(walletProofRequest).toString('hex');
const walletProofRequestDigest = digestHex(Buffer.from(walletProofRequestPreimageHex, 'hex'));

const tx = sdk.ConfidentialTransactionBigInt;
if (tx.transactionContextPreimageHex(context) !== contextPreimageHex) {
  throw new Error('bignum transaction context preimage implementation mismatch');
}
if (tx.transactionContextDigest(context) !== contextDigest) {
  throw new Error('bignum transaction context digest implementation mismatch');
}
if (tx.transactionMerkleProofPreimageHex(proof) !== proofPreimageHex) {
  throw new Error('bignum transaction proof preimage implementation mismatch');
}
if (tx.transactionMerkleProofDigest(proof) !== proofDigest) {
  throw new Error('bignum transaction proof digest implementation mismatch');
}
if (tx.transactionEnvelopePreimageHex(envelope) !== envelopePreimageHex) {
  throw new Error('bignum transaction envelope preimage implementation mismatch');
}
if (tx.transactionEnvelopeDigest(envelope) !== envelopeDigest) {
  throw new Error('bignum transaction envelope digest implementation mismatch');
}
if (tx.transactionAcceptedRootWindowPreimageHex(acceptedRootWindow) !== acceptedRootWindowPreimageHex) {
  throw new Error('bignum accepted-root window preimage implementation mismatch');
}
if (tx.transactionAcceptedRootWindowDigest(acceptedRootWindow) !== acceptedRootWindowDigest) {
  throw new Error('bignum accepted-root window digest implementation mismatch');
}
if (tx.transactionWalletProofRequestPreimageHex(walletProofRequest) !== walletProofRequestPreimageHex) {
  throw new Error('bignum wallet proof request preimage implementation mismatch');
}
if (tx.transactionWalletProofRequestDigest(walletProofRequest) !== walletProofRequestDigest) {
  throw new Error('bignum wallet proof request digest implementation mismatch');
}

const fixture = {
  version: 1,
  algorithm: 'SHA3-256',
  status: 'typescript-bignum-transaction-namespace-preview',
  notes: [
    'This fixture pins the versioned bignum Merkle and transaction digest namespace for widened SIS-note parameters.',
    'It does not replace the existing signed-64 transaction namespace until OCaml/Haskell/native parity and launch wiring are complete.',
  ],
  merkle: {
    dst: merkleDst.toString('ascii'),
    integerEncoding,
    digestEncoding: 'len_i64_le || 32 raw digest bytes',
    tags: merkleTags,
  },
  transaction: {
    dst: transactionDst.toString('ascii'),
    protocolId,
    integerEncoding,
    digestEncoding: 'len_i64_le || 32 raw digest bytes',
    tags,
  },
  params: {
    q: rangeVectors.params.q,
    beta: rangeVectors.params.beta,
    gamma: rangeVectors.params.gamma,
    rangeBits: rangeVectors.params.k,
  },
  ledger,
  merkleCases: [
    {
      name: 'q83-bignum-leaf',
      commitment: cIn1,
      preimageHex: merkleLeafPreimage(cIn1).toString('hex'),
      digest: merkleLeaf(cIn1),
    },
    {
      name: 'q83-bignum-root',
      commitments: ledger,
      digest: rootDigest,
    },
  ],
  contextCases: [
    {
      name: 'q83-bignum-context',
      context,
      preimageHex: contextPreimageHex,
      digest: contextDigest,
    },
  ],
  merkleProofCases: [
    {
      name: 'q83-bignum-merkle-proof',
      proof,
      preimageHex: proofPreimageHex,
      digest: proofDigest,
    },
  ],
  envelopeCases: [
    {
      name: 'q83-bignum-envelope',
      envelope,
      preimageHex: envelopePreimageHex,
      digest: envelopeDigest,
    },
  ],
  acceptedRootWindowCases: [
    {
      name: 'q83-bignum-accepted-root-window',
      window: acceptedRootWindow,
      preimageHex: acceptedRootWindowPreimageHex,
      digest: acceptedRootWindowDigest,
    },
  ],
  walletProofRequestCases: [
    {
      name: 'q83-bignum-wallet-proof-request',
      request: walletProofRequest,
      preimageHex: walletProofRequestPreimageHex,
      digest: walletProofRequestDigest,
      contextDigest,
    },
  ],
};

fs.writeFileSync(out, `${JSON.stringify(fixture, null, 2)}\n`);
console.log(`wrote ${out}`);
