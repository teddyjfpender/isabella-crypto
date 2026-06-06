#!/usr/bin/env node
import { mkdir, writeFile } from 'node:fs/promises';
import { createHash } from 'node:crypto';
import path from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';

const __filename = fileURLToPath(import.meta.url);
const __dirname = path.dirname(__filename);
const root = path.join(__dirname, '..');
const sdkPath = path.join(root, 'isabella.ts', 'dist', 'index.mjs');
const sdk = await import(pathToFileURL(sdkPath).href);

const q83 = 4835703278458516765933661n;
const beta = 65536n;
const gamma = 16777216n;
const k = 64;
const amount = 5n;
const params = sdk.ConfidentialBalanceBigInt.makeParams(2, 2, q83, beta);
const ck = [
  [1n, q83 - 1n, 2n],
  [2n, 3n, q83 - 2n],
];
const amountOpening = { msg: [amount], rand: [0n, 0n] };

const bitOpenings = Array.from({ length: k }, (_, index) => ({
  msg: [(amount >> BigInt(index)) & 1n],
  rand: [beta, -beta],
}));
const compOpenings = bitOpenings.map((opening) => ({
  msg: [1n - opening.msg[0]],
  rand: [0n, 0n],
}));

function openingCommit(opening) {
  const vector = [...opening.msg, ...opening.rand];
  return ck.map((row) => row.reduce((acc, value, index) => acc + value * vector[index], 0n) % q83);
}

function mask(round, salt) {
  return [
    BigInt((round + salt) % 11) - 5n,
    4n - BigInt((round * 3 + salt) % 9),
  ];
}

function amountMask(round) {
  return mask(round, 1);
}

function pairMask(round, bit) {
  return mask(round, bit + 7);
}

const cAmount = openingCommit(amountOpening);
const yAmounts = Array.from({ length: sdk.ConfidentialRangeBigInt.fsRounds() }, (_, round) =>
  amountMask(round)
);
const yPairss = Array.from({ length: sdk.ConfidentialRangeBigInt.fsRounds() }, (_, round) =>
  Array.from({ length: k }, (_, bit) => pairMask(round, bit))
);

const proof = sdk.ConfidentialRangeBigInt.fsProve(
  params,
  gamma,
  k,
  ck,
  cAmount,
  amountOpening,
  bitOpenings,
  compOpenings,
  yAmounts,
  yPairss
);

if (proof === null) {
  throw new Error('failed to build q83 BigInt range proof fixture');
}
if (!sdk.ConfidentialRangeBigInt.fsVerify(params, gamma, k, ck, cAmount, proof)) {
  throw new Error('q83 BigInt range proof fixture does not verify');
}

const transcriptFields = sdk.ConfidentialRangeBigInt
  .fsFields(ck, cAmount, proof.bits, proof.comps, proof.amountAs, proof.pairAss);
const firstRounds = sdk.ConfidentialRangeBigInt
  .fsChallenges(params, ck, cAmount, proof.bits, proof.comps, proof.amountAs, proof.pairAss, 4)
  .map((challenge, round) => ({ round, challenge }));
const amountWitnessBound = sdk.ConfidentialRangeBigInt.amountWitnessBound(params, k);
const amountResponseBoundChallenge1 = sdk.ConfidentialRangeBigInt.amountResponseBound(params, gamma, k, 1);
const pairResponseBoundChallenge1 = sdk.ConfidentialRangeBigInt.pairResponseBound(params, gamma, 1);

function decimalize(value) {
  if (typeof value === 'bigint') {
    return value.toString();
  }
  if (Array.isArray(value)) {
    return value.map(decimalize);
  }
  if (value && typeof value === 'object') {
    return Object.fromEntries(Object.entries(value).map(([key, item]) => [key, decimalize(item)]));
  }
  return value;
}

const proofJson = JSON.stringify(decimalize(proof));
const proofDigest = createHash('sha3-256').update(proofJson).digest('hex');

const fixture = decimalize({
  version: 1,
  algorithm: 'SHA3-256-counter-mode-low-bit',
  status: 'typescript-reference-with-native-preview-parity',
  notes: [
    'This fixture exercises q83-scale confidential-range arithmetic in the TypeScript BigInt reference path.',
    'OCaml and Haskell preview commands rebuild and verify the compact proof commitment with multiprecision arithmetic.',
    'It uses k=64 so the amount residual witness/response bounds cross the current safe-integer runtime model; full launch integration remains a blocker.',
  ],
  params: {
    m: params.m,
    n2: params.n2,
    q: params.q,
    beta: params.beta,
    gamma,
    k,
  },
  bounds: {
    amountWitnessBound,
    amountResponseBoundChallenge1,
    pairResponseBoundChallenge1,
  },
  maskPolicy: {
    amountMask: '[(round + 1) mod 11 - 5, 4 - ((round * 3 + 1) mod 9)]',
    pairMask: '[(round + bit + 7) mod 11 - 5, 4 - ((round * 3 + bit + 7) mod 9)]',
  },
  transcript: {
    dst: sdk.ConfidentialRangeBigInt.transcriptDst,
    domain: sdk.ConfidentialRangeBigInt.fsDomain,
    fieldEncoding: sdk.ConfidentialRangeBigInt.fieldEncoding,
    rounds: sdk.ConfidentialRangeBigInt.fsRounds(),
    fields: transcriptFields,
    firstRounds,
  },
  proofCommitment: {
    hash: 'sha3-256',
    digest: proofDigest,
    canonicalJsonBytes: Buffer.byteLength(proofJson, 'utf8'),
    amountRows: proof.amountAs.length,
    pairRounds: proof.pairAss.length,
    pairRowsPerRound: proof.pairAss[0]?.length ?? 0,
    sample: {
      firstAmountAnnouncement: proof.amountAs[0],
      firstAmountResponse: proof.amountZs[0],
      firstPairAnnouncement: proof.pairAss[0]?.[0] ?? [],
      firstPairResponse: proof.pairZss[0]?.[0] ?? [],
    },
  },
  case: {
    name: 'q83-range-64bit-residual',
    commitmentKey: ck,
    amount,
    amountOpening,
    amountCommitment: cAmount,
    bitOpenings,
    compOpenings,
  },
});

const out = path.join(root, 'tests', 'fixtures', 'confidential-bigint-range-vectors.json');
await mkdir(path.dirname(out), { recursive: true });
await writeFile(out, `${JSON.stringify(fixture, null, 2)}\n`, 'utf8');
console.log(JSON.stringify({
  wrote: path.relative(root, out),
  case: fixture.case.name,
  q: fixture.params.q,
  k: fixture.params.k,
  amountWitnessBound: fixture.bounds.amountWitnessBound,
  firstChallenges: fixture.transcript.firstRounds.map((entry) => entry.challenge),
}, null, 2));
