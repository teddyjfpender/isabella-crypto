#!/usr/bin/env node
import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';

const __filename = fileURLToPath(import.meta.url);
const __dirname = path.dirname(__filename);
const projectRoot = path.resolve(__dirname, '..');
const out = process.env.OUT ?? path.join(projectRoot, 'tests/fixtures/confidential-bigint-nullifier-vectors.json');
const sdk = await import(pathToFileURL(path.join(projectRoot, 'isabella.ts/dist/index.mjs')).href);

const q83 = 4835703278458516765933661n;
const beta = 65536n;
const gamma = 16777216n;

function decimalize(value) {
  if (typeof value === 'bigint') {
    return value.toString(10);
  }
  if (Array.isArray(value)) {
    return value.map(decimalize);
  }
  if (value && typeof value === 'object') {
    return Object.fromEntries(Object.entries(value).map(([key, item]) => [key, decimalize(item)]));
  }
  return value;
}

function openingCommit(key, opening) {
  const vector = [...opening.msg, ...opening.rand];
  return key.map((row) => {
    const raw = row.reduce((acc, value, index) => acc + value * vector[index], 0n);
    const reduced = raw % q83;
    return reduced < 0n ? reduced + q83 : reduced;
  });
}

const params = sdk.ConfidentialBalanceBigInt.makeParams(2, 2, q83, beta);
const ck = [
  [1n, q83 - 1n, 2n],
  [2n, 3n, q83 - 2n],
];
const nk = [
  [3n, q83 - 4n, 5n],
  [q83 - 7n, 11n, 13n],
];
const opening = { msg: [5n], rand: [beta, -beta] };
const c = openingCommit(ck, opening);
const nf = openingCommit(nk, opening);
const masks = Array.from({ length: sdk.ConfidentialNullifierBigInt.fsRounds() }, (_, round) => ({
  msg: [BigInt((round + 3) % 11) - 5n],
  rand: [
    BigInt((round * 2 + 1) % 13) - 6n,
    6n - BigInt((round * 3 + 2) % 13),
  ],
}));

const proof = sdk.ConfidentialNullifierBigInt.fsProve(params, gamma, ck, nk, c, nf, opening, masks);
if (proof === null) {
  throw new Error('failed to build q83 BigInt nullifier proof fixture');
}
if (!sdk.ConfidentialNullifierBigInt.fsVerify(params, gamma, ck, nk, c, nf, proof)) {
  throw new Error('q83 BigInt nullifier proof fixture does not verify');
}

const fields = sdk.ConfidentialNullifierBigInt.fsFields(
  ck,
  nk,
  c,
  nf,
  proof.aCommits,
  proof.aNullifiers
);
const firstRounds = sdk.ConfidentialNullifierBigInt
  .fsChallenges(params, ck, nk, c, nf, proof.aCommits, proof.aNullifiers, 4)
  .map((challenge, round) => ({ round, challenge }));

const fixture = decimalize({
  version: 1,
  algorithm: 'SHA3-256-counter-mode-low-bit',
  status: 'typescript-reference-with-native-preview-parity',
  notes: [
    'This fixture exercises q83-scale confidential-nullifier arithmetic in the TypeScript BigInt reference path.',
    'OCaml and Haskell preview commands rebuild and verify this fixture with multiprecision arithmetic.',
    'It proves the same bounded opening maps to both a note commitment and a nullifier; full launch integration remains a blocker.',
  ],
  params: {
    m: params.m,
    n1: params.n1,
    n2: params.n2,
    q: params.q,
    beta: params.beta,
    gamma,
  },
  bounds: {
    responseBoundChallenge1: sdk.ConfidentialNullifierBigInt.responseBound(params, gamma, 1),
  },
  maskPolicy: {
    msg: '[(round + 3) mod 11 - 5]',
    rand: '[(round * 2 + 1) mod 13 - 6, 6 - ((round * 3 + 2) mod 13)]',
  },
  transcript: {
    dst: sdk.ConfidentialNullifierBigInt.transcriptDst,
    domain: sdk.ConfidentialNullifierBigInt.fsDomain,
    fieldEncoding: sdk.ConfidentialNullifierBigInt.fieldEncoding,
    rounds: sdk.ConfidentialNullifierBigInt.fsRounds(),
    fields,
    firstRounds,
  },
  case: {
    name: 'q83-nullifier-basic',
    commitmentKey: ck,
    nullifierKey: nk,
    opening,
    commitment: c,
    nullifier: nf,
    masks,
    proof,
  },
});

fs.mkdirSync(path.dirname(out), { recursive: true });
fs.writeFileSync(out, `${JSON.stringify(fixture, null, 2)}\n`);
console.log(JSON.stringify({
  wrote: path.relative(projectRoot, out),
  case: fixture.case.name,
  q: fixture.params.q,
  proofRows: proof.aCommits.length,
  firstChallenges: firstRounds.map((entry) => entry.challenge),
}, null, 2));
