#!/usr/bin/env node
import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';

const __filename = fileURLToPath(import.meta.url);
const __dirname = path.dirname(__filename);
const projectRoot = path.resolve(__dirname, '..');
const out = process.env.OUT ?? path.join(projectRoot, 'tests/fixtures/confidential-bigint-balance-vectors.json');
const sdk = await import(pathToFileURL(path.join(projectRoot, 'isabella.ts/dist/index.mjs')).href);

const q83 = 4835703278458516765933661n;
const beta = 65536n;
const gamma = 16777216n;

function decimal(value) {
  return value.toString(10);
}

function decimalVec(values) {
  return values.map(decimal);
}

function decimalMatrix(rows) {
  return rows.map(decimalVec);
}

function decimalProof(proof) {
  return {
    as: decimalMatrix(proof.as),
    zs: decimalMatrix(proof.zs),
  };
}

const params = sdk.ConfidentialBalanceBigInt.makeParams(2, 2, q83, beta);
const ck = [
  [1n, q83 - 1n, 2n],
  [2n, 3n, q83 - 2n],
];
const witness = [4n, -5n];
const masks = Array.from({ length: sdk.ConfidentialBalanceBigInt.fsRounds() }, (_, round) => {
  const left = BigInt((round % 5) - 2);
  const right = BigInt(2 - (round % 7));
  return [left, right];
});

const commitment = sdk.ConfidentialBalanceBigInt.randCommit(params, ck, witness);
const proof = sdk.ConfidentialBalanceBigInt.fsProve(params, gamma, ck, commitment, witness, masks);
if (proof === null) {
  throw new Error('failed to build q83 BigInt balance proof fixture');
}
if (!sdk.ConfidentialBalanceBigInt.fsVerify(params, gamma, ck, commitment, proof)) {
  throw new Error('q83 BigInt balance proof fixture does not verify');
}

const fields = sdk.ConfidentialBalanceBigInt.fsFields(ck, commitment, proof.as);
const rounds = sdk.ConfidentialBalanceBigInt
  .fsChallenges(params, ck, commitment, proof.as, 4)
  .map((challenge, round) => ({ round, challenge }));

const fixture = {
  version: 1,
  algorithm: 'SHA3-256-counter-mode-low-bit',
  status: 'typescript-reference-with-native-preview-parity',
  notes: [
    'This fixture exercises q83-scale confidential-balance arithmetic in the TypeScript BigInt reference path.',
    'OCaml and Haskell preview commands verify this fixture with multiprecision arithmetic; full launch integration remains a blocker.'
  ],
  params: {
    m: params.m,
    n1: params.n1,
    n2: params.n2,
    q: decimal(params.q),
    beta: decimal(params.beta),
    gamma: decimal(gamma),
  },
  transcript: {
    dst: sdk.ConfidentialBalanceBigInt.transcriptDst,
    domain: sdk.ConfidentialBalanceBigInt.fsDomain,
    fieldEncoding: sdk.ConfidentialBalanceBigInt.fieldEncoding,
    fields: decimalVec(fields),
    firstRounds: rounds,
  },
  case: {
    name: 'q83-balance-basic',
    commitmentKey: decimalMatrix(ck),
    witness: decimalVec(witness),
    commitment: decimalVec(commitment),
    masks: decimalMatrix(masks),
    proof: decimalProof(proof),
  },
};

fs.mkdirSync(path.dirname(out), { recursive: true });
fs.writeFileSync(out, `${JSON.stringify(fixture, null, 2)}\n`);
console.log(JSON.stringify({
  wrote: path.relative(projectRoot, out),
  case: fixture.case.name,
  q: fixture.params.q,
  proofRows: proof.as.length,
  firstChallenges: rounds.map((entry) => entry.challenge),
}, null, 2));
