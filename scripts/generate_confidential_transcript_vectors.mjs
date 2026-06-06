#!/usr/bin/env node
import fs from 'node:fs';
import path from 'node:path';
import { createHash } from 'node:crypto';
import { fileURLToPath } from 'node:url';

const __filename = fileURLToPath(import.meta.url);
const __dirname = path.dirname(__filename);
const projectRoot = path.resolve(__dirname, '..');
const out = process.env.OUT ?? path.join(projectRoot, 'tests/fixtures/confidential-transcript-vectors.json');

const dst = Buffer.from('ISABELLA-CT-FS-v1', 'ascii');
const controlEncoding = 'domain_i64_le || round_i64_le || field_count_i64_le';
const fieldEncoding = 'sign_u8 || len_i64_le || magnitude_le_minimal';
const integerEncoding = `control=${controlEncoding}; field=${fieldEncoding}`;

function i64le(value) {
  const out = Buffer.alloc(8);
  out.writeBigInt64LE(BigInt(value), 0);
  return out;
}

function encodeTranscriptField(value) {
  const normalized = BigInt(value);
  const negative = normalized < 0n;
  let magnitude = negative ? -normalized : normalized;
  const bytes = [];
  while (magnitude > 0n) {
    bytes.push(Number(magnitude & 0xffn));
    magnitude >>= 8n;
  }
  return Buffer.concat([
    Buffer.from([negative ? 1 : 0]),
    i64le(bytes.length),
    Buffer.from(bytes),
  ]);
}

function encodeTranscript(domain, round, fields) {
  return Buffer.concat([
    dst,
    i64le(domain),
    i64le(round),
    i64le(fields.length),
    ...fields.map(encodeTranscriptField),
  ]);
}

function challenge(domain, fields, round) {
  const digest = createHash('sha3-256').update(encodeTranscript(domain, round, fields)).digest();
  return { round, digest: digest.toString('hex'), challenge: digest[0] & 1 };
}

function sum(xs) {
  return xs.reduce((acc, value) => acc + value, 0);
}

function flatten(xs) {
  return xs.flat(Infinity);
}

const balance = {
  name: 'balance-basic',
  domain: 1001,
  ck: [[1, 0, 0], [0, 1, 0]],
  c: [1, 2],
  as: [[3, 4], [5, -6], [7, 8]],
};
balance.fields = [sum(flatten(balance.ck)), sum(balance.c), sum(flatten(balance.as))];

const range = {
  name: 'range-basic',
  domain: 2001,
  ck: [[1, 0, 0], [0, 1, 0]],
  cAmount: [11, 12],
  cBits: [[1, 2], [3, 4], [5, 6]],
  cComps: [[7, 8], [9, 10], [11, 12]],
  aAmounts: [[13, 14], [15, 16]],
  aPairss: [
    [[17, 18], [19, 20], [21, 22]],
    [[23, 24], [25, 26], [27, 28]],
  ],
};
range.fields = [
  sum(flatten(range.ck)),
  sum(range.cAmount),
  sum(flatten(range.cBits)),
  sum(flatten(range.cComps)),
  sum(flatten(range.aAmounts)),
  sum(flatten(range.aPairss)),
];

const nullifier = {
  name: 'nullifier-basic',
  domain: 3001,
  ck: [[1, 0, 0], [0, 1, 0]],
  nk: [[0, 1, 0], [1, 0, 0]],
  c: [29, 30],
  nf: [31, 32],
  aCommits: [[33, 34], [35, 36]],
  aNullifiers: [[37, 38], [39, 40]],
};
nullifier.fields = [
  sum(flatten(nullifier.ck)),
  sum(flatten(nullifier.nk)),
  sum(nullifier.c),
  sum(nullifier.nf),
  sum(flatten(nullifier.aCommits)),
  sum(flatten(nullifier.aNullifiers)),
];

const nullifierCanonical = {
  name: 'nullifier-canonical-basic',
  domain: 3001,
  ck: nullifier.ck,
  nk: nullifier.nk,
  c: nullifier.c,
  nf: nullifier.nf,
  aCommit: nullifier.aCommits[0],
  aNullifier: nullifier.aNullifiers[0],
};
nullifierCanonical.fields = [
  sum(flatten(nullifierCanonical.ck)),
  sum(flatten(nullifierCanonical.nk)),
  sum(nullifierCanonical.c),
  sum(nullifierCanonical.nf),
  sum(nullifierCanonical.aCommit),
  sum(nullifierCanonical.aNullifier),
];

const signedFields = {
  name: 'signed-fields-direct',
  domain: 1001,
  fields: [0, -1, 255, 256, -256],
};

const vectors = {
  version: 1,
  algorithm: 'SHA3-256-counter-mode-low-bit',
  dst: dst.toString('ascii'),
  integerEncoding,
  controlEncoding,
  fieldEncoding,
  transcriptLayout: 'dst || domain_i64_le || round_i64_le || field_count_i64_le || fields_bignum...',
  cases: [balance, range, nullifier, nullifierCanonical, signedFields].map((entry) => ({
    ...entry,
    rounds: [0, 1, 2, 3].map((round) => challenge(entry.domain, entry.fields, round)),
  })),
};

fs.mkdirSync(path.dirname(out), { recursive: true });
fs.writeFileSync(out, `${JSON.stringify(vectors, null, 2)}\n`);
console.log(JSON.stringify(vectors, null, 2));
