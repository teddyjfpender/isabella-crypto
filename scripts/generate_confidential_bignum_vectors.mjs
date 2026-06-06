#!/usr/bin/env node
import fs from 'node:fs';
import path from 'node:path';
import { createHash } from 'node:crypto';
import { fileURLToPath } from 'node:url';

const __filename = fileURLToPath(import.meta.url);
const __dirname = path.dirname(__filename);
const projectRoot = path.resolve(__dirname, '..');
const out = process.env.OUT ?? path.join(projectRoot, 'tests/fixtures/confidential-bignum-vectors.json');

const dst = 'ISABELLA-CT-BIGNUM-v1';
const integerEncoding = 'sign_u8 || len_i64_le || magnitude_le_minimal';
const vectorEncoding = 'len_i64_le || bignum...';

function i64le(value) {
  if (!Number.isSafeInteger(value) || value < 0) {
    throw new RangeError(`non-canonical length: ${value}`);
  }
  const bytes = Buffer.alloc(8);
  bytes.writeBigInt64LE(BigInt(value), 0);
  return bytes;
}

function parseCanonicalBigInt(value) {
  if (!/^(0|-?[1-9][0-9]*)$/.test(value)) {
    throw new Error(`non-canonical integer: ${value}`);
  }
  return BigInt(value);
}

function encodeBigIntDecimal(value) {
  const normalized = parseCanonicalBigInt(value);
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

function encodeBigIntVector(values) {
  return Buffer.concat([
    i64le(values.length),
    ...values.map(encodeBigIntDecimal),
  ]);
}

function digestHex(encoded) {
  return createHash('sha3-256')
    .update(Buffer.concat([Buffer.from(dst, 'ascii'), encoded]))
    .digest('hex');
}

const q83 = '4835703278458516765933661';
const largestSisBound = '2417851639229258382966784';
const rangeExtractedResponse = '1208925819614629208260608';

const scalarInputs = [
  ['zero', '0'],
  ['one', '1'],
  ['minus-one', '-1'],
  ['byte-boundary-255', '255'],
  ['byte-boundary-256', '256'],
  ['minus-byte-boundary-256', '-256'],
  ['typescript-max-safe', '9007199254740991'],
  ['minus-typescript-max-safe', '-9007199254740991'],
  ['q83-modulus', q83],
  ['largest-sis-bound', largestSisBound],
  ['minus-largest-sis-bound', `-${largestSisBound}`],
  ['range-extracted-response', rangeExtractedResponse],
];

const vectorInputs = [
  ['empty', []],
  ['small-mixed', ['0', '1', '-1', '255', '256', '-256']],
  ['q83-runtime-blocker', [q83, largestSisBound, `-${largestSisBound}`, rangeExtractedResponse]],
];

const scalarCases = scalarInputs.map(([name, decimal]) => {
  const encoded = encodeBigIntDecimal(decimal);
  return {
    name,
    decimal,
    encodedHex: encoded.toString('hex'),
    digest: digestHex(encoded),
  };
});

const vectorCases = vectorInputs.map(([name, decimals]) => {
  const encoded = encodeBigIntVector(decimals);
  return {
    name,
    decimals,
    encodedHex: encoded.toString('hex'),
    digest: digestHex(encoded),
  };
});

const fixture = {
  version: 1,
  algorithm: 'canonical-signed-magnitude-little-endian',
  dst,
  integerEncoding,
  vectorEncoding,
  notes: [
    'This fixture defines the production bignum codec target for widened confidential-transfer parameters.',
    'Fiat-Shamir transcript fields consume this codec; proof arithmetic, proof APIs, and transaction/runtime integer surfaces still need multiprecision integration before launch.'
  ],
  scalarCases,
  vectorCases,
  rejectedDecimals: [
    '',
    '+1',
    '-0',
    '00',
    '01',
    '-01',
    '1.0',
    ' 1',
    '1 '
  ],
};

fs.writeFileSync(out, `${JSON.stringify(fixture, null, 2)}\n`);
console.log(`wrote ${out}`);
