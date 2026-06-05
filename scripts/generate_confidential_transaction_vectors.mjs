#!/usr/bin/env node
import fs from 'node:fs';
import path from 'node:path';
import { createHash } from 'node:crypto';
import { fileURLToPath } from 'node:url';

const __filename = fileURLToPath(import.meta.url);
const __dirname = path.dirname(__filename);
const projectRoot = path.resolve(__dirname, '..');
const out = process.env.OUT ?? path.join(projectRoot, 'tests/fixtures/confidential-transaction-vectors.json');
const merkleVectorsPath = path.join(projectRoot, 'tests/fixtures/confidential-merkle-vectors.json');

const dst = Buffer.from('ISABELLA-CT-TX-v1', 'ascii');
const protocolId = 'ISABELLA-CT-SIS-NOTE';
const tags = {
  context: 0,
};

function i64le(value) {
  if (!Number.isSafeInteger(value)) {
    throw new RangeError(`non-canonical integer: ${value}`);
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

function encodeDigest(digest) {
  if (!/^[0-9a-f]{64}$/.test(digest)) {
    throw new Error('digest must be a canonical lowercase SHA3-256 digest');
  }
  const bytes = Buffer.from(digest, 'hex');
  return Buffer.concat([i64le(bytes.length), bytes]);
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

function digestHex(buffer) {
  return createHash('sha3-256').update(buffer).digest('hex');
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
};

fs.mkdirSync(path.dirname(out), { recursive: true });
fs.writeFileSync(out, `${JSON.stringify(vectors, null, 2)}\n`);
console.log(JSON.stringify(vectors, null, 2));
