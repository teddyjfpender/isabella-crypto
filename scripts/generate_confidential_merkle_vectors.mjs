#!/usr/bin/env node
import fs from 'node:fs';
import path from 'node:path';
import { createHash } from 'node:crypto';
import { fileURLToPath } from 'node:url';

const __filename = fileURLToPath(import.meta.url);
const __dirname = path.dirname(__filename);
const projectRoot = path.resolve(__dirname, '..');
const out = process.env.OUT ?? path.join(projectRoot, 'tests/fixtures/confidential-merkle-vectors.json');

const dst = Buffer.from('ISABELLA-CT-MERKLE-v1', 'ascii');
const tags = {
  leaf: 0,
  node: 1,
  empty: 2,
};

function i64le(value) {
  const out = Buffer.alloc(8);
  out.writeBigInt64LE(BigInt(value), 0);
  return out;
}

function encodeIntVec(values) {
  return Buffer.concat([i64le(values.length), ...values.map(i64le)]);
}

function preimage(tag, body) {
  return Buffer.concat([dst, i64le(tag), body]);
}

function digestHex(buffer) {
  return createHash('sha3-256').update(buffer).digest('hex');
}

function leaf(commitment) {
  const encoded = preimage(tags.leaf, encodeIntVec(commitment));
  return {
    commitment,
    preimageHex: encoded.toString('hex'),
    digest: digestHex(encoded),
  };
}

function empty(width) {
  const encoded = preimage(tags.empty, i64le(width));
  return {
    width,
    preimageHex: encoded.toString('hex'),
    digest: digestHex(encoded),
  };
}

function node(leftDigest, rightDigest) {
  const encoded = preimage(
    tags.node,
    Buffer.concat([
      encodeIntVec([...Buffer.from(leftDigest, 'hex')]),
      encodeIntVec([...Buffer.from(rightDigest, 'hex')]),
    ])
  );
  return {
    left: leftDigest,
    right: rightDigest,
    preimageHex: encoded.toString('hex'),
    digest: digestHex(encoded),
  };
}

const leaf0 = leaf([1, -2, 3]);
const leaf1 = leaf([4, 5, -6]);
const emptyLeafWidth = empty(leaf0.commitment.length);
const parent01 = node(leaf0.digest, leaf1.digest);
const parent0Empty = node(leaf0.digest, emptyLeafWidth.digest);
const root = node(parent01.digest, parent0Empty.digest);

const vectors = {
  version: 1,
  algorithm: 'SHA3-256',
  dst: dst.toString('ascii'),
  integerEncoding: 'signed-64-bit-little-endian',
  vectorEncoding: 'len_i64_le || values_i64_le...',
  tags,
  leaves: [leaf0, leaf1],
  empty: [emptyLeafWidth],
  nodes: [parent01, parent0Empty, root],
  sampleRoot: root.digest,
};

fs.mkdirSync(path.dirname(out), { recursive: true });
fs.writeFileSync(out, `${JSON.stringify(vectors, null, 2)}\n`);
console.log(JSON.stringify(vectors, null, 2));
