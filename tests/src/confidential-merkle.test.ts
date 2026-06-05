import fs from 'node:fs';
import path from 'node:path';
import { createHash } from 'node:crypto';
import { fileURLToPath } from 'node:url';

const __filename = fileURLToPath(import.meta.url);
const __dirname = path.dirname(__filename);
const projectRoot = path.resolve(__dirname, '..', '..');
const vectorsPath = path.join(projectRoot, 'tests/fixtures/confidential-merkle-vectors.json');

type MerkleVector = {
  preimageHex: string;
  digest: string;
};

type MerkleVectors = {
  version: number;
  algorithm: string;
  dst: string;
  integerEncoding: string;
  vectorEncoding: string;
  tags: { leaf: number; node: number; empty: number };
  leaves: MerkleVector[];
  empty: MerkleVector[];
  nodes: MerkleVector[];
  sampleRoot: string;
};

function sha3Hex(preimageHex: string): string {
  return createHash('sha3-256')
    .update(Buffer.from(preimageHex, 'hex'))
    .digest('hex');
}

describe('Confidential Merkle hash vectors', () => {
  const vectors = JSON.parse(fs.readFileSync(vectorsPath, 'utf8')) as MerkleVectors;

  it('pins the canonical Merkle domain and tags', () => {
    expect(vectors.algorithm).toBe('SHA3-256');
    expect(vectors.dst).toBe('ISABELLA-CT-MERKLE-v1');
    expect(vectors.integerEncoding).toBe('signed-64-bit-little-endian');
    expect(vectors.vectorEncoding).toBe('len_i64_le || values_i64_le...');
    expect(vectors.tags).toEqual({ leaf: 0, node: 1, empty: 2 });
  });

  it('hashes every pinned preimage to the recorded digest', () => {
    for (const entry of [...vectors.leaves, ...vectors.empty, ...vectors.nodes]) {
      expect(sha3Hex(entry.preimageHex)).toBe(entry.digest);
    }
    expect(vectors.nodes.at(-1)?.digest).toBe(vectors.sampleRoot);
  });

  it('keeps leaf, empty, and node encodings domain separated', () => {
    const preimages = [
      ...vectors.leaves.map((entry) => entry.preimageHex),
      ...vectors.empty.map((entry) => entry.preimageHex),
      ...vectors.nodes.map((entry) => entry.preimageHex),
    ];
    expect(new Set(preimages).size).toBe(preimages.length);
  });
});
