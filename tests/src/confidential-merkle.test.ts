import fs from 'node:fs';
import path from 'node:path';
import { createHash } from 'node:crypto';
import { fileURLToPath, pathToFileURL } from 'node:url';

import { buildMerkleTransactionFixture } from './confidential-fixtures.ts';
import { merkleTransactionProofMutations } from './confidential-proof-mutations.ts';

const __filename = fileURLToPath(import.meta.url);
const __dirname = path.dirname(__filename);
const projectRoot = path.resolve(__dirname, '..', '..');
const vectorsPath = path.join(projectRoot, 'tests/fixtures/confidential-merkle-vectors.json');
const typeScriptEntry = path.join(projectRoot, 'isabella.ts/dist/index.mjs');

type MerkleVector = {
  preimageHex: string;
  digest: string;
};

type LeafVector = MerkleVector & {
  commitment: number[];
};

type EmptyVector = MerkleVector & {
  width: number;
};

type NodeVector = MerkleVector & {
  left: string;
  right: string;
};

type MerkleVectors = {
  version: number;
  algorithm: string;
  dst: string;
  integerEncoding: string;
  vectorEncoding: string;
  tags: { leaf: number; node: number; empty: number };
  leaves: LeafVector[];
  empty: EmptyVector[];
  nodes: NodeVector[];
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

  it('matches the TypeScript Merkle API for leaves, nodes, roots, and paths', async () => {
    const sdk = await import(pathToFileURL(typeScriptEntry).href);
    const merkle = sdk.ConfidentialMerkle;
    const [leaf0, leaf1] = vectors.leaves;
    const [empty2] = vectors.empty;
    const [parent01, parent0Empty, root] = vectors.nodes;

    expect(merkle.dst).toBe(vectors.dst);
    expect(merkle.tags).toEqual(vectors.tags);
    expect(merkle.encodeLeaf(leaf0.commitment)).toBe(leaf0.preimageHex);
    expect(merkle.leaf(leaf0.commitment)).toBe(leaf0.digest);
    expect(merkle.encodeEmpty(empty2.width)).toBe(empty2.preimageHex);
    expect(merkle.empty(empty2.width)).toBe(empty2.digest);
    expect(merkle.encodeNode(parent01.left, parent01.right)).toBe(parent01.preimageHex);
    expect(merkle.node(parent01.left, parent01.right)).toBe(parent01.digest);

    const ledger = [leaf0.commitment, leaf1.commitment, leaf0.commitment];
    expect(merkle.root(ledger)).toBe(root.digest);

    const proof = merkle.membershipProve(ledger, leaf1.commitment);
    expect(proof).not.toBeNull();
    expect(proof!.root).toBe(vectors.sampleRoot);
    expect(merkle.membershipVerify(leaf1.commitment, proof!)).toBe(true);
    expect(merkle.pathRoot(leaf1.commitment, proof!.siblings, proof!.directions)).toBe(
      vectors.sampleRoot
    );

    expect(merkle.membershipVerify(leaf0.commitment, proof!)).toBe(false);
    expect(
      merkle.membershipVerify(leaf1.commitment, {
        ...proof!,
        siblings: [parent0Empty.digest, ...proof!.siblings.slice(1)],
      })
    ).toBe(false);
    expect(
      merkle.membershipVerify(leaf1.commitment, {
        ...proof!,
        directions: proof!.directions.map((direction: boolean, index: number) =>
          index === 0 ? !direction : direction
        ),
      })
    ).toBe(false);
    expect(
      merkle.membershipVerify(leaf1.commitment, {
        ...proof!,
        root: proof!.root.toUpperCase(),
      })
    ).toBe(false);
    expect(() => merkle.root([leaf0.commitment, [1, 2]])).toThrow();
    expect(() => merkle.leaf([Number.MAX_SAFE_INTEGER + 1])).toThrow();
  });

  it('verifies confidential transactions against cryptographic Merkle roots', async () => {
    const {
      sdk,
      params,
      gamma,
      k,
      ck,
      nk,
      ledger,
      root,
      spent,
      cIn1,
      cIn2,
      cOut1,
      cOut2,
      nf1,
      nf2,
      proof,
    } = await buildMerkleTransactionFixture();
    expect(sdk.ConfidentialTransaction.fsVerifyMerkle(
      params,
      gamma,
      k,
      ck,
      nk,
      root.digest,
      spent,
      cIn1,
      cIn2,
      cOut1,
      cOut2,
      nf1,
      nf2,
      proof
    )).toBe(true);
    expect(sdk.ConfidentialTransaction.fsVerifyMerkle(
      params,
      gamma,
      k,
      ck,
      nk,
      JSON.stringify(sdk.ConfidentialTransaction.ledgerRoot(params, ledger)),
      spent,
      cIn1,
      cIn2,
      cOut1,
      cOut2,
      nf1,
      nf2,
      proof
    )).toBe(false);
    expect(sdk.ConfidentialTransaction.fsVerifyMerkle(
      params,
      gamma,
      k,
      ck,
      nk,
      root.digest,
      spent,
      cIn1,
      cIn2,
      cOut1,
      cOut2,
      nf1,
      nf2,
      {
        ...proof,
        in2Member: { ...proof.in2Member, directions: [!proof.in2Member.directions[0]] },
      }
    )).toBe(false);
  });

  it('rejects deterministic Merkle transaction proof mutations', async () => {
    const {
      sdk,
      params,
      gamma,
      k,
      ck,
      nk,
      root,
      spent,
      cIn1,
      cIn2,
      cOut1,
      cOut2,
      nf1,
      nf2,
      proof,
    } = await buildMerkleTransactionFixture();
    const verify = (candidate: typeof proof, candidateSpent = spent, candidateRoot = root.digest) =>
      sdk.ConfidentialTransaction.fsVerifyMerkle(
        params,
        gamma,
        k,
        ck,
        nk,
        candidateRoot,
        candidateSpent,
        cIn1,
        cIn2,
        cOut1,
        cOut2,
        nf1,
        nf2,
        candidate
      );
    const mutations = merkleTransactionProofMutations(proof, spent, root.digest, nf1);
    expect(mutations.length).toBeGreaterThanOrEqual(20);
    expect(new Set(mutations.map((mutation) => mutation.name)).size).toBe(mutations.length);
    for (const mutation of mutations) {
      const accepted = verify(mutation.proof, mutation.spent, mutation.root);
      if (accepted) {
        throw new Error(`accepted mutated Merkle transaction proof: ${mutation.name}`);
      }
      expect(accepted).toBe(false);
    }
  });
});
