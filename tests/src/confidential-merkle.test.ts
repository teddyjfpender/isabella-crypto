import fs from 'node:fs';
import path from 'node:path';
import { createHash } from 'node:crypto';
import { fileURLToPath, pathToFileURL } from 'node:url';

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
    const sdk = await import(pathToFileURL(typeScriptEntry).href);
    const params = sdk.ConfidentialBalance.makeParams(2, 2, 17, 6);
    const ck = [
      [1, 0, 0],
      [0, 1, 0],
    ];
    const nk = [
      [0, 1, 0],
      [1, 0, 0],
    ];
    const gamma = 5;
    const k = 1;
    const rounds = sdk.ConfidentialBalance.fsRounds();
    const opIn1 = { msg: [1], rand: [1, 0] };
    const opIn2 = { msg: [1], rand: [0, 1] };
    const opOut1 = { msg: [1], rand: [1, 1] };
    const opOut2 = { msg: [1], rand: [0, 0] };
    const bit1 = [{ msg: [1], rand: [1, 1] }];
    const comp1 = [{ msg: [0], rand: [0, 0] }];
    const bit2 = [{ msg: [1], rand: [0, 0] }];
    const comp2 = [{ msg: [0], rand: [0, 0] }];
    const yIn1 = Array.from({ length: rounds }, () => ({ msg: [0], rand: [1, 0] }));
    const yIn2 = Array.from({ length: rounds }, () => ({ msg: [1], rand: [0, 1] }));
    const yBalance = Array.from({ length: rounds }, () => [0, 1]);
    const yOut1 = Array.from({ length: rounds }, () => [0, 1]);
    const yOut1Pairs = Array.from({ length: rounds }, () => [[0, 0]]);
    const yOut2 = Array.from({ length: rounds }, () => [1, 0]);
    const yOut2Pairs = Array.from({ length: rounds }, () => [[0, 0]]);
    const commitOf = (opening: { msg: number[]; rand: number[] }) =>
      sdk.Zq.matVecMultMod(ck, sdk.Vec.concat(opening.msg, opening.rand), params.q);
    const cIn1 = commitOf(opIn1);
    const cIn2 = commitOf(opIn2);
    const cOut1 = commitOf(opOut1);
    const cOut2 = commitOf(opOut2);
    const nf1 = sdk.ConfidentialTransaction.nullifier(params, nk, opIn1);
    const nf2 = sdk.ConfidentialTransaction.nullifier(params, nk, opIn2);
    const ledger = [cIn1, cIn2];
    const spent: number[][] = [];

    const proof = sdk.ConfidentialTransaction.fsProveMerkle(
      params,
      gamma,
      k,
      ck,
      nk,
      ledger,
      spent,
      cIn1,
      cIn2,
      cOut1,
      cOut2,
      nf1,
      nf2,
      opIn1,
      opIn2,
      opOut1,
      opOut2,
      bit1,
      comp1,
      bit2,
      comp2,
      yIn1,
      yIn2,
      yBalance,
      yOut1,
      yOut1Pairs,
      yOut2,
      yOut2Pairs
    );
    expect(proof).not.toBeNull();

    const root = sdk.ConfidentialTransaction.merkleLedgerRoot(ledger);
    expect(root).toBe(sdk.ConfidentialMerkle.root(ledger));
    expect(sdk.ConfidentialTransaction.fsVerifyMerkle(
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
      proof!
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
      proof!
    )).toBe(false);
    expect(sdk.ConfidentialTransaction.fsVerifyMerkle(
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
      {
        ...proof!,
        in2Member: { ...proof!.in2Member, directions: [!proof!.in2Member.directions[0]] },
      }
    )).toBe(false);
  });
});
