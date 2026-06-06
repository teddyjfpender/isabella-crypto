import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';

const __filename = fileURLToPath(import.meta.url);
const __dirname = path.dirname(__filename);
const projectRoot = path.resolve(__dirname, '..', '..');
const vectorsPath = path.join(projectRoot, 'tests/fixtures/confidential-bignum-transaction-vectors.json');
const typeScriptEntry = path.join(projectRoot, 'isabella.ts/dist/index.mjs');

type BignumTransactionVectors = {
  version: number;
  algorithm: string;
  status: string;
  merkle: {
    dst: string;
    integerEncoding: string;
    digestEncoding: string;
    tags: Record<string, number>;
  };
  transaction: {
    dst: string;
    protocolId: string;
    integerEncoding: string;
    digestEncoding: string;
    tags: Record<string, number>;
  };
  ledger: string[][];
  merkleCases: Array<{
    name: string;
    commitment?: string[];
    commitments?: string[][];
    preimageHex?: string;
    digest: string;
  }>;
  contextCases: Array<{
    name: string;
    context: Record<string, any>;
    preimageHex: string;
    digest: string;
  }>;
  merkleProofCases: Array<{
    name: string;
    proof: Record<string, any>;
    preimageHex: string;
    digest: string;
  }>;
  envelopeCases: Array<{
    name: string;
    envelope: Record<string, any>;
    preimageHex: string;
    digest: string;
  }>;
  acceptedRootWindowCases: Array<{
    name: string;
    window: Record<string, any>;
    preimageHex: string;
    digest: string;
  }>;
  walletProofRequestCases: Array<{
    name: string;
    request: Record<string, any>;
    preimageHex: string;
    digest: string;
    contextDigest: string;
  }>;
};

function mutateDigest(digest: string): string {
  const replacement = digest[0] === '0' ? '1' : '0';
  return `${replacement}${digest.slice(1)}`;
}

function rootKey(root: { digest: string; depth: number }): string {
  return `${root.digest}:${root.depth}`;
}

describe('Confidential bignum transaction namespace vectors', () => {
  const vectors = JSON.parse(fs.readFileSync(vectorsPath, 'utf8')) as BignumTransactionVectors;

  it('pins the bignum Merkle namespace and q83 leaf/root vectors', async () => {
    const sdk = await import(pathToFileURL(typeScriptEntry).href);
    const merkle = sdk.ConfidentialMerkleBigInt;
    const legacyMerkle = sdk.ConfidentialMerkle;
    const [leafCase, rootCase] = vectors.merkleCases;

    expect(vectors.version).toBe(1);
    expect(vectors.algorithm).toBe('SHA3-256');
    expect(vectors.status).toBe('typescript-bignum-transaction-namespace-preview');
    expect(merkle.dst).toBe(vectors.merkle.dst);
    expect(merkle.integerEncoding).toBe(vectors.merkle.integerEncoding);
    expect(merkle.digestEncoding).toBe(vectors.merkle.digestEncoding);
    expect(merkle.tags).toEqual(vectors.merkle.tags);

    expect(merkle.encodeLeaf(leafCase.commitment)).toBe(leafCase.preimageHex);
    expect(merkle.leaf(leafCase.commitment)).toBe(leafCase.digest);
    expect(merkle.root(rootCase.commitments)).toBe(rootCase.digest);
    expect(() => legacyMerkle.leaf(leafCase.commitment.map((value) => Number(value)))).toThrow();
    expect(() => merkle.leaf(['00', ...leafCase.commitment!.slice(1)])).toThrow();

    const proof = merkle.membershipProve(vectors.ledger, vectors.ledger[1]);
    expect(proof).not.toBeNull();
    expect(proof!.root).toBe(rootCase.digest);
    expect(merkle.membershipVerify(vectors.ledger[1], proof!)).toBe(true);
    expect(merkle.membershipVerify([`${BigInt(vectors.ledger[1][0]) + 1n}`, vectors.ledger[1][1]], proof!))
      .toBe(false);
  });

  it('pins bignum transaction context, proof, and envelope digests', async () => {
    const sdk = await import(pathToFileURL(typeScriptEntry).href);
    const tx = sdk.ConfidentialTransactionBigInt;
    const legacyTx = sdk.ConfidentialTransaction;
    const [contextVector] = vectors.contextCases;
    const [proofVector] = vectors.merkleProofCases;
    const [envelopeVector] = vectors.envelopeCases;

    expect(tx.transactionDst).toBe(vectors.transaction.dst);
    expect(tx.transactionProtocolId).toBe(vectors.transaction.protocolId);
    expect(tx.transactionTags).toEqual(vectors.transaction.tags);
    expect(tx.integerEncoding).toBe(vectors.transaction.integerEncoding);
    expect(tx.digestEncoding).toBe(vectors.transaction.digestEncoding);

    expect(tx.transactionContextPreimageHex(contextVector.context)).toBe(contextVector.preimageHex);
    expect(tx.transactionContextDigest(contextVector.context)).toBe(contextVector.digest);
    expect(tx.transactionMerkleProofPreimageHex(proofVector.proof)).toBe(proofVector.preimageHex);
    expect(tx.transactionMerkleProofDigest(proofVector.proof)).toBe(proofVector.digest);
    expect(tx.transactionEnvelopePreimageHex(envelopeVector.envelope)).toBe(envelopeVector.preimageHex);
    expect(tx.transactionEnvelopeDigest(envelopeVector.envelope)).toBe(envelopeVector.digest);
    expect(legacyTx.transactionContextDigest({
      ...contextVector.context,
      publicFee: 0,
      cIn1: [1, 2],
      cIn2: [3, 4],
      cOut1: [5, 6],
      cOut2: [7, 8],
      nf1: [9, 10],
      nf2: [11, 12],
    })).not.toBe(contextVector.digest);

    expect(tx.transactionContextDigest({
      ...contextVector.context,
      publicFee: `${BigInt(contextVector.context.publicFee) - 1n}`,
    })).not.toBe(contextVector.digest);
    expect(tx.transactionMerkleProofDigest({
      ...proofVector.proof,
      in2Member: proofVector.proof.in1Member,
    })).not.toBe(proofVector.digest);
    expect(tx.transactionEnvelopeDigest({
      ...envelopeVector.envelope,
      context: {
        ...envelopeVector.envelope.context,
        networkId: 'isabella-mainnet',
      },
      contextDigest: tx.transactionContextDigest({
        ...envelopeVector.envelope.context,
        networkId: 'isabella-mainnet',
      }),
    })).not.toBe(envelopeVector.digest);
    expect(() => tx.transactionEnvelopeDigest({
      ...envelopeVector.envelope,
      contextDigest: proofVector.digest,
    })).toThrow();
  });

  it('rejects malformed bignum transaction fields', async () => {
    const sdk = await import(pathToFileURL(typeScriptEntry).href);
    const tx = sdk.ConfidentialTransactionBigInt;
    const [contextVector] = vectors.contextCases;
    const [proofVector] = vectors.merkleProofCases;

    expect(() => tx.transactionContextDigest({ ...contextVector.context, publicFee: '+1' })).toThrow();
    expect(() => tx.transactionContextDigest({ ...contextVector.context, publicFee: -0 })).toThrow();
    expect(() => tx.transactionContextDigest({
      ...contextVector.context,
      publicFee: Number.MAX_SAFE_INTEGER + 1,
    })).toThrow();
    expect(() => tx.transactionContextDigest({
      ...contextVector.context,
      cIn1: ['00', ...contextVector.context.cIn1.slice(1)],
    })).toThrow();
    expect(() => tx.transactionContextDigest({ ...contextVector.context, extension: 1 })).toThrow();
    expect(() => tx.transactionMerkleProofDigest({
      ...proofVector.proof,
      balance: { ...proofVector.proof.balance, extension: 1 },
    })).toThrow();
    expect(() => tx.transactionMerkleProofDigest({
      ...proofVector.proof,
      out1Range: { ...proofVector.proof.out1Range, extension: 1 },
    })).toThrow();
  });

  it('pins bignum accepted-root window and wallet request digests', async () => {
    const sdk = await import(pathToFileURL(typeScriptEntry).href);
    const tx = sdk.ConfidentialTransactionBigInt;
    const [windowVector] = vectors.acceptedRootWindowCases;
    const [requestVector] = vectors.walletProofRequestCases;
    const window = windowVector.window;
    const request = requestVector.request;
    const mutableAcceptedRootIndex = request.acceptedRoots.findIndex(
      (root: { digest: string; depth: number }) => rootKey(root) !== rootKey(request.context.root)
    );

    expect(tx.transactionAcceptedRootWindowPreimageHex(window)).toBe(windowVector.preimageHex);
    expect(tx.transactionAcceptedRootWindowDigest(window)).toBe(windowVector.digest);
    expect(tx.transactionAcceptedRootWindowRoots(window)).toEqual(request.acceptedRoots);
    expect(tx.transactionContextMatchesAcceptedRootWindow(request.context, window)).toBe(true);
    expect(tx.transactionWalletProofRequestFromWindow(
      request.context,
      window,
      request.spentNullifiers
    )).toEqual(request);
    expect(tx.transactionWalletProofRequestPreimageHex(request)).toBe(requestVector.preimageHex);
    expect(tx.transactionWalletProofRequestDigest(request)).toBe(requestVector.digest);
    expect(tx.transactionContextDigest(request.context)).toBe(requestVector.contextDigest);

    expect(mutableAcceptedRootIndex).toBeGreaterThanOrEqual(0);
    expect(tx.transactionWalletProofRequestDigest({
      ...request,
      acceptedRoots: request.acceptedRoots.map((root: { digest: string; depth: number }, index: number) =>
        index === mutableAcceptedRootIndex
          ? { ...root, digest: mutateDigest(root.digest) }
          : root
      ).sort((left: { digest: string; depth: number }, right: { digest: string; depth: number }) =>
        rootKey(left).localeCompare(rootKey(right))
      ),
    })).not.toBe(requestVector.digest);
    expect(() => tx.transactionWalletProofRequestDigest({
      ...request,
      spentNullifiers: [...request.spentNullifiers, request.context.nf1],
    })).toThrow();
    expect(() => tx.transactionAcceptedRootWindowDigest({
      ...window,
      roots: [window.roots[0], window.roots[0]],
    })).toThrow();
  });
});
