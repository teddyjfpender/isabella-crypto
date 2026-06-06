import fs from 'node:fs';
import path from 'node:path';
import { createHash } from 'node:crypto';
import { fileURLToPath, pathToFileURL } from 'node:url';

import { buildMerkleTransactionFixture } from './confidential-fixtures.ts';

const __filename = fileURLToPath(import.meta.url);
const __dirname = path.dirname(__filename);
const projectRoot = path.resolve(__dirname, '..', '..');
const vectorsPath = path.join(projectRoot, 'tests/fixtures/confidential-transaction-vectors.json');
const typeScriptEntry = path.join(projectRoot, 'isabella.ts/dist/index.mjs');

type TransactionContext = {
  protocolVersion: number;
  networkId: string;
  assetId: number;
  ledgerEpoch: number;
  root: { digest: string; depth: number };
  publicFee: number;
  cIn1: number[];
  cIn2: number[];
  cOut1: number[];
  cOut2: number[];
  nf1: number[];
  nf2: number[];
};

type TransactionVector = {
  name: string;
  context: TransactionContext;
  preimageHex: string;
  digest: string;
};

type DigestVector = {
  name: string;
  preimageHex: string;
  digest: string;
};

type EnvelopeVector = DigestVector & {
  context: TransactionContext;
  contextDigest: string;
  proofDigest: string;
};

type WalletProofRequest = {
  context: TransactionContext;
  acceptedRoots: Array<{ digest: string; depth: number }>;
  spentNullifiers: number[][];
};

type WalletProofRequestVector = DigestVector & {
  request: WalletProofRequest;
  contextDigest: string;
};

type TransactionVectors = {
  version: number;
  algorithm: string;
  dst: string;
  protocolId: string;
  integerEncoding: string;
  stringEncoding: string;
  digestEncoding: string;
  vectorEncoding: string;
  tags: { context: number; merkleProof: number; envelope: number; walletProofRequest: number };
  cases: TransactionVector[];
  merkleProofCases: DigestVector[];
  envelopeCases: EnvelopeVector[];
  walletProofRequestCases: WalletProofRequestVector[];
};

function sha3Hex(preimageHex: string): string {
  return createHash('sha3-256')
    .update(Buffer.from(preimageHex, 'hex'))
    .digest('hex');
}

function mutateDigest(digest: string): string {
  return digest.replace(/^./, digest[0] === '0' ? '1' : '0');
}

function rootKey(root: { digest: string; depth: number }): string {
  return `${root.digest}:${root.depth}`;
}

describe('Confidential transaction context vectors', () => {
  const vectors = JSON.parse(fs.readFileSync(vectorsPath, 'utf8')) as TransactionVectors;

  it('pins the canonical transaction context domain and encodings', () => {
    expect(vectors.algorithm).toBe('SHA3-256');
    expect(vectors.dst).toBe('ISABELLA-CT-TX-v1');
    expect(vectors.protocolId).toBe('ISABELLA-CT-SIS-NOTE');
    expect(vectors.integerEncoding).toBe('signed-64-bit-little-endian');
    expect(vectors.stringEncoding).toBe('len_i64_le || printable_ascii_bytes');
    expect(vectors.digestEncoding).toBe('len_i64_le || 32 raw digest bytes');
    expect(vectors.vectorEncoding).toBe('len_i64_le || values_i64_le...');
    expect(vectors.tags).toEqual({
      context: 0,
      merkleProof: 1,
      envelope: 2,
      walletProofRequest: 3,
    });
  });

  it('hashes every pinned transaction context preimage to the recorded digest', () => {
    for (const entry of vectors.cases) {
      expect(sha3Hex(entry.preimageHex)).toBe(entry.digest);
    }
  });

  it('hashes every pinned Merkle proof and envelope preimage to the recorded digest', () => {
    for (const entry of vectors.merkleProofCases) {
      expect(sha3Hex(entry.preimageHex)).toBe(entry.digest);
    }
    for (const entry of vectors.envelopeCases) {
      expect(sha3Hex(entry.preimageHex)).toBe(entry.digest);
    }
    for (const entry of vectors.walletProofRequestCases) {
      expect(sha3Hex(entry.preimageHex)).toBe(entry.digest);
    }
  });

  it('matches the TypeScript transaction context API', async () => {
    const sdk = await import(pathToFileURL(typeScriptEntry).href);
    const tx = sdk.ConfidentialTransaction;
    const [entry] = vectors.cases;

    expect(tx.transactionDst).toBe(vectors.dst);
    expect(tx.transactionProtocolId).toBe(vectors.protocolId);
    expect(tx.transactionTags).toEqual(vectors.tags);
    expect(tx.transactionContextPreimageHex(entry.context)).toBe(entry.preimageHex);
    expect(tx.transactionContextDigest(entry.context)).toBe(entry.digest);

    expect(tx.transactionContextDigest({ ...entry.context, publicFee: entry.context.publicFee + 1 }))
      .not.toBe(entry.digest);
    expect(tx.transactionContextDigest({ ...entry.context, networkId: 'isabella-mainnet' }))
      .not.toBe(entry.digest);
    expect(tx.transactionContextDigest({
      ...entry.context,
      root: {
        ...entry.context.root,
        digest: mutateDigest(entry.context.root.digest),
      },
    })).not.toBe(entry.digest);
    expect(tx.transactionContextDigest({
      ...entry.context,
      root: { ...entry.context.root, depth: entry.context.root.depth + 1 },
    })).not.toBe(entry.digest);
  });

  it('rejects malformed or non-canonical transaction context fields', async () => {
    const sdk = await import(pathToFileURL(typeScriptEntry).href);
    const tx = sdk.ConfidentialTransaction;
    const [entry] = vectors.cases;

    expect(() => tx.transactionContextDigest({ ...entry.context, publicFee: -1 })).toThrow();
    expect(() => tx.transactionContextDigest({ ...entry.context, publicFee: -0 })).toThrow();
    expect(() => tx.transactionContextDigest({ ...entry.context, assetId: Number.MAX_SAFE_INTEGER + 1 }))
      .toThrow();
    expect(() => tx.transactionContextDigest({ ...entry.context, networkId: 'isabella-\u2603' }))
      .toThrow();
    expect(() => tx.transactionContextDigest({
      ...entry.context,
      root: { ...entry.context.root, digest: entry.context.root.digest.toUpperCase() },
    }))
      .toThrow();
    expect(() => tx.transactionContextDigest({
      ...entry.context,
      root: { ...entry.context.root, depth: -1 },
    }))
      .toThrow();
  });

  it('matches the TypeScript Merkle proof and envelope serialization APIs', async () => {
    const {
      sdk,
      root,
      cIn1,
      cIn2,
      cOut1,
      cOut2,
      nf1,
      nf2,
      proof,
    } = await buildMerkleTransactionFixture();
    const tx = sdk.ConfidentialTransaction;
    const [proofVector] = vectors.merkleProofCases;
    const [envelopeVector] = vectors.envelopeCases;
    const context: TransactionContext = {
      protocolVersion: 1,
      networkId: 'isabella-local-devnet',
      assetId: 7,
      ledgerEpoch: 42,
      root,
      publicFee: 0,
      cIn1,
      cIn2,
      cOut1,
      cOut2,
      nf1,
      nf2,
    };
    const envelope = {
      context,
      contextDigest: tx.transactionContextDigest(context),
      proof,
    };

    expect(tx.transactionMerkleProofPreimageHex(proof)).toBe(proofVector.preimageHex);
    expect(tx.transactionMerkleProofDigest(proof)).toBe(proofVector.digest);
    expect(tx.transactionEnvelopePreimageHex(envelope)).toBe(envelopeVector.preimageHex);
    expect(tx.transactionEnvelopeDigest(envelope)).toBe(envelopeVector.digest);
    expect(envelope.contextDigest).toBe(envelopeVector.contextDigest);
    expect(tx.transactionMerkleProofDigest({ ...proof, in2Member: proof.in1Member }))
      .not.toBe(proofVector.digest);
    expect(tx.transactionEnvelopeDigest({
      context: { ...context, networkId: 'isabella-mainnet' },
      contextDigest: tx.transactionContextDigest({ ...context, networkId: 'isabella-mainnet' }),
      proof,
    })).not.toBe(envelopeVector.digest);
    expect(() => tx.transactionEnvelopeDigest({ ...envelope, contextDigest: proofVector.digest }))
      .toThrow();
  });

  it('matches the TypeScript wallet proof request serialization API', async () => {
    const sdk = await import(pathToFileURL(typeScriptEntry).href);
    const tx = sdk.ConfidentialTransaction;
    const [requestVector] = vectors.walletProofRequestCases;
    const request = requestVector.request;
    const mutableAcceptedRootIndex = request.acceptedRoots.findIndex(
      (root) => !root || rootKey(root) !== rootKey(request.context.root)
    );
    expect(mutableAcceptedRootIndex).toBeGreaterThanOrEqual(0);

    expect(tx.transactionWalletProofRequestPreimageHex(request)).toBe(requestVector.preimageHex);
    expect(tx.transactionWalletProofRequestDigest(request)).toBe(requestVector.digest);
    expect(tx.transactionContextDigest(request.context)).toBe(requestVector.contextDigest);
    expect(tx.transactionWalletProofRequestDigest({
      ...request,
      acceptedRoots: request.acceptedRoots.map((root, index) =>
        index === mutableAcceptedRootIndex
          ? { ...root, depth: root.depth + 1 }
          : root
      ).sort((left, right) => rootKey(left).localeCompare(rootKey(right))),
    })).not.toBe(requestVector.digest);
    expect(tx.transactionWalletProofRequestDigest({
      ...request,
      acceptedRoots: request.acceptedRoots.map((root, index) =>
        index === mutableAcceptedRootIndex
          ? { ...root, digest: mutateDigest(root.digest) }
          : root
      ).sort((left, right) => rootKey(left).localeCompare(rootKey(right))),
    })).not.toBe(requestVector.digest);
    expect(tx.transactionWalletProofRequestDigest({
      ...request,
      spentNullifiers: [...request.spentNullifiers, [99, 100, 101]],
    })).not.toBe(requestVector.digest);
    expect(tx.transactionWalletProofRequestDigest({
      ...request,
      context: { ...request.context, ledgerEpoch: request.context.ledgerEpoch + 1 },
    })).not.toBe(requestVector.digest);
  });

  it('rejects malformed or non-canonical wallet proof requests', async () => {
    const sdk = await import(pathToFileURL(typeScriptEntry).href);
    const tx = sdk.ConfidentialTransaction;
    const [requestVector] = vectors.walletProofRequestCases;
    const request = requestVector.request;
    const unsortedRoots = request.acceptedRoots.slice().reverse();
    const duplicateRoots = [request.acceptedRoots[0], request.acceptedRoots[0]];

    expect(() => tx.transactionWalletProofRequestDigest({
      ...request,
      acceptedRoots: [],
    })).toThrow();
    expect(() => tx.transactionWalletProofRequestDigest({
      ...request,
      acceptedRoots: request.acceptedRoots.filter((root) => rootKey(root) !== rootKey(request.context.root)),
    })).toThrow();
    expect(() => tx.transactionWalletProofRequestDigest({
      ...request,
      acceptedRoots: request.acceptedRoots.map((root) =>
        rootKey(root) === rootKey(request.context.root)
          ? { ...root, depth: root.depth + 1 }
          : root
      ).sort((left, right) => rootKey(left).localeCompare(rootKey(right))),
    })).toThrow();
    expect(() => tx.transactionWalletProofRequestDigest({
      ...request,
      acceptedRoots: duplicateRoots,
    })).toThrow();
    if (unsortedRoots.map(rootKey).join('|') !== request.acceptedRoots.map(rootKey).join('|')) {
      expect(() => tx.transactionWalletProofRequestDigest({
        ...request,
        acceptedRoots: unsortedRoots,
      })).toThrow();
    }
    expect(() => tx.transactionWalletProofRequestDigest({
      ...request,
      acceptedRoots: request.acceptedRoots.map((root, index) =>
        index === 0 ? { ...root, digest: `${root.digest.slice(0, -1)}A` } : root
      ),
    })).toThrow();
    expect(() => tx.transactionWalletProofRequestDigest({
      ...request,
      acceptedRoots: request.acceptedRoots.map((root, index) =>
        index === 0 ? { ...root, depth: -1 } : root
      ),
    })).toThrow();
    expect(() => tx.transactionWalletProofRequestDigest({
      ...request,
      spentNullifiers: request.spentNullifiers.slice().reverse(),
    })).toThrow();
    expect(() => tx.transactionWalletProofRequestDigest({
      ...request,
      spentNullifiers: [request.spentNullifiers[0], request.spentNullifiers[0]],
    })).toThrow();
    expect(() => tx.transactionWalletProofRequestDigest({
      ...request,
      spentNullifiers: [[Number.MAX_SAFE_INTEGER + 1]],
    })).toThrow();
    expect(() => tx.transactionWalletProofRequestDigest({
      ...request,
      spentNullifiers: [[-0]],
    })).toThrow();
    expect(() => tx.transactionWalletProofRequestDigest({
      ...request,
      spentNullifiers: [request.context.nf1],
    })).toThrow();
    expect(() => tx.transactionWalletProofRequestDigest({
      ...request,
      context: { ...request.context, nf2: request.context.nf1 },
    })).toThrow();
  });

  it('verifies Merkle transaction envelopes only under the expected public context', async () => {
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
    const tx = sdk.ConfidentialTransaction;
    const context: TransactionContext = {
      protocolVersion: 1,
      networkId: 'isabella-local-devnet',
      assetId: 7,
      ledgerEpoch: 42,
      root,
      publicFee: 0,
      cIn1,
      cIn2,
      cOut1,
      cOut2,
      nf1,
      nf2,
    };
    const policy = {
      networkId: context.networkId,
      assetId: context.assetId,
      ledgerEpoch: context.ledgerEpoch,
      root: context.root,
      publicFee: 0,
    };
    const envelope = {
      context,
      contextDigest: tx.transactionContextDigest(context),
      proof,
    };

    expect(tx.fsVerifyMerkleEnvelope(params, gamma, k, ck, nk, spent, envelope, policy))
      .toBe(true);
    expect(tx.fsVerifyMerkleEnvelope(
      params,
      gamma,
      k,
      ck,
      nk,
      spent,
      { ...envelope, contextDigest: envelope.contextDigest.replace(/^./, '0') },
      policy
    )).toBe(false);
    expect(tx.fsVerifyMerkleEnvelope(
      params,
      gamma,
      k,
      ck,
      nk,
      spent,
      {
        ...envelope,
        context: { ...context, networkId: 'isabella-mainnet' },
        contextDigest: tx.transactionContextDigest({ ...context, networkId: 'isabella-mainnet' }),
      },
      policy
    )).toBe(false);
    expect(tx.fsVerifyMerkleEnvelope(
      params,
      gamma,
      k,
      ck,
      nk,
      spent,
      envelope,
      { ...policy, assetId: policy.assetId + 1 }
    )).toBe(false);
    expect(tx.fsVerifyMerkleEnvelope(
      params,
      gamma,
      k,
      ck,
      nk,
      spent,
      {
        ...envelope,
        context: { ...context, publicFee: 1 },
        contextDigest: tx.transactionContextDigest({ ...context, publicFee: 1 }),
      },
      { ...policy, publicFee: 1 }
    )).toBe(false);

    const feeFixture = await buildMerkleTransactionFixture({ publicFee: 1 });
    const feeContext: TransactionContext = {
      protocolVersion: 1,
      networkId: 'isabella-local-devnet',
      assetId: 7,
      ledgerEpoch: 42,
      root: feeFixture.root,
      publicFee: 1,
      cIn1: feeFixture.cIn1,
      cIn2: feeFixture.cIn2,
      cOut1: feeFixture.cOut1,
      cOut2: feeFixture.cOut2,
      nf1: feeFixture.nf1,
      nf2: feeFixture.nf2,
    };
    const feePolicy = {
      networkId: feeContext.networkId,
      assetId: feeContext.assetId,
      ledgerEpoch: feeContext.ledgerEpoch,
      root: feeContext.root,
      publicFee: 1,
    };
    const feeEnvelope = {
      context: feeContext,
      contextDigest: tx.transactionContextDigest(feeContext),
      proof: feeFixture.proof,
    };
    expect(tx.fsVerifyMerkleEnvelope(
      feeFixture.params,
      feeFixture.gamma,
      feeFixture.k,
      feeFixture.ck,
      feeFixture.nk,
      feeFixture.spent,
      feeEnvelope,
      feePolicy
    )).toBe(true);
    expect(tx.fsVerifyMerkleEnvelope(
      feeFixture.params,
      feeFixture.gamma,
      feeFixture.k,
      feeFixture.ck,
      feeFixture.nk,
      feeFixture.spent,
      feeEnvelope,
      { ...feePolicy, publicFee: 0 }
    )).toBe(false);
    expect(tx.fsVerifyMerkleEnvelope(
      params,
      gamma,
      k,
      ck,
      nk,
      spent,
      {
        ...envelope,
        proof: { ...proof, in2Member: proof.in1Member },
      },
      policy
    )).toBe(false);
    const wrongDepthContext = {
      ...context,
      root: { ...context.root, depth: context.root.depth + 1 },
    };
    expect(tx.fsVerifyMerkleEnvelope(
      params,
      gamma,
      k,
      ck,
      nk,
      spent,
      {
        ...envelope,
        context: wrongDepthContext,
        contextDigest: tx.transactionContextDigest(wrongDepthContext),
      },
      { ...policy, root: wrongDepthContext.root }
    )).toBe(false);
    expect(tx.fsVerifyMerkleEnvelope(
      params,
      gamma,
      k,
      ck,
      nk,
      spent,
      envelope,
      { ...policy, root: { ...policy.root, depth: policy.root.depth + 1 } }
    )).toBe(false);
  });
});
