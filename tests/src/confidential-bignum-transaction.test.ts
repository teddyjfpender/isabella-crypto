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

function makeOpening(amount: bigint, r0: bigint, r1: bigint) {
  return { msg: [amount], rand: [r0, r1] };
}

function bitOpenings(amount: bigint, bits: number) {
  return Array.from({ length: bits }, (_, bit) =>
    makeOpening((amount >> BigInt(bit)) & 1n, BigInt((bit % 3) - 1), BigInt(1 - (bit % 3)))
  );
}

function compOpenings(bits: ReturnType<typeof bitOpenings>) {
  return bits.map((opening, index) =>
    makeOpening(1n - opening.msg[0], BigInt(1 - (index % 2)), BigInt((index % 2) - 1))
  );
}

function openingMasks(rounds: number) {
  return Array.from({ length: rounds }, (_, round) =>
    makeOpening(BigInt((round % 5) - 2), BigInt((round % 7) - 3), BigInt(3 - (round % 7)))
  );
}

function vectorMasks(rounds: number) {
  return Array.from({ length: rounds }, (_, round) => [
    BigInt((round % 7) - 3),
    BigInt(3 - (round % 7)),
  ]);
}

function pairMasks(rounds: number, bits: number) {
  return Array.from({ length: rounds }, (_, round) =>
    Array.from({ length: bits }, (_, bit) => [
      BigInt(((round + bit) % 7) - 3),
      BigInt(3 - ((round + bit) % 7)),
    ])
  );
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
    expect(vectors.status).toBe('native-bignum-transaction-namespace-preview');
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

  it('composes a BigInt Merkle transaction proof and verifies its envelope policy', async () => {
    const sdk = await import(pathToFileURL(typeScriptEntry).href);
    const tx = sdk.ConfidentialTransactionBigInt;
    const balance = sdk.ConfidentialBalanceBigInt;
    const nullifier = sdk.ConfidentialNullifierBigInt;
    const params = balance.makeParams(2, 2, '4835703278458516765933661', 16n);
    const gamma = 32n;
    const k = 4;
    const rounds = balance.fsRounds();
    const fee = 1n;
    const ck = [
      [3n, 5n, 7n],
      [11n, 13n, 17n],
    ];
    const nk = [
      [19n, 23n, 29n],
      [31n, 37n, 41n],
    ];
    const opIn1 = makeOpening(9n, 1n, -2n);
    const opIn2 = makeOpening(7n, -1n, 3n);
    const opOut1 = makeOpening(10n, 2n, -1n);
    const opOut2 = makeOpening(5n, -3n, 1n);
    const cIn1 = nullifier.nullifier(params, ck, opIn1);
    const cIn2 = nullifier.nullifier(params, ck, opIn2);
    const cOut1 = nullifier.nullifier(params, ck, opOut1);
    const cOut2 = nullifier.nullifier(params, ck, opOut2);
    const nf1 = nullifier.nullifier(params, nk, opIn1);
    const nf2 = nullifier.nullifier(params, nk, opIn2);
    const out1Bits = bitOpenings(opOut1.msg[0], k);
    const out1Comps = compOpenings(out1Bits);
    const out2Bits = bitOpenings(opOut2.msg[0], k);
    const out2Comps = compOpenings(out2Bits);
    const ledger = [cIn1, cIn2, cOut1, cOut2];
    const spent: bigint[][] = [];
    const proof = tx.fsProveMerkleWithFee(
      params,
      gamma,
      k,
      ck,
      nk,
      ledger,
      spent,
      fee,
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
      out1Bits,
      out1Comps,
      out2Bits,
      out2Comps,
      openingMasks(rounds),
      openingMasks(rounds),
      vectorMasks(rounds),
      vectorMasks(rounds),
      pairMasks(rounds, k),
      vectorMasks(rounds),
      pairMasks(rounds, k)
    );
    expect(proof).not.toBeNull();

    const root = tx.merkleLedgerRoot(ledger);
    expect(tx.fsVerifyMerkleWithFee(
      params,
      gamma,
      k,
      ck,
      nk,
      root,
      spent,
      fee,
      cIn1,
      cIn2,
      cOut1,
      cOut2,
      nf1,
      nf2,
      proof!
    )).toBe(true);
    expect(tx.fsVerifyMerkleWithFee(
      params,
      gamma,
      k,
      ck,
      nk,
      root,
      [nf1],
      fee,
      cIn1,
      cIn2,
      cOut1,
      cOut2,
      nf1,
      nf2,
      proof!
    )).toBe(false);
    expect(tx.fsProveMerkleWithFee(
      params,
      gamma,
      k,
      ck,
      nk,
      ledger,
      [nf1],
      fee,
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
      out1Bits,
      out1Comps,
      out2Bits,
      out2Comps,
      openingMasks(rounds),
      openingMasks(rounds),
      vectorMasks(rounds),
      vectorMasks(rounds),
      pairMasks(rounds, k),
      vectorMasks(rounds),
      pairMasks(rounds, k)
    )).toBeNull();

    const context = {
      protocolVersion: 1,
      networkId: 'isabella-devnet',
      assetId: 7,
      ledgerEpoch: 42,
      root: { digest: root, depth: proof!.in1Member.siblings.length },
      publicFee: fee,
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
      proof: proof!,
    };
    const policy = {
      protocolVersion: 1,
      networkId: 'isabella-devnet',
      assetId: 7,
      ledgerEpoch: 42,
      root: context.root,
      publicFee: fee,
    };
    expect(tx.transactionContextPolicyIsComplete(policy)).toBe(true);
    expect(tx.transactionContextMatchesPolicy(context, policy)).toBe(true);
    expect(tx.transactionEnvelopeDigest(envelope)).toMatch(/^[0-9a-f]{64}$/);
    expect(tx.fsVerifyMerkleEnvelope(params, gamma, k, ck, nk, spent, envelope, policy)).toBe(true);
    expect(tx.fsVerifyMerkleEnvelope(
      params,
      gamma,
      k,
      ck,
      nk,
      spent,
      { ...envelope, contextDigest: mutateDigest(envelope.contextDigest) },
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
      { ...policy, publicFee: fee + 1n }
    )).toBe(false);
  });
});
