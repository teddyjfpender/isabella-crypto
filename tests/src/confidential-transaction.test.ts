import fs from 'node:fs';
import path from 'node:path';
import { createHash } from 'node:crypto';
import { fileURLToPath, pathToFileURL } from 'node:url';

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
  root: string;
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

type TransactionVectors = {
  version: number;
  algorithm: string;
  dst: string;
  protocolId: string;
  integerEncoding: string;
  stringEncoding: string;
  digestEncoding: string;
  vectorEncoding: string;
  tags: { context: number };
  cases: TransactionVector[];
};

function sha3Hex(preimageHex: string): string {
  return createHash('sha3-256')
    .update(Buffer.from(preimageHex, 'hex'))
    .digest('hex');
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
    expect(vectors.tags).toEqual({ context: 0 });
  });

  it('hashes every pinned transaction context preimage to the recorded digest', () => {
    for (const entry of vectors.cases) {
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
      root: entry.context.root.replace(/^./, entry.context.root[0] === '0' ? '1' : '0'),
    })).not.toBe(entry.digest);
  });

  it('rejects malformed or non-canonical transaction context fields', async () => {
    const sdk = await import(pathToFileURL(typeScriptEntry).href);
    const tx = sdk.ConfidentialTransaction;
    const [entry] = vectors.cases;

    expect(() => tx.transactionContextDigest({ ...entry.context, publicFee: -1 })).toThrow();
    expect(() => tx.transactionContextDigest({ ...entry.context, assetId: Number.MAX_SAFE_INTEGER + 1 }))
      .toThrow();
    expect(() => tx.transactionContextDigest({ ...entry.context, networkId: 'isabella-\u2603' }))
      .toThrow();
    expect(() => tx.transactionContextDigest({ ...entry.context, root: entry.context.root.toUpperCase() }))
      .toThrow();
  });
});
