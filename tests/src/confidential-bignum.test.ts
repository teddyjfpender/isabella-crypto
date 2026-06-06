import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';

const __filename = fileURLToPath(import.meta.url);
const __dirname = path.dirname(__filename);
const projectRoot = path.resolve(__dirname, '..', '..');
const vectorsPath = path.join(projectRoot, 'tests/fixtures/confidential-bignum-vectors.json');
const typeScriptEntry = path.join(projectRoot, 'isabella.ts/dist/index.mjs');

type ScalarCase = {
  name: string;
  decimal: string;
  encodedHex: string;
  digest: string;
};

type VectorCase = {
  name: string;
  decimals: string[];
  encodedHex: string;
  digest: string;
};

type BignumVectors = {
  version: number;
  dst: string;
  integerEncoding: string;
  vectorEncoding: string;
  scalarCases: ScalarCase[];
  vectorCases: VectorCase[];
  rejectedDecimals: string[];
};

describe('Confidential bignum codec vectors', () => {
  const vectors = JSON.parse(fs.readFileSync(vectorsPath, 'utf8')) as BignumVectors;

  it('pins the canonical bignum encoding with TypeScript bigint support', async () => {
    const sdk = await import(pathToFileURL(typeScriptEntry).href);

    expect(vectors.version).toBe(1);
    expect(sdk.ConfidentialBignum.dst).toBe(vectors.dst);
    expect(sdk.ConfidentialBignum.integerEncoding).toBe(vectors.integerEncoding);
    expect(sdk.ConfidentialBignum.vectorEncoding).toBe(vectors.vectorEncoding);

    for (const entry of vectors.scalarCases) {
      expect(sdk.ConfidentialBignum.encodeIntegerHex(entry.decimal)).toBe(entry.encodedHex);
      expect(sdk.ConfidentialBignum.digestInteger(entry.decimal)).toBe(entry.digest);
      expect(sdk.ConfidentialBignum.encodeIntegerHex(BigInt(entry.decimal))).toBe(entry.encodedHex);
    }

    for (const entry of vectors.vectorCases) {
      expect(sdk.ConfidentialBignum.encodeIntegerVectorHex(entry.decimals)).toBe(entry.encodedHex);
      expect(sdk.ConfidentialBignum.digestIntegerVector(entry.decimals)).toBe(entry.digest);
      expect(sdk.ConfidentialBignum.encodeIntegerVectorHex(entry.decimals.map(BigInt))).toBe(entry.encodedHex);
    }
  });

  it('rejects non-canonical decimal strings and unsafe numbers', async () => {
    const sdk = await import(pathToFileURL(typeScriptEntry).href);

    for (const decimal of vectors.rejectedDecimals) {
      expect(() => sdk.ConfidentialBignum.encodeIntegerHex(decimal)).toThrow();
    }

    expect(() => sdk.ConfidentialBignum.encodeIntegerHex(-0)).toThrow(RangeError);
    expect(() => sdk.ConfidentialBignum.encodeIntegerHex(Number.MAX_SAFE_INTEGER + 1)).toThrow(RangeError);
  });
});
