import fs from 'node:fs';
import path from 'node:path';
import { createHash } from 'node:crypto';
import { fileURLToPath, pathToFileURL } from 'node:url';

const __filename = fileURLToPath(import.meta.url);
const __dirname = path.dirname(__filename);
const projectRoot = path.resolve(__dirname, '..', '..');
const vectorsPath = path.join(projectRoot, 'tests/fixtures/confidential-transcript-vectors.json');
const typeScriptEntry = path.join(projectRoot, 'isabella.ts/dist/index.mjs');

type TranscriptRound = {
  round: number;
  digest: string;
  challenge: number;
};

type TranscriptCase = {
  name: string;
  domain: number;
  fields: number[];
  rounds: TranscriptRound[];
  ck?: number[][];
  c?: number[];
  as?: number[][];
  nk?: number[][];
  nf?: number[];
  aCommit?: number[];
  aNullifier?: number[];
  cAmount?: number[];
  cBits?: number[][];
  cComps?: number[][];
  aAmounts?: number[][];
  aPairss?: number[][][];
};

type TranscriptVectors = {
  version: number;
  algorithm: string;
  dst: string;
  integerEncoding: string;
  transcriptLayout: string;
  cases: TranscriptCase[];
};

function i64le(value: number): Buffer {
  const out = Buffer.alloc(8);
  out.writeBigInt64LE(BigInt(value), 0);
  return out;
}

function encodeTranscript(dst: string, domain: number, round: number, fields: number[]): Buffer {
  return Buffer.concat([
    Buffer.from(dst, 'ascii'),
    i64le(domain),
    i64le(round),
    i64le(fields.length),
    ...fields.map(i64le),
  ]);
}

function digestHex(dst: string, domain: number, round: number, fields: number[]): string {
  return createHash('sha3-256')
    .update(encodeTranscript(dst, domain, round, fields))
    .digest('hex');
}

function caseByName(vectors: TranscriptVectors, name: string): TranscriptCase {
  const found = vectors.cases.find((entry) => entry.name === name);
  if (found === undefined) {
    throw new Error(`missing transcript vector: ${name}`);
  }
  return found;
}

describe('Confidential Fiat-Shamir transcript vectors', () => {
  const vectors = JSON.parse(fs.readFileSync(vectorsPath, 'utf8')) as TranscriptVectors;

  it('pins the canonical SHA3 transcript encoding', () => {
    expect(vectors.algorithm).toBe('SHA3-256-counter-mode-low-bit');
    expect(vectors.dst).toBe('ISABELLA-CT-FS-v1');
    expect(vectors.integerEncoding).toBe('signed-64-bit-little-endian');

    for (const entry of vectors.cases) {
      for (const round of entry.rounds) {
        const digest = digestHex(vectors.dst, entry.domain, round.round, entry.fields);
        expect(digest).toBe(round.digest);
        expect(Number.parseInt(digest.slice(0, 2), 16) & 1).toBe(round.challenge);
      }
    }
  });

  it('matches balance, range, and nullifier runtime challenge APIs', async () => {
    const sdk = await import(pathToFileURL(typeScriptEntry).href);
    const params = sdk.ConfidentialBalance.makeParams(2, 2, 17, 6);

    const balance = caseByName(vectors, 'balance-basic');
    expect(sdk.ConfidentialBalance.fsChallenges(params, balance.ck!, balance.c!, balance.as!).slice(0, 4)).toEqual(
      balance.rounds.map((round) => round.challenge)
    );

    const range = caseByName(vectors, 'range-basic');
    expect(
      sdk.ConfidentialRange.canonicalChallenge(
        params,
        range.ck!,
        range.cAmount!,
        range.cBits!,
        range.cComps!,
        range.aAmounts!,
        range.aPairss!
      )
    ).toBe(range.rounds[0].challenge);

    const nullifier = caseByName(vectors, 'nullifier-canonical-basic');
    expect(
      sdk.ConfidentialTransaction.canonicalNullifierChallenge(
        params,
        nullifier.ck!,
        nullifier.nk!,
        nullifier.c!,
        nullifier.nf!,
        nullifier.aCommit!,
        nullifier.aNullifier!
      )
    ).toBe(nullifier.rounds[0].challenge);
  });
});
