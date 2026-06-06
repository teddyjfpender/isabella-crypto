import { describe, expect, it } from 'bun:test';
import { createHash } from 'node:crypto';
import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';

const __filename = fileURLToPath(import.meta.url);
const __dirname = path.dirname(__filename);
const projectRoot = path.join(__dirname, '..', '..');
const typeScriptEntry = process.env.ISABELLA_TS_ENTRY
  ? path.resolve(process.env.ISABELLA_TS_ENTRY)
  : path.join(projectRoot, 'isabella.ts', 'dist', 'index.mjs');
const vectorsPath = path.join(projectRoot, 'tests/fixtures/confidential-bigint-range-vectors.json');

type DecimalOpening = { msg: string[]; rand: string[] };
type RangeFixture = {
  version: number;
  algorithm: string;
  status: string;
  params: { m: number; n2: number; q: string; beta: string; gamma: string; k: number };
  bounds: {
    amountWitnessBound: string;
    amountResponseBoundChallenge1: string;
    pairResponseBoundChallenge1: string;
  };
  maskPolicy: {
    amountMask: string;
    pairMask: string;
  };
  transcript: {
    dst: string;
    domain: number;
    fieldEncoding: string;
    rounds: number;
    fields: string[];
    firstRounds: Array<{ round: number; challenge: number }>;
  };
  proofCommitment: {
    hash: string;
    digest: string;
    canonicalJsonBytes: number;
    amountRows: number;
    pairRounds: number;
    pairRowsPerRound: number;
    sample: {
      firstAmountAnnouncement: string[];
      firstAmountResponse: string[];
      firstPairAnnouncement: string[];
      firstPairResponse: string[];
    };
  };
  case: {
    name: string;
    commitmentKey: string[][];
    amount: string;
    amountOpening: DecimalOpening;
    amountCommitment: string[];
    bitOpenings: DecimalOpening[];
    compOpenings: DecimalOpening[];
  };
};

const vectors = JSON.parse(fs.readFileSync(vectorsPath, 'utf8')) as RangeFixture;

function bigintVec(values: string[]): bigint[] {
  return values.map(BigInt);
}

function bigintMat(rows: string[][]): bigint[][] {
  return rows.map(bigintVec);
}

function opening(openingJson: DecimalOpening) {
  return {
    msg: bigintVec(openingJson.msg),
    rand: bigintVec(openingJson.rand),
  };
}

function decimalize(value: unknown): unknown {
  if (typeof value === 'bigint') {
    return value.toString();
  }
  if (Array.isArray(value)) {
    return value.map(decimalize);
  }
  if (value && typeof value === 'object') {
    return Object.fromEntries(Object.entries(value).map(([key, item]) => [key, decimalize(item)]));
  }
  return value;
}

function proofDigest(proof: unknown): { digest: string; bytes: number } {
  const canonical = JSON.stringify(decimalize(proof));
  return {
    digest: createHash('sha3-256').update(canonical).digest('hex'),
    bytes: Buffer.byteLength(canonical, 'utf8'),
  };
}

function amountMask(round: number): bigint[] {
  return [
    BigInt((round + 1) % 11) - 5n,
    4n - BigInt((round * 3 + 1) % 9),
  ];
}

function pairMask(round: number, bit: number): bigint[] {
  return [
    BigInt((round + bit + 7) % 11) - 5n,
    4n - BigInt((round * 3 + bit + 7) % 9),
  ];
}

describe('Confidential range BigInt vectors', () => {
  it('pins a q83 64-bit TypeScript BigInt range proof path', async () => {
    const sdk = await import(pathToFileURL(typeScriptEntry).href);
    expect(vectors.version).toBe(1);
    expect(vectors.algorithm).toBe('SHA3-256-counter-mode-low-bit');
    expect(vectors.status).toBe('typescript-reference-with-native-preview-parity');
    expect(vectors.transcript.dst).toBe('ISABELLA-CT-FS-v1');
    expect(vectors.transcript.domain).toBe(2001);
    expect(vectors.params.k).toBe(64);
    expect(vectors.maskPolicy.amountMask).toContain('round + 1');
    expect(vectors.maskPolicy.pairMask).toContain('round + bit + 7');

    const params = sdk.ConfidentialBalanceBigInt.makeParams(
      vectors.params.m,
      vectors.params.n2,
      vectors.params.q,
      vectors.params.beta
    );
    const gamma = BigInt(vectors.params.gamma);
    const ck = bigintMat(vectors.case.commitmentKey);
    const amountCommitment = bigintVec(vectors.case.amountCommitment);
    const amountOpening = opening(vectors.case.amountOpening);
    const bitOpenings = vectors.case.bitOpenings.map(opening);
    const compOpenings = vectors.case.compOpenings.map(opening);
    const amountMasks = Array.from({ length: sdk.ConfidentialRangeBigInt.fsRounds() }, (_, round) =>
      amountMask(round)
    );
    const pairMasks = Array.from({ length: sdk.ConfidentialRangeBigInt.fsRounds() }, (_, round) =>
      Array.from({ length: vectors.params.k }, (_, bit) => pairMask(round, bit))
    );
    const generatedProof = sdk.ConfidentialRangeBigInt.fsProve(
      params,
      gamma,
      vectors.params.k,
      ck,
      amountCommitment,
      amountOpening,
      bitOpenings,
      compOpenings,
      amountMasks,
      pairMasks
    );
    expect(generatedProof).not.toBeNull();
    const checkedProof = generatedProof!;
    const digest = proofDigest(checkedProof);

    expect(sdk.ConfidentialRangeBigInt.amountWitnessBound(params, vectors.params.k).toString())
      .toBe(vectors.bounds.amountWitnessBound);
    expect(sdk.ConfidentialRangeBigInt.amountResponseBound(params, gamma, vectors.params.k, 1).toString())
      .toBe(vectors.bounds.amountResponseBoundChallenge1);
    expect(sdk.ConfidentialRangeBigInt.pairResponseBound(params, gamma, 1).toString())
      .toBe(vectors.bounds.pairResponseBoundChallenge1);
    expect(sdk.ConfidentialRangeBigInt.fsFields(
      ck,
      amountCommitment,
      checkedProof.bits,
      checkedProof.comps,
      checkedProof.amountAs,
      checkedProof.pairAss
    ).map((value: bigint) => value.toString())).toEqual(vectors.transcript.fields);
    expect(sdk.ConfidentialRangeBigInt.fsChallenges(
      params,
      ck,
      amountCommitment,
      checkedProof.bits,
      checkedProof.comps,
      checkedProof.amountAs,
      checkedProof.pairAss,
      vectors.transcript.firstRounds.length
    )).toEqual(vectors.transcript.firstRounds.map((entry) => entry.challenge));
    expect(vectors.proofCommitment.hash).toBe('sha3-256');
    expect(digest.digest).toBe(vectors.proofCommitment.digest);
    expect(digest.bytes).toBe(vectors.proofCommitment.canonicalJsonBytes);
    expect(checkedProof.amountAs.length).toBe(vectors.proofCommitment.amountRows);
    expect(checkedProof.pairAss.length).toBe(vectors.proofCommitment.pairRounds);
    expect(checkedProof.pairAss[0].length).toBe(vectors.proofCommitment.pairRowsPerRound);
    expect(checkedProof.amountAs[0].map((value: bigint) => value.toString()))
      .toEqual(vectors.proofCommitment.sample.firstAmountAnnouncement);
    expect(checkedProof.amountZs[0].map((value: bigint) => value.toString()))
      .toEqual(vectors.proofCommitment.sample.firstAmountResponse);
    expect(checkedProof.pairAss[0][0].map((value: bigint) => value.toString()))
      .toEqual(vectors.proofCommitment.sample.firstPairAnnouncement);
    expect(checkedProof.pairZss[0][0].map((value: bigint) => value.toString()))
      .toEqual(vectors.proofCommitment.sample.firstPairResponse);
    expect(sdk.ConfidentialRangeBigInt.fsVerify(
      params,
      gamma,
      vectors.params.k,
      ck,
      amountCommitment,
      checkedProof
    )).toBe(true);
    expect(sdk.ConfidentialRangeBigInt.fsVerify(
      params,
      gamma,
      vectors.params.k,
      ck,
      [amountCommitment[0] + 1n, ...amountCommitment.slice(1)],
      checkedProof
    )).toBe(false);
  });
});
