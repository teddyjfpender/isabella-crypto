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
const vectorsPath = path.join(projectRoot, 'tests/fixtures/confidential-bigint-nullifier-vectors.json');

type DecimalVec = string[];
type DecimalMatrix = string[][];
type DecimalOpening = { msg: DecimalVec; rand: DecimalVec };
type NullifierProofJson = {
  aCommits: DecimalMatrix;
  aNullifiers: DecimalMatrix;
  zMsgs: DecimalMatrix;
  zRands: DecimalMatrix;
};

type NullifierFixture = {
  version: number;
  algorithm: string;
  status: string;
  params: { m: number; n1: number; n2: number; q: string; beta: string; gamma: string };
  bounds: { responseBoundChallenge1: string };
  maskPolicy: { msg: string; rand: string };
  transcript: {
    dst: string;
    domain: number;
    fieldEncoding: string;
    rounds: number;
    fields: DecimalVec;
    firstRounds: Array<{ round: number; challenge: number }>;
  };
  case: {
    name: string;
    commitmentKey: DecimalMatrix;
    nullifierKey: DecimalMatrix;
    opening: DecimalOpening;
    commitment: DecimalVec;
    nullifier: DecimalVec;
    masks: DecimalOpening[];
    proof: NullifierProofJson;
  };
};

const vectors = JSON.parse(fs.readFileSync(vectorsPath, 'utf8')) as NullifierFixture;

function parseDecimal(value: string): bigint {
  if (!/^(0|-?[1-9][0-9]*)$/.test(value)) {
    throw new Error(`non-canonical decimal integer: ${value}`);
  }
  return BigInt(value);
}

function parseVec(values: DecimalVec): bigint[] {
  return values.map(parseDecimal);
}

function parseMatrix(rows: DecimalMatrix): bigint[][] {
  return rows.map(parseVec);
}

function parseOpening(opening: DecimalOpening) {
  return {
    msg: parseVec(opening.msg),
    rand: parseVec(opening.rand),
  };
}

function parseProof(proof: NullifierProofJson) {
  return {
    aCommits: parseMatrix(proof.aCommits),
    aNullifiers: parseMatrix(proof.aNullifiers),
    zMsgs: parseMatrix(proof.zMsgs),
    zRands: parseMatrix(proof.zRands),
  };
}

function i64le(value: number): Buffer {
  const out = Buffer.alloc(8);
  out.writeBigInt64LE(BigInt(value), 0);
  return out;
}

function encodeBigInt(value: bigint): Buffer {
  const negative = value < 0n;
  let magnitude = negative ? -value : value;
  const bytes: number[] = [];
  while (magnitude > 0n) {
    bytes.push(Number(magnitude & 0xffn));
    magnitude >>= 8n;
  }
  return Buffer.concat([
    Buffer.from([negative ? 1 : 0]),
    i64le(bytes.length),
    Buffer.from(bytes),
  ]);
}

function transcriptChallenge(dst: string, domain: number, fields: bigint[], round: number): number {
  const preimage = Buffer.concat([
    Buffer.from(dst, 'ascii'),
    i64le(domain),
    i64le(round),
    i64le(fields.length),
    ...fields.map(encodeBigInt),
  ]);
  return createHash('sha3-256').update(preimage).digest()[0] & 1;
}

describe('Confidential nullifier BigInt vectors', () => {
  it('pins a q83 TypeScript BigInt nullifier proof path', async () => {
    const sdk = await import(pathToFileURL(typeScriptEntry).href);
    expect(vectors.version).toBe(1);
    expect(vectors.algorithm).toBe('SHA3-256-counter-mode-low-bit');
    expect(vectors.status).toBe('typescript-reference-with-native-preview-parity');
    expect(vectors.transcript.dst).toBe('ISABELLA-CT-FS-v1');
    expect(vectors.transcript.domain).toBe(3001);
    expect(vectors.transcript.rounds).toBe(128);
    expect(vectors.transcript.fieldEncoding).toBe('sign_u8 || len_i64_le || magnitude_le_minimal');
    expect(vectors.maskPolicy.msg).toContain('round + 3');

    const params = sdk.ConfidentialBalanceBigInt.makeParams(
      vectors.params.m,
      vectors.params.n2,
      vectors.params.q,
      vectors.params.beta
    );
    const gamma = parseDecimal(vectors.params.gamma);
    const ck = parseMatrix(vectors.case.commitmentKey);
    const nk = parseMatrix(vectors.case.nullifierKey);
    const opening = parseOpening(vectors.case.opening);
    const c = parseVec(vectors.case.commitment);
    const nf = parseVec(vectors.case.nullifier);
    const masks = vectors.case.masks.map(parseOpening);
    const proof = parseProof(vectors.case.proof);
    const fields = parseVec(vectors.transcript.fields);

    expect(params.q).toBe(parseDecimal(vectors.params.q));
    expect(params.q > BigInt(Number.MAX_SAFE_INTEGER)).toBe(true);
    expect(sdk.ConfidentialBalanceBigInt.validScalarParams(params)).toBe(true);
    expect(sdk.ConfidentialBalanceBigInt.validCommitKey(params, ck)).toBe(true);
    expect(sdk.ConfidentialBalanceBigInt.validCommitKey(params, nk)).toBe(true);
    expect(sdk.ConfidentialNullifierBigInt.nullifier(params, nk, opening)).toEqual(nf);
    expect(sdk.ConfidentialNullifierBigInt.responseBound(params, gamma, 1).toString())
      .toBe(vectors.bounds.responseBoundChallenge1);
    expect(sdk.ConfidentialNullifierBigInt.fsFields(
      ck,
      nk,
      c,
      nf,
      proof.aCommits,
      proof.aNullifiers
    )).toEqual(fields);

    for (const entry of vectors.transcript.firstRounds) {
      expect(transcriptChallenge(vectors.transcript.dst, vectors.transcript.domain, fields, entry.round))
        .toBe(entry.challenge);
    }

    expect(sdk.ConfidentialNullifierBigInt.fsChallenges(
      params,
      ck,
      nk,
      c,
      nf,
      proof.aCommits,
      proof.aNullifiers,
      vectors.transcript.firstRounds.length
    )).toEqual(vectors.transcript.firstRounds.map((entry) => entry.challenge));
    expect(sdk.ConfidentialNullifierBigInt.fsProve(params, gamma, ck, nk, c, nf, opening, masks))
      .toEqual(proof);
    expect(sdk.ConfidentialNullifierBigInt.fsVerify(params, gamma, ck, nk, c, nf, proof)).toBe(true);
    expect(sdk.ConfidentialNullifierBigInt.fsVerify(
      params,
      gamma,
      ck,
      nk,
      [c[0] + 1n, ...c.slice(1)],
      nf,
      proof
    )).toBe(false);
    expect(sdk.ConfidentialNullifierBigInt.fsVerify(
      params,
      gamma,
      ck,
      nk,
      c,
      [nf[0] + 1n, ...nf.slice(1)],
      proof
    )).toBe(false);
  });
});
