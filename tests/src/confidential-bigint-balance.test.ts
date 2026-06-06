import fs from 'node:fs';
import path from 'node:path';
import { createHash } from 'node:crypto';
import { fileURLToPath, pathToFileURL } from 'node:url';

const __filename = fileURLToPath(import.meta.url);
const __dirname = path.dirname(__filename);
const projectRoot = path.resolve(__dirname, '..', '..');
const vectorsPath = path.join(projectRoot, 'tests/fixtures/confidential-bigint-balance-vectors.json');
const typeScriptEntry = path.join(projectRoot, 'isabella.ts/dist/index.mjs');

type DecimalVec = string[];
type DecimalMatrix = string[][];

type BigIntBalanceVectors = {
  version: number;
  algorithm: string;
  status: string;
  params: {
    m: number;
    n1: number;
    n2: number;
    q: string;
    beta: string;
    gamma: string;
  };
  transcript: {
    dst: string;
    domain: number;
    fieldEncoding: string;
    fields: DecimalVec;
    firstRounds: Array<{ round: number; challenge: number }>;
  };
  case: {
    name: string;
    commitmentKey: DecimalMatrix;
    witness: DecimalVec;
    commitment: DecimalVec;
    masks: DecimalMatrix;
    proof: {
      as: DecimalMatrix;
      zs: DecimalMatrix;
    };
  };
};

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

describe('Confidential balance BigInt vectors', () => {
  const vectors = JSON.parse(fs.readFileSync(vectorsPath, 'utf8')) as BigIntBalanceVectors;

  it('pins a q83 TypeScript BigInt balance proof path', async () => {
    const sdk = await import(pathToFileURL(typeScriptEntry).href);
    expect(vectors.version).toBe(1);
    expect(vectors.algorithm).toBe('SHA3-256-counter-mode-low-bit');
    expect(vectors.status).toBe('typescript-reference-with-native-preview-parity');
    expect(vectors.transcript.dst).toBe('ISABELLA-CT-FS-v1');
    expect(vectors.transcript.domain).toBe(1001);
    expect(vectors.transcript.fieldEncoding).toBe('sign_u8 || len_i64_le || magnitude_le_minimal');

    const params = sdk.ConfidentialBalanceBigInt.makeParams(
      vectors.params.m,
      vectors.params.n2,
      vectors.params.q,
      vectors.params.beta
    );
    const gamma = parseDecimal(vectors.params.gamma);
    const ck = parseMatrix(vectors.case.commitmentKey);
    const witness = parseVec(vectors.case.witness);
    const commitment = parseVec(vectors.case.commitment);
    const masks = parseMatrix(vectors.case.masks);
    const proof = {
      as: parseMatrix(vectors.case.proof.as),
      zs: parseMatrix(vectors.case.proof.zs),
    };
    const fields = parseVec(vectors.transcript.fields);

    expect(params.q).toBe(parseDecimal(vectors.params.q));
    expect(params.q > BigInt(Number.MAX_SAFE_INTEGER)).toBe(true);
    expect(sdk.ConfidentialBalanceBigInt.validScalarParams(params)).toBe(true);
    expect(sdk.ConfidentialBalanceBigInt.validCommitKey(params, ck)).toBe(true);
    expect(sdk.ConfidentialBalanceBigInt.validWitness(params, witness)).toBe(true);
    expect(sdk.ConfidentialBalanceBigInt.randCommit(params, ck, witness)).toEqual(commitment);
    expect(sdk.ConfidentialBalanceBigInt.fsFields(ck, commitment, proof.as)).toEqual(fields);

    for (const entry of vectors.transcript.firstRounds) {
      expect(transcriptChallenge(vectors.transcript.dst, vectors.transcript.domain, fields, entry.round)).toBe(
        entry.challenge
      );
    }

    expect(sdk.ConfidentialBalanceBigInt.fsVerify(params, gamma, ck, commitment, proof)).toBe(true);
    expect(sdk.ConfidentialBalanceBigInt.fsProve(params, gamma, ck, commitment, witness, masks)).toEqual(proof);
    expect(
      sdk.ConfidentialBalanceBigInt.fsVerify(
        params,
        gamma,
        ck,
        [commitment[0] + 1n, commitment[1]],
        proof
      )
    ).toBe(false);
    expect(() =>
      sdk.ConfidentialBalanceBigInt.makeParams(2, 2, Number.MAX_SAFE_INTEGER + 1, 65536)
    ).toThrow();
  });
});
