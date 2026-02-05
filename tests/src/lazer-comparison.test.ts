/**
 * Optional LaZer cross-comparison tests.
 *
 * These tests are deterministic and skip safely when LaZer's Python bindings
 * are unavailable on the machine.
 */

import { execFileSync } from 'child_process';
import * as path from 'path';
import { fileURLToPath } from 'url';

import { isCliAvailable, ringMult } from './isabella-cli.js';

interface RingParams {
  q: number;
  n: number;
}

interface Dims {
  rows: number;
  cols: number;
}

interface RingCase {
  a: number[];
  b: number[];
  ab: number[];
}

interface ChallengeCase {
  tau: number;
  challenge: number[];
  scaled_vector: number[][];
  mat_vec_scaled_right: number[][];
  mat_vec_scaled_left: number[][];
}

interface CenteredSamples {
  inputs: number[];
  outputs: number[];
}

interface LazerFixture {
  available: true;
  schema_version: number;
  ring: RingParams;
  dims: Dims;
  matrix: number[][][];
  vector: number[][];
  mat_vec_result: number[][];
  ring_case: RingCase;
  challenge_case: ChallengeCase;
  centered_samples: CenteredSamples;
}

interface LazerUnavailable {
  available: false;
  error: string;
}

type LazerAdapterOutput = LazerFixture | LazerUnavailable;

function centeredMod(x: number, q: number): number {
  const z = ((x % q) + q) % q;
  const half = Math.floor((q - 1) / 2);
  return z > half ? z - q : z;
}

function normalizePoly(poly: number[], q: number, n: number): number[] {
  const out = new Array<number>(n).fill(0);
  for (let i = 0; i < n; i++) {
    out[i] = centeredMod(poly[i] ?? 0, q);
  }
  return out;
}

function addPolysCentered(a: number[], b: number[], q: number): number[] {
  if (a.length !== b.length) {
    throw new Error(`Polynomial length mismatch: ${a.length} vs ${b.length}`);
  }
  const out = new Array<number>(a.length);
  for (let i = 0; i < a.length; i++) {
    out[i] = centeredMod(a[i] + b[i], q);
  }
  return out;
}

function scaleVecByPoly(vec: number[][], scalar: number[], n: number, q: number): number[][] {
  return vec.map(poly => {
    const lhs = normalizePoly(poly, q, n);
    const rhs = normalizePoly(scalar, q, n);
    return normalizePoly(ringMult(lhs, rhs, n, q).result, q, n);
  });
}

function challengeWeight(challenge: number[]): number {
  return challenge.filter(c => c !== 0).length;
}

function matVecMulWithIsabella(matrix: number[][][], vector: number[][], n: number, q: number): number[][] {
  const rows = matrix.length;
  if (rows === 0) return [];
  const cols = matrix[0].length;

  if (vector.length !== cols) {
    throw new Error(`Vector length ${vector.length} does not match matrix cols ${cols}`);
  }

  const out: number[][] = [];
  for (let r = 0; r < rows; r++) {
    if (matrix[r].length !== cols) {
      throw new Error(`Row ${r} has ${matrix[r].length} cols, expected ${cols}`);
    }

    let acc = new Array<number>(n).fill(0);
    for (let c = 0; c < cols; c++) {
      const lhs = normalizePoly(matrix[r][c], q, n);
      const rhs = normalizePoly(vector[c], q, n);
      const prod = ringMult(lhs, rhs, n, q).result;
      acc = addPolysCentered(acc, normalizePoly(prod, q, n), q);
    }
    out.push(acc);
  }
  return out;
}

function loadAdapterFixture(): LazerAdapterOutput {
  const __filename = fileURLToPath(import.meta.url);
  const __dirname = path.dirname(__filename);
  const adapterPath = path.join(__dirname, '..', 'scripts', 'lazer_adapter.py');

  let raw = '';
  try {
    raw = execFileSync('python3', [adapterPath], {
      encoding: 'utf-8',
      env: process.env,
      timeout: 30000,
      stdio: ['ignore', 'pipe', 'pipe'],
    }).trim();
  } catch (error: unknown) {
    const err = error as { message?: string };
    return { available: false, error: `adapter execution failed: ${err.message ?? 'unknown error'}` };
  }

  let parsed: unknown;
  try {
    parsed = JSON.parse(raw);
  } catch {
    return { available: false, error: `adapter output was not valid JSON: ${raw.slice(0, 200)}` };
  }

  if (typeof parsed !== 'object' || parsed === null || !('available' in parsed)) {
    return { available: false, error: 'adapter returned malformed payload' };
  }

  const payload = parsed as { available: unknown; error?: unknown };
  if (payload.available === false) {
    return {
      available: false,
      error: typeof payload.error === 'string' ? payload.error : 'LaZer unavailable',
    };
  }

  if (payload.available !== true) {
    return { available: false, error: 'adapter returned malformed availability flag' };
  }

  return parsed as LazerFixture;
}

const CLI_AVAILABLE = isCliAvailable();
const LAZER_ADAPTER: LazerAdapterOutput = CLI_AVAILABLE
  ? loadAdapterFixture()
  : { available: false, error: 'Isabella CLI unavailable' };

const LAZER_READY = CLI_AVAILABLE && LAZER_ADAPTER.available;
const describeIfLazer = LAZER_READY ? describe : describe.skip;

describeIfLazer('LaZer Comparison', () => {
  const requireFixture = (): LazerFixture => {
    if (!LAZER_ADAPTER.available) {
      throw new Error(`LaZer fixture unavailable: ${LAZER_ADAPTER.error}`);
    }
    return LAZER_ADAPTER;
  };

  it('uses the expected adapter schema', () => {
    const fixture = requireFixture();
    expect(fixture.schema_version).toBe(1);
    expect(fixture.ring.q).toBeGreaterThan(2);
    expect(fixture.ring.n).toBeGreaterThan(0);
    expect(fixture.matrix.length).toBe(fixture.dims.rows);
    expect(fixture.vector.length).toBe(fixture.dims.cols);
    expect(fixture.mat_vec_result.length).toBe(fixture.dims.rows);
    expect(fixture.challenge_case.challenge.length).toBe(fixture.ring.n);
  });

  it('matches centered reduction semantics used by LaZer', () => {
    const fixture = requireFixture();
    const { q } = fixture.ring;
    const { inputs, outputs } = fixture.centered_samples;
    expect(inputs.length).toBe(outputs.length);
    for (let i = 0; i < inputs.length; i++) {
      expect(centeredMod(inputs[i], q)).toBe(outputs[i]);
    }
  });

  it('matches deterministic ring multiplication probe', () => {
    const fixture = requireFixture();
    const { q, n } = fixture.ring;
    const actual = ringMult(
      normalizePoly(fixture.ring_case.a, q, n),
      normalizePoly(fixture.ring_case.b, q, n),
      n,
      q
    ).result;

    expect(normalizePoly(actual, q, n)).toEqual(normalizePoly(fixture.ring_case.ab, q, n));
  });

  it('matches deterministic matrix-vector multiplication over R_q', () => {
    const fixture = requireFixture();
    const { q, n } = fixture.ring;
    const actual = matVecMulWithIsabella(fixture.matrix, fixture.vector, n, q);
    const expected = fixture.mat_vec_result.map(poly => normalizePoly(poly, q, n));
    expect(actual).toEqual(expected);
  });

  it('uses sparse ternary challenge data with expected weight', () => {
    const fixture = requireFixture();
    const { n } = fixture.ring;
    const { challenge, tau } = fixture.challenge_case;

    expect(challenge.length).toBe(n);
    expect(challenge.every(c => c === -1 || c === 0 || c === 1)).toBe(true);
    expect(challengeWeight(challenge)).toBe(tau);
  });

  it('matches module scaling identity fixtures: A*(x*c) and (A*x)*c', () => {
    const fixture = requireFixture();
    const { q, n } = fixture.ring;
    const challenge = normalizePoly(fixture.challenge_case.challenge, q, n);

    const scaledVectorActual = scaleVecByPoly(fixture.vector, challenge, n, q);
    const scaledVectorExpected = fixture.challenge_case.scaled_vector.map(poly => normalizePoly(poly, q, n));
    expect(scaledVectorActual).toEqual(scaledVectorExpected);

    const rightActual = matVecMulWithIsabella(fixture.matrix, scaledVectorActual, n, q);
    const rightExpected = fixture.challenge_case.mat_vec_scaled_right.map(poly => normalizePoly(poly, q, n));
    expect(rightActual).toEqual(rightExpected);

    const baseActual = fixture.mat_vec_result.map(poly => normalizePoly(poly, q, n));
    const leftActual = scaleVecByPoly(baseActual, challenge, n, q);
    const leftExpected = fixture.challenge_case.mat_vec_scaled_left.map(poly => normalizePoly(poly, q, n));
    expect(leftActual).toEqual(leftExpected);

    // Algebraic consistency check in Isabella path.
    expect(leftActual).toEqual(rightActual);
  });
});

describe('LaZer Comparison Availability', () => {
  it('reports whether optional LaZer checks can run', () => {
    console.log(`Isabella CLI available: ${CLI_AVAILABLE}`);
    if (!CLI_AVAILABLE) {
      console.log('Skipping LaZer tests: build the CLI with `cd isabella.ml && dune build`.');
      return;
    }

    if (!LAZER_ADAPTER.available) {
      console.log(`Skipping LaZer tests: ${LAZER_ADAPTER.error}`);
      console.log('Set `LAZER_ROOT` (or `LAZER_PYTHON`) after building LaZer Python bindings.');
    }
  });
});
