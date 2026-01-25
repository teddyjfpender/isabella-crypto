/**
 * Isabella CLI Integration
 *
 * Functions for calling the OCaml CLI and parsing results.
 */

import { execSync, spawn } from 'child_process';
import * as path from 'path';
import { fileURLToPath } from 'url';

const __filename = fileURLToPath(import.meta.url);
const __dirname = path.dirname(__filename);
const projectRoot = path.join(__dirname, '..', '..');
const ocamlDir = path.join(projectRoot, 'isabella.ml');

/**
 * Run the Isabella OCaml CLI with given arguments
 */
export function runCli(args: string[], json: boolean = true): string {
  const allArgs = json ? ['--json', ...args] : args;
  try {
    const result = execSync(
      `eval $(opam env) && dune exec isabella_cli -- ${allArgs.map(a => `"${a}"`).join(' ')}`,
      {
        cwd: ocamlDir,
        encoding: 'utf-8',
        shell: '/bin/bash',
        timeout: 30000,
      }
    );
    return result.trim();
  } catch (error: any) {
    throw new Error(`CLI failed: ${error.message}\nStderr: ${error.stderr}`);
  }
}

/**
 * Parse JSON result from CLI
 */
export function parseCliResult<T>(output: string): T {
  try {
    return JSON.parse(output) as T;
  } catch (e) {
    throw new Error(`Failed to parse CLI output as JSON: ${output}`);
  }
}

/**
 * NTT operations via CLI
 */
export interface NttResult {
  input: number[];
  output: number[];
  n: number;
  q: number;
  omega: number;
}

export function nttFast(vec: number[], omega: number, q: number, n: number): NttResult {
  const output = runCli(['ntt-fast', JSON.stringify(vec), omega.toString(), q.toString(), n.toString()]);
  return parseCliResult<NttResult>(output);
}

export function inttFast(vec: number[], omega: number, q: number, n: number): NttResult {
  const output = runCli(['intt-fast', JSON.stringify(vec), omega.toString(), q.toString(), n.toString()]);
  return parseCliResult<NttResult>(output);
}

export interface PointwiseResult {
  a: number[];
  b: number[];
  result: number[];
  q: number;
}

export function nttPointwise(a: number[], b: number[], q: number): PointwiseResult {
  const output = runCli(['ntt-pointwise', JSON.stringify(a), JSON.stringify(b), q.toString()]);
  return parseCliResult<PointwiseResult>(output);
}

/**
 * Basic math operations via CLI
 */
export interface SingleResult {
  result: number;
}

export interface BoolResult {
  result: boolean;
}

export function powerMod(a: number, k: number, m: number): number {
  const output = runCli(['power-mod', a.toString(), k.toString(), m.toString()]);
  return parseCliResult<SingleResult>(output).result;
}

export function modInverse(a: number, m: number): number {
  const output = runCli(['mod-inverse', a.toString(), m.toString()]);
  return parseCliResult<SingleResult>(output).result;
}

export function isPrimitiveRoot(omega: number, n: number, q: number): boolean {
  const output = runCli(['is-primitive-root', omega.toString(), n.toString(), q.toString()]);
  return parseCliResult<BoolResult>(output).result;
}

/**
 * Polynomial operations via CLI
 */
export interface PolyMultResult {
  a: number[];
  b: number[];
  result: number[];
}

export function polyMult(a: number[], b: number[]): PolyMultResult {
  const output = runCli(['poly-mult', JSON.stringify(a), JSON.stringify(b)]);
  return parseCliResult<PolyMultResult>(output);
}

export interface RingMultResult {
  a: number[];
  b: number[];
  result: number[];
  n: number;
  q: number;
}

export function ringMult(a: number[], b: number[], n: number, q: number): RingMultResult {
  const output = runCli(['ring-mult', JSON.stringify(a), JSON.stringify(b), n.toString(), q.toString()]);
  return parseCliResult<RingMultResult>(output);
}

/**
 * Kyber operations via CLI
 */
export interface KyberNttResult {
  input: number[];
  output: number[];
}

export function kyberNtt(vec: number[]): KyberNttResult {
  const output = runCli(['kyber-ntt', JSON.stringify(vec)]);
  return parseCliResult<KyberNttResult>(output);
}

export function kyberIntt(vec: number[]): KyberNttResult {
  const output = runCli(['kyber-intt', JSON.stringify(vec)]);
  return parseCliResult<KyberNttResult>(output);
}

export function kyberPolyMult(a: number[], b: number[]): PolyMultResult {
  const output = runCli(['kyber-poly-mult', JSON.stringify(a), JSON.stringify(b)]);
  return parseCliResult<PolyMultResult>(output);
}

export function kyberEncodeMsg(msg: number[]): KyberNttResult {
  const output = runCli(['kyber-encode-msg', JSON.stringify(msg)]);
  return parseCliResult<KyberNttResult>(output);
}

export function kyberDecodeMsg(poly: number[]): KyberNttResult {
  const output = runCli(['kyber-decode-msg', JSON.stringify(poly)]);
  return parseCliResult<KyberNttResult>(output);
}

/**
 * Check if CLI is available
 */
export function isCliAvailable(): boolean {
  try {
    execSync('eval $(opam env) && dune exec isabella_cli -- --help', {
      cwd: ocamlDir,
      shell: '/bin/bash',
      timeout: 10000,
      stdio: 'pipe',
    });
    return true;
  } catch {
    return false;
  }
}

// ============================================
// Dilithium CLI Operations
// ============================================

export interface DilithiumParams {
  n: number;
  q: number;
  k: number;
  l: number;
  eta: number;
  tau: number;
  beta: number;
  gamma1: number;
  gamma2: number;
  d: number;
  omega: number;
}

export interface Power2RoundResult {
  r: number;
  d: number;
  r1: number;
  r0: number;
}

export interface DecomposeResult {
  r: number;
  alpha: number;
  r1: number;
  r0: number;
}

export interface HintResult {
  z?: number;
  h?: number;
  r: number;
  alpha: number;
  result: number;
}

export interface BoundCheckResult {
  value: number;
  bound: number;
  result: boolean;
}

/**
 * Get Dilithium/ML-DSA parameters for a variant
 */
export function dilParams(variant: '44' | '65' | '87'): DilithiumParams {
  const output = runCli(['dil-params', variant]);
  return parseCliResult<DilithiumParams>(output);
}

/**
 * Centered modular reduction
 */
export function dilModCentered(r: number, m: number): number {
  const output = runCli(['dil-mod-centered', r.toString(), m.toString()]);
  return parseCliResult<{ r: number; m: number; result: number }>(output).result;
}

/**
 * Power2Round: split r into (r1, r0) where r = r1 * 2^d + r0
 */
export function dilPower2Round(r: number, d: number): Power2RoundResult {
  const output = runCli(['dil-power2round', r.toString(), d.toString()]);
  return parseCliResult<Power2RoundResult>(output);
}

/**
 * Decompose: split r into high and low bits using alpha
 */
export function dilDecompose(r: number, alpha: number): DecomposeResult {
  const output = runCli(['dil-decompose', r.toString(), alpha.toString()]);
  return parseCliResult<DecomposeResult>(output);
}

/**
 * HighBits: extract high-order bits
 */
export function dilHighbits(r: number, alpha: number): number {
  const output = runCli(['dil-highbits', r.toString(), alpha.toString()]);
  return parseCliResult<{ r: number; alpha: number; result: number }>(output).result;
}

/**
 * LowBits: extract low-order bits
 */
export function dilLowbits(r: number, alpha: number): number {
  const output = runCli(['dil-lowbits', r.toString(), alpha.toString()]);
  return parseCliResult<{ r: number; alpha: number; result: number }>(output).result;
}

/**
 * MakeHint: compute hint bit
 */
export function dilMakeHint(z: number, r: number, alpha: number): number {
  const output = runCli(['dil-makehint', z.toString(), r.toString(), alpha.toString()]);
  return parseCliResult<HintResult>(output).result;
}

/**
 * UseHint: recover high bits using hint
 */
export function dilUseHint(h: number, r: number, alpha: number): number {
  const output = runCli(['dil-usehint', h.toString(), r.toString(), alpha.toString()]);
  return parseCliResult<HintResult>(output).result;
}

/**
 * Check if |value| < bound
 */
export function dilCheckBound(value: number, bound: number): boolean {
  const output = runCli(['dil-check-bound', value.toString(), bound.toString()]);
  return parseCliResult<BoundCheckResult>(output).result;
}

/**
 * Compute hint weight (total number of 1s)
 */
export function dilHintWeight(hints: number[][]): number {
  const hintsStr = '[' + hints.map(row => '[' + row.join(',') + ']').join(',') + ']';
  const output = runCli(['dil-hint-weight', hintsStr]);
  return parseCliResult<SingleResult>(output).result;
}
