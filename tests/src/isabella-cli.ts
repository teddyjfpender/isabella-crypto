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
const projectRoot = process.env.ISABELLA_PROJECT_ROOT
  ? path.resolve(process.env.ISABELLA_PROJECT_ROOT)
  : path.join(__dirname, '..', '..');
const ocamlDir = process.env.ISABELLA_OCAML_DIR
  ? path.resolve(process.env.ISABELLA_OCAML_DIR)
  : path.join(projectRoot, 'isabella.ml');
const ocamlCliBinary = process.env.ISABELLA_OCAML_CLI
  ? path.resolve(process.env.ISABELLA_OCAML_CLI)
  : path.join(ocamlDir, '_build', 'default', 'bin', 'isabella_cli.exe');
const ocamlCliBinaryShell = JSON.stringify(ocamlCliBinary);

/**
 * Run the Isabella OCaml CLI with given arguments
 */
export function runCli(args: string[], json: boolean = true): string {
  const allArgs = json ? ['--json', ...args] : args;
  try {
    const result = execSync(
      `${ocamlCliBinaryShell} ${allArgs.map(a => `"${a}"`).join(' ')}`,
      {
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

function parseCliBool(output: string): boolean {
  const parsed = parseCliResult<BoolResult | boolean>(output);
  if (typeof parsed === 'boolean') {
    return parsed;
  }
  if (typeof parsed === 'object' && parsed !== null && 'result' in parsed) {
    return Boolean(parsed.result);
  }
  throw new Error(`Failed to parse CLI output as a boolean result: ${output}`);
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
    execSync(`${ocamlCliBinaryShell} --help`, {
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

// ============================================
// Confidential Balance CLI Operations
// ============================================

export interface ScalarCommitParams {
  n1: number;
  n2: number;
  m: number;
  q: number;
  beta: number;
}

export interface BalanceProof {
  as: number[][];
  zs: number[][];
}

export interface BalanceRound {
  a: number[];
  z: number[];
  challenge?: boolean | number;
}

export type BalanceProofLike =
  | BalanceProof
  | { rounds: BalanceRound[] }
  | { as: number[][]; zs: number[][]; challenges?: Array<boolean | number> };

export function normalizeBalanceProof(proof: BalanceProofLike): BalanceRound[] {
  if ('rounds' in proof && Array.isArray(proof.rounds)) {
    return proof.rounds.map((round) => ({
      a: round.a,
      z: round.z,
      challenge: round.challenge,
    }));
  }
  if ('as' in proof && 'zs' in proof && Array.isArray(proof.as) && Array.isArray(proof.zs)) {
    return proof.as.map((a, index) => ({
      a,
      z: proof.zs[index] ?? [],
      challenge: proof.challenges?.[index],
    }));
  }
  return [{ a: proof.a, z: proof.z }];
}

export function balanceProofShape(proof: BalanceProofLike): 'single' | 'rounds' | 'lists' {
  if ('rounds' in proof && Array.isArray(proof.rounds)) {
    return 'rounds';
  }
  if ('as' in proof && 'zs' in proof && Array.isArray(proof.as) && Array.isArray(proof.zs)) {
    return 'lists';
  }
  return 'single';
}

export function listBalanceProof(proof: BalanceProofLike): BalanceProof {
  if ('as' in proof && 'zs' in proof && Array.isArray(proof.as) && Array.isArray(proof.zs)) {
    return { as: proof.as, zs: proof.zs };
  }
  const rounds = normalizeBalanceProof(proof);
  return {
    as: rounds.map((round) => round.a),
    zs: rounds.map((round) => round.z),
  };
}

function vecMod(v: number[], q: number): number[] {
  return v.map((x) => ((x % q) + q) % q);
}

function vecAdd(v1: number[], v2: number[]): number[] {
  return v1.map((x, i) => x + v2[i]);
}

function scalarMult(c: number, v: number[]): number[] {
  return v.map((x) => c * x);
}

function matVecMult(mat: number[][], vec: number[]): number[] {
  return mat.map((row) => row.reduce((sum, coeff, i) => sum + coeff * vec[i], 0));
}

function ledgerHash(q: number, left: number[], right: number[]): number[] {
  return vecMod(vecAdd(left, scalarMult(2, right)), q);
}

function emptyCommitment(m: number): number[] {
  return Array.from({ length: m }, () => 0);
}

function compressPairs(q: number, ledger: number[][]): number[][] {
  if (ledger.length === 0) {
    return [];
  }
  if (ledger.length === 1) {
    return [ledger[0].slice()];
  }
  const out: number[][] = [];
  for (let i = 0; i < ledger.length; i += 2) {
    const left = ledger[i];
    const right = i + 1 < ledger.length ? ledger[i + 1] : emptyCommitment(left.length);
    out.push(ledgerHash(q, left, right));
  }
  return out;
}

function ledgerRoot(params: ScalarCommitParams, ledger: number[][]): number[] {
  if (ledger.length === 0) {
    return emptyCommitment(params.m);
  }
  if (ledger.length === 1) {
    return ledger[0].slice();
  }
  return ledgerRoot(params, compressPairs(params.q, ledger));
}

function indexDirections(depth: number, index: number): boolean[] {
  const directions: boolean[] = [];
  let current = index;
  for (let i = 0; i < depth; i += 1) {
    directions.push(current % 2 === 1);
    current = Math.floor(current / 2);
  }
  return directions;
}

function authPathRoot(
  params: ScalarCommitParams,
  node: number[],
  siblings: number[][],
  directions: boolean[]
): number[] {
  let acc = node.slice();
  for (let i = 0; i < siblings.length; i += 1) {
    const sibling = siblings[i];
    acc = directions[i] ? ledgerHash(params.q, sibling, acc) : ledgerHash(params.q, acc, sibling);
  }
  return acc;
}

export function cbParams(m: number, n2: number, q: number, beta: number): ScalarCommitParams {
  const output = runCli(['cb-params', m.toString(), n2.toString(), q.toString(), beta.toString()]);
  return parseCliResult<ScalarCommitParams>(output);
}

export function cbValidParams(m: number, n2: number, q: number, beta: number): boolean {
  const output = runCli(['cb-valid-params', m.toString(), n2.toString(), q.toString(), beta.toString()]);
  return parseCliResult<BoolResult>(output).result;
}

export function cbRandCommitKey(
  m: number,
  n2: number,
  q: number,
  beta: number,
  ck: number[][]
): number[][] {
  const output = runCli([
    'cb-rand-commit-key',
    m.toString(),
    n2.toString(),
    q.toString(),
    beta.toString(),
    JSON.stringify(ck),
  ]);
  return parseCliResult<{ result: number[][] }>(output).result;
}

export function cbRandCommit(
  m: number,
  n2: number,
  q: number,
  beta: number,
  ck: number[][],
  r: number[]
): number[] {
  const output = runCli([
    'cb-rand-commit',
    m.toString(),
    n2.toString(),
    q.toString(),
    beta.toString(),
    JSON.stringify(ck),
    JSON.stringify(r),
  ]);
  return parseCliResult<{ result: number[] }>(output).result;
}

export function cbValidWitness(m: number, n2: number, q: number, beta: number, r: number[]): boolean {
  const output = runCli([
    'cb-valid-witness',
    m.toString(),
    n2.toString(),
    q.toString(),
    beta.toString(),
    JSON.stringify(r),
  ]);
  return parseCliResult<BoolResult>(output).result;
}

export function cbValidMask(
  m: number,
  n2: number,
  q: number,
  beta: number,
  gamma: number,
  y: number[]
): boolean {
  const output = runCli([
    'cb-valid-mask',
    m.toString(),
    n2.toString(),
    q.toString(),
    beta.toString(),
    gamma.toString(),
    JSON.stringify(y),
  ]);
  return parseCliResult<BoolResult>(output).result;
}

export function cbValidResponse(
  m: number,
  n2: number,
  q: number,
  beta: number,
  gamma: number,
  challenge: number,
  z: number[]
): boolean {
  return z.length === n2 && z.every((value) => Math.abs(value) <= gamma + Math.abs(challenge) * (4 * beta));
}

export function cbBalanceCommitment(
  cIn1: number[],
  cIn2: number[],
  cOut1: number[],
  cOut2: number[],
  q: number
): number[] {
  const output = runCli([
    'cb-balance-commitment',
    JSON.stringify(cIn1),
    JSON.stringify(cIn2),
    JSON.stringify(cOut1),
    JSON.stringify(cOut2),
    q.toString(),
  ]);
  return parseCliResult<{ result: number[] }>(output).result;
}

export function cbCanonicalChallenge(
  m: number,
  n2: number,
  q: number,
  beta: number,
  ck: number[][],
  c: number[],
  a: number[]
): number {
  const output = runCli([
    'cb-canonical-challenge',
    m.toString(),
    n2.toString(),
    q.toString(),
    beta.toString(),
    JSON.stringify(ck),
    JSON.stringify(c),
    JSON.stringify(a),
  ]);
  return parseCliResult<{ result: number }>(output).result;
}

export function ctNullifierCanonicalChallenge(
  m: number,
  n2: number,
  q: number,
  beta: number,
  ck: number[][],
  nk: number[][],
  c: number[],
  nf: number[],
  aCommit: number[],
  aNullifier: number[]
): number {
  const output = runCli([
    'ct-nullifier-canonical-challenge',
    m.toString(),
    n2.toString(),
    q.toString(),
    beta.toString(),
    JSON.stringify(ck),
    JSON.stringify(nk),
    JSON.stringify(c),
    JSON.stringify(nf),
    JSON.stringify(aCommit),
    JSON.stringify(aNullifier),
  ]);
  return parseCliResult<{ result: number }>(output).result;
}

export function cbSigmaCommit(
  m: number,
  n2: number,
  q: number,
  beta: number,
  ck: number[][],
  y: number[]
): number[] {
  const randKey = ck.map((row) => row.slice(1));
  return vecMod(matVecMult(randKey, y), q);
}

export function cbSigmaRespond(r: number[], y: number[], challenge: number): number[] {
  return vecAdd(y, scalarMult(challenge, r));
}

export function cbSigmaVerify(
  m: number,
  n2: number,
  q: number,
  beta: number,
  gamma: number,
  ck: number[][],
  c: number[],
  a: number[],
  challenge: number,
  z: number[]
): boolean {
  return (
    cbValidResponse(m, n2, q, beta, gamma, challenge, z) &&
    JSON.stringify(cbSigmaCommit(m, n2, q, beta, ck, z)) ===
      JSON.stringify(vecMod(vecAdd(a, scalarMult(challenge, c)), q))
  );
}

export function cbProve(
  m: number,
  n2: number,
  q: number,
  beta: number,
  gamma: number,
  ck: number[][],
  c: number[],
  r: number[],
  ys: number[][]
): BalanceProofLike | null {
  const output = runCli([
    'cb-prove',
    m.toString(),
    n2.toString(),
    q.toString(),
    beta.toString(),
    gamma.toString(),
    JSON.stringify(ck),
    JSON.stringify(c),
    JSON.stringify(r),
    JSON.stringify(ys),
  ]);
  return output === 'null' ? null : parseCliResult<BalanceProofLike>(output);
}

export function cbVerify(
  m: number,
  n2: number,
  q: number,
  beta: number,
  gamma: number,
  ck: number[][],
  c: number[],
  proof: BalanceProofLike
): boolean {
  const listed = listBalanceProof(proof);
  const output = runCli([
    'cb-verify',
    m.toString(),
    n2.toString(),
    q.toString(),
    beta.toString(),
    gamma.toString(),
    JSON.stringify(ck),
    JSON.stringify(c),
    JSON.stringify(listed.as),
    JSON.stringify(listed.zs),
  ]);
  return parseCliBool(output);
}

export interface RangeProof {
  bits: number[][];
  comps: number[][];
  amountAs: number[][];
  amountZs: number[][];
  pairAss: number[][][];
  pairZss: number[][][];
  challenges?: Array<boolean | number>;
}

interface LegacyRangeProof {
  bits: number[][];
  comps: number[][];
  amountA: number[];
  amountZ: number[];
  pairAs: number[][];
  pairZs: number[][];
}

export interface RangeRound {
  amountA: number[];
  amountZ: number[];
  pairAs: number[][];
  pairZs: number[][];
  challenge?: boolean | number;
}

export type RangeProofLike =
  | RangeProof
  | { bits: number[][]; comps: number[][]; rounds: RangeRound[] }
  | {
      bits: number[][];
      comps: number[][];
      amountAs: number[][];
      amountZs: number[][];
      pairAss: number[][][];
      pairZss: number[][][];
      challenges?: Array<boolean | number>;
    }
  | Record<string, unknown>;

export function rangeProofShape(proof: unknown): 'legacy' | 'rounds' | 'lists' | 'unknown' {
  if (!proof || typeof proof !== 'object') {
    return 'unknown';
  }
  if ('rounds' in proof && Array.isArray((proof as { rounds?: unknown[] }).rounds)) {
    return 'rounds';
  }
  if ('amountAs' in proof || 'amountZs' in proof || 'pairAss' in proof || 'pairZss' in proof) {
    return 'lists';
  }
  if (
    'bits' in proof &&
    'comps' in proof &&
    'amountA' in proof &&
    'amountZ' in proof &&
    'pairAs' in proof &&
    'pairZs' in proof
  ) {
    return 'legacy';
  }
  return 'unknown';
}

function expectLegacyRangeProof(proof: RangeProofLike, context: string): RangeProof {
  if (rangeProofShape(proof) === 'legacy') {
    return proof as unknown as RangeProof;
  }
  throw new Error(
    `${context} has not been updated for repeated range-proof serialization yet. ` +
      `Observed proof shape: ${rangeProofShape(proof)}.`
  );
}

export function listRangeProof(proof: RangeProofLike): {
  bits: number[][];
  comps: number[][];
  amountsA: number[][];
  amountsZ: number[][];
  pairAss: number[][][];
  pairZss: number[][][];
} {
  const shape = rangeProofShape(proof);
  if (shape === 'legacy') {
    const legacy = proof as LegacyRangeProof;
    return {
      bits: legacy.bits,
      comps: legacy.comps,
      amountsA: [legacy.amountA],
      amountsZ: [legacy.amountZ],
      pairAss: [legacy.pairAs],
      pairZss: [legacy.pairZs],
    };
  }
  if (shape === 'rounds') {
    const repeated = proof as { bits: number[][]; comps: number[][]; rounds: RangeRound[] };
    return {
      bits: repeated.bits,
      comps: repeated.comps,
      amountsA: repeated.rounds.map((round) => round.amountA),
      amountsZ: repeated.rounds.map((round) => round.amountZ),
      pairAss: repeated.rounds.map((round) => round.pairAs),
      pairZss: repeated.rounds.map((round) => round.pairZs),
    };
  }
  if (shape === 'lists') {
    const listed = proof as {
      bits: number[][];
      comps: number[][];
      amountAs?: number[][];
      amountZs?: number[][];
      pairAss?: number[][][];
      pairZss?: number[][][];
      amountA?: number[];
      amountZ?: number[];
      pairAs?: number[][];
      pairZs?: number[][];
    };
    return {
      bits: listed.bits,
      comps: listed.comps,
      amountsA: listed.amountAs ?? (listed.amountA ? [listed.amountA] : []),
      amountsZ: listed.amountZs ?? (listed.amountZ ? [listed.amountZ] : []),
      pairAss: listed.pairAss ?? (listed.pairAs ? [listed.pairAs] : []),
      pairZss: listed.pairZss ?? (listed.pairZs ? [listed.pairZs] : []),
    };
  }
  throw new Error('range proof shape is not recognized by the CLI shim');
}

export function crAmountCommitment(
  m: number,
  n2: number,
  q: number,
  beta: number,
  ck: number[][],
  cAmount: number[],
  cBits: number[][]
): number[] {
  const output = runCli([
    'cr-amount-commitment',
    m.toString(),
    n2.toString(),
    q.toString(),
    beta.toString(),
    JSON.stringify(ck),
    JSON.stringify(cAmount),
    JSON.stringify(cBits),
  ]);
  return parseCliResult<{ result: number[] }>(output).result;
}

export function crProve(
  m: number,
  n2: number,
  q: number,
  beta: number,
  gamma: number,
  k: number,
  ck: number[][],
  cAmount: number[],
  amount: number,
  amountRand: number[],
  bits: number[],
  bitRands: number[][],
  comps: number[],
  compRands: number[][],
  yAmounts: number[][],
  yPairss: number[][][]
): RangeProofLike | null {
  const output = runCli([
    'cr-prove',
    m.toString(),
    n2.toString(),
    q.toString(),
    beta.toString(),
    gamma.toString(),
    k.toString(),
    JSON.stringify(ck),
    JSON.stringify(cAmount),
    amount.toString(),
    JSON.stringify(amountRand),
    JSON.stringify(bits),
    JSON.stringify(bitRands),
    JSON.stringify(comps),
    JSON.stringify(compRands),
    JSON.stringify(yAmounts),
    JSON.stringify(yPairss),
  ]);
  return output === 'null' ? null : parseCliResult<RangeProofLike>(output);
}

export function crVerify(
  m: number,
  n2: number,
  q: number,
  beta: number,
  gamma: number,
  k: number,
  ck: number[][],
  cAmount: number[],
  proof: RangeProofLike
): boolean {
  const shape = rangeProofShape(proof);
  if (shape === 'legacy') {
    const legacy = proof as RangeProof;
    const output = runCli([
      'cr-verify',
      m.toString(),
      n2.toString(),
      q.toString(),
      beta.toString(),
      gamma.toString(),
      k.toString(),
      JSON.stringify(ck),
      JSON.stringify(cAmount),
      JSON.stringify(legacy.bits),
      JSON.stringify(legacy.comps),
      JSON.stringify(legacy.amountA),
    JSON.stringify(legacy.amountZ),
    JSON.stringify(legacy.pairAs),
    JSON.stringify(legacy.pairZs),
  ]);
    return parseCliBool(output);
  }
  const listed = listRangeProof(proof);
  const output = runCli([
    'cr-verify',
    m.toString(),
    n2.toString(),
    q.toString(),
    beta.toString(),
    gamma.toString(),
    k.toString(),
    JSON.stringify(ck),
    JSON.stringify(cAmount),
    JSON.stringify(listed.bits),
    JSON.stringify(listed.comps),
    JSON.stringify(listed.amountsA),
    JSON.stringify(listed.amountsZ),
    JSON.stringify(listed.pairAss),
    JSON.stringify(listed.pairZss),
  ]);
  return parseCliBool(output);
}

export interface NullifierProof {
  aCommits: number[][];
  aNullifiers: number[][];
  zMsgs: number[][];
  zRands: number[][];
  challenges?: Array<boolean | number>;
}

interface LegacyNullifierProof {
  aCommit: number[];
  aNullifier: number[];
  zMsg: number[];
  zRand: number[];
}

export interface NullifierRound {
  aCommit: number[];
  aNullifier: number[];
  zMsg: number[];
  zRand: number[];
  challenge?: boolean | number;
}

export type NullifierProofLike =
  | NullifierProof
  | { rounds: NullifierRound[] }
  | {
      aCommits: number[][];
      aNullifiers: number[][];
      zMsgs: number[][];
      zRands: number[][];
      challenges?: Array<boolean | number>;
    }
  | {
      commitAs: number[][];
      nullifierAs: number[][];
      msgZs: number[][];
      randZs: number[][];
      challenges?: Array<boolean | number>;
    };

export function nullifierProofShape(proof: unknown): 'legacy' | 'rounds' | 'lists' | 'unknown' {
  if (!proof || typeof proof !== 'object') {
    return 'unknown';
  }
  if ('rounds' in proof && Array.isArray((proof as { rounds?: unknown[] }).rounds)) {
    return 'rounds';
  }
  if (
    'aCommits' in proof &&
    'aNullifiers' in proof &&
    'zMsgs' in proof &&
    'zRands' in proof
  ) {
    return 'lists';
  }
  if (
    'commitAs' in proof &&
    'nullifierAs' in proof &&
    'msgZs' in proof &&
    'randZs' in proof
  ) {
    return 'lists';
  }
  if ('aCommit' in proof && 'aNullifier' in proof && 'zMsg' in proof && 'zRand' in proof) {
    return 'legacy';
  }
  return 'unknown';
}

export function listNullifierProof(proof: NullifierProofLike): {
  aCommits: number[][];
  aNullifiers: number[][];
  zMsgs: number[][];
  zRands: number[][];
} {
  const shape = nullifierProofShape(proof);
  if (shape === 'legacy') {
    const legacy = proof as LegacyNullifierProof;
    return {
      aCommits: [legacy.aCommit],
      aNullifiers: [legacy.aNullifier],
      zMsgs: [legacy.zMsg],
      zRands: [legacy.zRand],
    };
  }
  if (shape === 'rounds') {
    const repeated = proof as { rounds: NullifierRound[] };
    return {
      aCommits: repeated.rounds.map((round) => round.aCommit),
      aNullifiers: repeated.rounds.map((round) => round.aNullifier),
      zMsgs: repeated.rounds.map((round) => round.zMsg),
      zRands: repeated.rounds.map((round) => round.zRand),
    };
  }
  if (shape === 'lists') {
    const listed = proof as {
      aCommits?: number[][];
      aNullifiers?: number[][];
      zMsgs?: number[][];
      zRands?: number[][];
      commitAs?: number[][];
      nullifierAs?: number[][];
      msgZs?: number[][];
      randZs?: number[][];
    };
    return {
      aCommits: listed.aCommits ?? listed.commitAs ?? [],
      aNullifiers: listed.aNullifiers ?? listed.nullifierAs ?? [],
      zMsgs: listed.zMsgs ?? listed.msgZs ?? [],
      zRands: listed.zRands ?? listed.randZs ?? [],
    };
  }
  throw new Error('nullifier proof shape is not recognized by the CLI shim');
}

export interface MembershipProof {
  index: number;
  root: number[];
  siblings: number[][];
  directions: boolean[];
}

export interface MerkleMembershipProof {
  index: number;
  root: string;
  siblings: string[];
  directions: boolean[];
}

export interface TransactionProof {
  in1Member: MembershipProof;
  in2Member: MembershipProof;
  in1Nullifier: NullifierProofLike;
  in2Nullifier: NullifierProofLike;
  balance: BalanceProofLike;
  out1Range: RangeProofLike;
  out2Range: RangeProofLike;
}

export interface MerkleTransactionProof {
  in1Member: MerkleMembershipProof;
  in2Member: MerkleMembershipProof;
  in1Nullifier: NullifierProofLike;
  in2Nullifier: NullifierProofLike;
  balance: BalanceProofLike;
  out1Range: RangeProofLike;
  out2Range: RangeProofLike;
}

export interface TransactionContext {
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
}

export interface TransactionContextPolicy {
  protocolVersion: number;
  networkId: string;
  assetId: number;
  ledgerEpoch: number;
  root: { digest: string; depth: number };
  publicFee: number;
}

export interface WalletProofRequest {
  context: TransactionContext;
  acceptedRoots: Array<{ digest: string; depth: number }>;
  spentNullifiers: number[][];
}

function acceptedRootDigests(roots: Array<{ digest: string; depth: number }>): string[] {
  return roots.map((root) => root.digest);
}

function acceptedRootDepths(roots: Array<{ digest: string; depth: number }>): number[] {
  return roots.map((root) => root.depth);
}

export function ctNullifier(
  m: number,
  n2: number,
  q: number,
  beta: number,
  nk: number[][],
  amount: number,
  rand: number[]
): number[] {
  const output = runCli([
    'ct-nullifier',
    m.toString(),
    n2.toString(),
    q.toString(),
    beta.toString(),
    JSON.stringify(nk),
    amount.toString(),
    JSON.stringify(rand),
  ]);
  return parseCliResult<{ result: number[] }>(output).result;
}

export function ctNullifierProve(
  m: number,
  n2: number,
  q: number,
  beta: number,
  gamma: number,
  ck: number[][],
  nk: number[][],
  c: number[],
  nf: number[],
  amount: number,
  rand: number[],
  yMsgs: number[],
  yRands: number[][]
): NullifierProofLike | null {
  const output = runCli([
    'ct-nullifier-prove',
    m.toString(),
    n2.toString(),
    q.toString(),
    beta.toString(),
    gamma.toString(),
    JSON.stringify(ck),
    JSON.stringify(nk),
    JSON.stringify(c),
    JSON.stringify(nf),
    amount.toString(),
    JSON.stringify(rand),
    JSON.stringify(yMsgs),
    JSON.stringify(yRands),
  ]);
  return output === 'null' ? null : parseCliResult<NullifierProofLike>(output);
}

export function ctNullifierVerify(
  m: number,
  n2: number,
  q: number,
  beta: number,
  gamma: number,
  ck: number[][],
  nk: number[][],
  c: number[],
  nf: number[],
  proof: NullifierProofLike
): boolean {
  const shape = nullifierProofShape(proof);
  if (shape === 'legacy') {
    const legacy = proof as LegacyNullifierProof;
    const output = runCli([
      'ct-nullifier-verify',
      m.toString(),
      n2.toString(),
      q.toString(),
      beta.toString(),
      gamma.toString(),
      JSON.stringify(ck),
      JSON.stringify(nk),
      JSON.stringify(c),
      JSON.stringify(nf),
      JSON.stringify(legacy.aCommit),
      JSON.stringify(legacy.aNullifier),
      JSON.stringify(legacy.zMsg),
      JSON.stringify(legacy.zRand),
    ]);
    return parseCliBool(output);
  }
  const listed = listNullifierProof(proof);
  const output = runCli([
    'ct-nullifier-verify',
    m.toString(),
    n2.toString(),
    q.toString(),
    beta.toString(),
    gamma.toString(),
    JSON.stringify(ck),
    JSON.stringify(nk),
    JSON.stringify(c),
    JSON.stringify(nf),
    JSON.stringify(listed.aCommits),
    JSON.stringify(listed.aNullifiers),
    JSON.stringify(listed.zMsgs),
    JSON.stringify(listed.zRands),
  ]);
  return parseCliBool(output);
}

export function ctLedgerRoot(params: ScalarCommitParams, ledger: number[][]): number[] {
  return ledgerRoot(params, ledger);
}

export function ctMemberProve(
  params: ScalarCommitParams,
  ledger: number[][],
  c: number[]
): MembershipProof | null {
  const output = runCli([
    'ct-member-prove',
    params.m.toString(),
    params.n2.toString(),
    params.q.toString(),
    params.beta.toString(),
    JSON.stringify(ledger),
    JSON.stringify(c),
  ]);
  return output === 'null' ? null : parseCliResult<MembershipProof>(output);
}

export function ctMemberVerify(
  params: ScalarCommitParams,
  c: number[],
  proof: MembershipProof
): boolean {
  return (
    proof.siblings.length === proof.directions.length &&
    JSON.stringify(proof.directions) === JSON.stringify(indexDirections(proof.siblings.length, proof.index)) &&
    JSON.stringify(authPathRoot(params, c, proof.siblings, proof.directions)) === JSON.stringify(proof.root)
  );
}

export function ctMerkleLeaf(commitment: number[]): string {
  const output = runCli(['ct-merkle-leaf', JSON.stringify(commitment)]);
  return parseCliResult<{ result: string }>(output).result;
}

export function ctMerkleEmpty(width: number): string {
  const output = runCli(['ct-merkle-empty', width.toString()]);
  return parseCliResult<{ result: string }>(output).result;
}

export function ctMerkleNode(left: string, right: string): string {
  const output = runCli(['ct-merkle-node', left, right]);
  return parseCliResult<{ result: string }>(output).result;
}

export function ctMerkleRoot(ledger: number[][]): string {
  const output = runCli(['ct-merkle-root', JSON.stringify(ledger)]);
  return parseCliResult<{ result: string }>(output).result;
}

export function ctMerkleMemberProve(
  ledger: number[][],
  commitment: number[]
): MerkleMembershipProof | null {
  const output = runCli(['ct-merkle-member-prove', JSON.stringify(ledger), JSON.stringify(commitment)]);
  return output === 'null' ? null : parseCliResult<MerkleMembershipProof>(output);
}

export function ctMerkleMemberVerify(ledger: number[][], commitment: number[]): boolean {
  const output = runCli(['ct-merkle-member-verify', JSON.stringify(ledger), JSON.stringify(commitment)]);
  return parseCliBool(output);
}

export function ctTransactionContext(
  protocolVersion: number,
  networkId: string,
  assetId: number,
  ledgerEpoch: number,
  root: { digest: string; depth: number },
  publicFee: number,
  cIn1: number[],
  cIn2: number[],
  cOut1: number[],
  cOut2: number[],
  nf1: number[],
  nf2: number[]
): string {
  const output = runCli([
    'ct-transaction-context',
    protocolVersion.toString(),
    networkId,
    assetId.toString(),
    ledgerEpoch.toString(),
    root.digest,
    root.depth.toString(),
    publicFee.toString(),
    JSON.stringify(cIn1),
    JSON.stringify(cIn2),
    JSON.stringify(cOut1),
    JSON.stringify(cOut2),
    JSON.stringify(nf1),
    JSON.stringify(nf2),
  ]);
  return parseCliResult<{ result: string }>(output).result;
}

export function ctWalletProofRequestDigest(request: WalletProofRequest): string {
  const context = request.context;
  const output = runCli([
    'ct-wallet-proof-request-digest',
    context.protocolVersion.toString(),
    context.networkId,
    context.assetId.toString(),
    context.ledgerEpoch.toString(),
    context.root.digest,
    context.root.depth.toString(),
    context.publicFee.toString(),
    JSON.stringify(context.cIn1),
    JSON.stringify(context.cIn2),
    JSON.stringify(context.cOut1),
    JSON.stringify(context.cOut2),
    JSON.stringify(context.nf1),
    JSON.stringify(context.nf2),
    JSON.stringify(acceptedRootDigests(request.acceptedRoots)),
    JSON.stringify(acceptedRootDepths(request.acceptedRoots)),
    JSON.stringify(request.spentNullifiers),
  ]);
  return parseCliResult<{ result: string }>(output).result;
}

export function ctProveScaffold(
  m: number,
  n2: number,
  q: number,
  beta: number,
  gamma: number,
  k: number,
  ck: number[][],
  nk: number[][],
  ledger: number[][],
  spent: number[][],
  cIn1: number[],
  cIn2: number[],
  cOut1: number[],
  cOut2: number[],
  nf1: number[],
  nf2: number[],
  in1Amount: number,
  in1Rand: number[],
  in2Amount: number,
  in2Rand: number[],
  out1Amount: number,
  out1Rand: number[],
  out2Amount: number,
  out2Rand: number[],
  out1Bits: number[],
  out1BitRands: number[][],
  out1Comps: number[],
  out1CompRands: number[][],
  out2Bits: number[],
  out2BitRands: number[][],
  out2Comps: number[],
  out2CompRands: number[][],
  yIn1Msgs: number[],
  yIn1Rands: number[][],
  yIn2Msgs: number[],
  yIn2Rands: number[][],
  yBalance: number[][],
  yOut1: number[][],
  yOut1Pairs: number[][][],
  yOut2: number[][],
  yOut2Pairs: number[][][]
): TransactionProof | null {
  const output = runCli([
    'ct-prove-scaffold',
    m.toString(),
    n2.toString(),
    q.toString(),
    beta.toString(),
    gamma.toString(),
    k.toString(),
    JSON.stringify(ck),
    JSON.stringify(nk),
    JSON.stringify(ledger),
    JSON.stringify(spent),
    JSON.stringify(cIn1),
    JSON.stringify(cIn2),
    JSON.stringify(cOut1),
    JSON.stringify(cOut2),
    JSON.stringify(nf1),
    JSON.stringify(nf2),
    in1Amount.toString(),
    JSON.stringify(in1Rand),
    in2Amount.toString(),
    JSON.stringify(in2Rand),
    out1Amount.toString(),
    JSON.stringify(out1Rand),
    out2Amount.toString(),
    JSON.stringify(out2Rand),
    JSON.stringify(out1Bits),
    JSON.stringify(out1BitRands),
    JSON.stringify(out1Comps),
    JSON.stringify(out1CompRands),
    JSON.stringify(out2Bits),
    JSON.stringify(out2BitRands),
    JSON.stringify(out2Comps),
    JSON.stringify(out2CompRands),
    JSON.stringify(yIn1Msgs),
    JSON.stringify(yIn1Rands),
    JSON.stringify(yIn2Msgs),
    JSON.stringify(yIn2Rands),
    JSON.stringify(yBalance),
    JSON.stringify(yOut1),
    JSON.stringify(yOut1Pairs),
    JSON.stringify(yOut2),
    JSON.stringify(yOut2Pairs),
  ]);
  return output === 'null' ? null : parseCliResult<TransactionProof>(output);
}

export function ctProveMerkle(
  m: number,
  n2: number,
  q: number,
  beta: number,
  gamma: number,
  k: number,
  ck: number[][],
  nk: number[][],
  ledger: number[][],
  spent: number[][],
  cIn1: number[],
  cIn2: number[],
  cOut1: number[],
  cOut2: number[],
  nf1: number[],
  nf2: number[],
  in1Amount: number,
  in1Rand: number[],
  in2Amount: number,
  in2Rand: number[],
  out1Amount: number,
  out1Rand: number[],
  out2Amount: number,
  out2Rand: number[],
  out1Bits: number[],
  out1BitRands: number[][],
  out1Comps: number[],
  out1CompRands: number[][],
  out2Bits: number[],
  out2BitRands: number[][],
  out2Comps: number[],
  out2CompRands: number[][],
  yIn1Msgs: number[],
  yIn1Rands: number[][],
  yIn2Msgs: number[],
  yIn2Rands: number[][],
  yBalance: number[][],
  yOut1: number[][],
  yOut1Pairs: number[][][],
  yOut2: number[][],
  yOut2Pairs: number[][][]
): MerkleTransactionProof | null {
  const output = runCli([
    'ct-prove-merkle',
    m.toString(),
    n2.toString(),
    q.toString(),
    beta.toString(),
    gamma.toString(),
    k.toString(),
    JSON.stringify(ck),
    JSON.stringify(nk),
    JSON.stringify(ledger),
    JSON.stringify(spent),
    JSON.stringify(cIn1),
    JSON.stringify(cIn2),
    JSON.stringify(cOut1),
    JSON.stringify(cOut2),
    JSON.stringify(nf1),
    JSON.stringify(nf2),
    in1Amount.toString(),
    JSON.stringify(in1Rand),
    in2Amount.toString(),
    JSON.stringify(in2Rand),
    out1Amount.toString(),
    JSON.stringify(out1Rand),
    out2Amount.toString(),
    JSON.stringify(out2Rand),
    JSON.stringify(out1Bits),
    JSON.stringify(out1BitRands),
    JSON.stringify(out1Comps),
    JSON.stringify(out1CompRands),
    JSON.stringify(out2Bits),
    JSON.stringify(out2BitRands),
    JSON.stringify(out2Comps),
    JSON.stringify(out2CompRands),
    JSON.stringify(yIn1Msgs),
    JSON.stringify(yIn1Rands),
    JSON.stringify(yIn2Msgs),
    JSON.stringify(yIn2Rands),
    JSON.stringify(yBalance),
    JSON.stringify(yOut1),
    JSON.stringify(yOut1Pairs),
    JSON.stringify(yOut2),
    JSON.stringify(yOut2Pairs),
  ]);
  return output === 'null' ? null : parseCliResult<MerkleTransactionProof>(output);
}

function ctTransactionProofArgs(
  proof: TransactionProof | MerkleTransactionProof,
  options: { forceListed?: boolean } = {}
): string[] {
  const listedBalance = listBalanceProof(proof.balance);
  const in1NullifierShape = nullifierProofShape(proof.in1Nullifier);
  const in2NullifierShape = nullifierProofShape(proof.in2Nullifier);
  const out1RangeShape = rangeProofShape(proof.out1Range);
  const out2RangeShape = rangeProofShape(proof.out2Range);
  const useLegacyIn1Nullifier = !options.forceListed && in1NullifierShape === 'legacy';
  const useLegacyIn2Nullifier = !options.forceListed && in2NullifierShape === 'legacy';
  const useLegacyOut1Range = !options.forceListed && out1RangeShape === 'legacy';
  const useLegacyOut2Range = !options.forceListed && out2RangeShape === 'legacy';
  const listedIn1Nullifier =
    useLegacyIn1Nullifier ? null : listNullifierProof(proof.in1Nullifier);
  const listedIn2Nullifier =
    useLegacyIn2Nullifier ? null : listNullifierProof(proof.in2Nullifier);
  const listedOut1Range =
    useLegacyOut1Range ? null : listRangeProof(proof.out1Range);
  const listedOut2Range =
    useLegacyOut2Range ? null : listRangeProof(proof.out2Range);
  const legacyIn1Nullifier =
    useLegacyIn1Nullifier ? (proof.in1Nullifier as LegacyNullifierProof) : null;
  const legacyIn2Nullifier =
    useLegacyIn2Nullifier ? (proof.in2Nullifier as LegacyNullifierProof) : null;
  const legacyOut1Range =
    useLegacyOut1Range ? (proof.out1Range as LegacyRangeProof) : null;
  const legacyOut2Range =
    useLegacyOut2Range ? (proof.out2Range as LegacyRangeProof) : null;
  return [
    JSON.stringify(
      legacyIn1Nullifier === null ? listedIn1Nullifier!.aCommits : legacyIn1Nullifier.aCommit
    ),
    JSON.stringify(
      legacyIn1Nullifier === null
        ? listedIn1Nullifier!.aNullifiers
        : legacyIn1Nullifier.aNullifier
    ),
    JSON.stringify(
      legacyIn1Nullifier === null ? listedIn1Nullifier!.zMsgs : legacyIn1Nullifier.zMsg
    ),
    JSON.stringify(
      legacyIn1Nullifier === null ? listedIn1Nullifier!.zRands : legacyIn1Nullifier.zRand
    ),
    JSON.stringify(
      legacyIn2Nullifier === null ? listedIn2Nullifier!.aCommits : legacyIn2Nullifier.aCommit
    ),
    JSON.stringify(
      legacyIn2Nullifier === null
        ? listedIn2Nullifier!.aNullifiers
        : legacyIn2Nullifier.aNullifier
    ),
    JSON.stringify(
      legacyIn2Nullifier === null ? listedIn2Nullifier!.zMsgs : legacyIn2Nullifier.zMsg
    ),
    JSON.stringify(
      legacyIn2Nullifier === null ? listedIn2Nullifier!.zRands : legacyIn2Nullifier.zRand
    ),
    JSON.stringify(listedBalance.as),
    JSON.stringify(listedBalance.zs),
    JSON.stringify(legacyOut1Range === null ? listedOut1Range!.bits : legacyOut1Range.bits),
    JSON.stringify(legacyOut1Range === null ? listedOut1Range!.comps : legacyOut1Range.comps),
    JSON.stringify(
      legacyOut1Range === null ? listedOut1Range!.amountsA : legacyOut1Range.amountA
    ),
    JSON.stringify(
      legacyOut1Range === null ? listedOut1Range!.amountsZ : legacyOut1Range.amountZ
    ),
    JSON.stringify(legacyOut1Range === null ? listedOut1Range!.pairAss : legacyOut1Range.pairAs),
    JSON.stringify(legacyOut1Range === null ? listedOut1Range!.pairZss : legacyOut1Range.pairZs),
    JSON.stringify(legacyOut2Range === null ? listedOut2Range!.bits : legacyOut2Range.bits),
    JSON.stringify(legacyOut2Range === null ? listedOut2Range!.comps : legacyOut2Range.comps),
    JSON.stringify(
      legacyOut2Range === null ? listedOut2Range!.amountsA : legacyOut2Range.amountA
    ),
    JSON.stringify(
      legacyOut2Range === null ? listedOut2Range!.amountsZ : legacyOut2Range.amountZ
    ),
    JSON.stringify(legacyOut2Range === null ? listedOut2Range!.pairAss : legacyOut2Range.pairAs),
    JSON.stringify(legacyOut2Range === null ? listedOut2Range!.pairZss : legacyOut2Range.pairZs),
  ];
}

function ctMerkleMembershipDigestArgs(proof: MerkleMembershipProof): string[] {
  return [
    proof.index.toString(),
    proof.root,
    JSON.stringify(proof.siblings),
    JSON.stringify(proof.directions.map((direction) => (direction ? 1 : 0))),
  ];
}

export function ctMerkleProofDigestArgs(proof: MerkleTransactionProof): string[] {
  return [
    ...ctMerkleMembershipDigestArgs(proof.in1Member),
    ...ctMerkleMembershipDigestArgs(proof.in2Member),
    ...ctTransactionProofArgs(proof, { forceListed: true }),
  ];
}

export function ctMerkleProofDigest(proof: MerkleTransactionProof): string {
  const output = runCli(['ct-merkle-proof-digest', ...ctMerkleProofDigestArgs(proof)]);
  return parseCliResult<{ result: string }>(output).result;
}

export function ctMerkleEnvelopeDigest(
  contextDigest: string,
  context: TransactionContext,
  proof: MerkleTransactionProof
): string {
  const output = runCli([
    'ct-merkle-envelope-digest',
    contextDigest,
    context.protocolVersion.toString(),
    context.networkId,
    context.assetId.toString(),
    context.ledgerEpoch.toString(),
    context.root.digest,
    context.root.depth.toString(),
    context.publicFee.toString(),
    JSON.stringify(context.cIn1),
    JSON.stringify(context.cIn2),
    JSON.stringify(context.cOut1),
    JSON.stringify(context.cOut2),
    JSON.stringify(context.nf1),
    JSON.stringify(context.nf2),
    ...ctMerkleProofDigestArgs(proof),
  ]);
  return parseCliResult<{ result: string }>(output).result;
}

function ctVerifyScaffoldArgs(
  m: number,
  n2: number,
  q: number,
  beta: number,
  gamma: number,
  k: number,
  ck: number[][],
  nk: number[][],
  ledger: number[][],
  spent: number[][],
  cIn1: number[],
  cIn2: number[],
  cOut1: number[],
  cOut2: number[],
  nf1: number[],
  nf2: number[],
  proof: TransactionProof | MerkleTransactionProof
): string[] {
  return [
    m.toString(),
    n2.toString(),
    q.toString(),
    beta.toString(),
    gamma.toString(),
    k.toString(),
    JSON.stringify(ck),
    JSON.stringify(nk),
    JSON.stringify(ledger),
    JSON.stringify(spent),
    JSON.stringify(cIn1),
    JSON.stringify(cIn2),
    JSON.stringify(cOut1),
    JSON.stringify(cOut2),
    JSON.stringify(nf1),
    JSON.stringify(nf2),
    ...ctTransactionProofArgs(proof),
  ];
}

export function ctVerifyMerkleArgs(
  m: number,
  n2: number,
  q: number,
  beta: number,
  gamma: number,
  k: number,
  ck: number[][],
  nk: number[][],
  ledger: number[][],
  spent: number[][],
  cIn1: number[],
  cIn2: number[],
  cOut1: number[],
  cOut2: number[],
  nf1: number[],
  nf2: number[],
  proof: MerkleTransactionProof
): string[] {
  return [
    m.toString(),
    n2.toString(),
    q.toString(),
    beta.toString(),
    gamma.toString(),
    k.toString(),
    JSON.stringify(ck),
    JSON.stringify(nk),
    JSON.stringify(ledger),
    JSON.stringify(spent),
    JSON.stringify(cIn1),
    JSON.stringify(cIn2),
    JSON.stringify(cOut1),
    JSON.stringify(cOut2),
    JSON.stringify(nf1),
    JSON.stringify(nf2),
    ...ctMerkleProofDigestArgs(proof),
  ];
}

function ctVerifyWithCommand(
  command: string,
  m: number,
  n2: number,
  q: number,
  beta: number,
  gamma: number,
  k: number,
  ck: number[][],
  nk: number[][],
  ledger: number[][],
  spent: number[][],
  cIn1: number[],
  cIn2: number[],
  cOut1: number[],
  cOut2: number[],
  nf1: number[],
  nf2: number[],
  proof: TransactionProof | MerkleTransactionProof
): boolean {
  const output = runCli([
    command,
    ...ctVerifyScaffoldArgs(
      m,
      n2,
      q,
      beta,
      gamma,
      k,
      ck,
      nk,
      ledger,
      spent,
      cIn1,
      cIn2,
      cOut1,
      cOut2,
      nf1,
      nf2,
      proof
    ),
  ]);
  return parseCliBool(output);
}

export function ctVerifyScaffold(
  m: number,
  n2: number,
  q: number,
  beta: number,
  gamma: number,
  k: number,
  ck: number[][],
  nk: number[][],
  ledger: number[][],
  spent: number[][],
  cIn1: number[],
  cIn2: number[],
  cOut1: number[],
  cOut2: number[],
  nf1: number[],
  nf2: number[],
  proof: TransactionProof
): boolean {
  return ctVerifyWithCommand(
    'ct-verify-scaffold',
    m,
    n2,
    q,
    beta,
    gamma,
    k,
    ck,
    nk,
    ledger,
    spent,
    cIn1,
    cIn2,
    cOut1,
    cOut2,
    nf1,
    nf2,
    proof
  );
}

export function ctVerifyMerkle(
  m: number,
  n2: number,
  q: number,
  beta: number,
  gamma: number,
  k: number,
  ck: number[][],
  nk: number[][],
  ledger: number[][],
  spent: number[][],
  cIn1: number[],
  cIn2: number[],
  cOut1: number[],
  cOut2: number[],
  nf1: number[],
  nf2: number[],
  proof: MerkleTransactionProof
): boolean {
  const output = runCli([
    'ct-verify-merkle',
    ...ctVerifyMerkleArgs(
      m,
      n2,
      q,
      beta,
      gamma,
      k,
      ck,
      nk,
      ledger,
      spent,
      cIn1,
      cIn2,
      cOut1,
      cOut2,
      nf1,
      nf2,
      proof
    ),
  ]);
  return parseCliBool(output);
}

export function ctVerifyMerkleEnvelopeArgs(
  m: number,
  n2: number,
  q: number,
  beta: number,
  gamma: number,
  k: number,
  ck: number[][],
  nk: number[][],
  ledger: number[][],
  spent: number[][],
  policy: TransactionContextPolicy,
  contextDigest: string,
  context: TransactionContext,
  proof: MerkleTransactionProof
): string[] {
  return [
    m.toString(),
    n2.toString(),
    q.toString(),
    beta.toString(),
    gamma.toString(),
    k.toString(),
    JSON.stringify(ck),
    JSON.stringify(nk),
    JSON.stringify(ledger),
    JSON.stringify(spent),
    policy.protocolVersion.toString(),
    policy.networkId,
    policy.assetId.toString(),
    policy.ledgerEpoch.toString(),
    policy.root.digest,
    policy.root.depth.toString(),
    policy.publicFee.toString(),
    contextDigest,
    context.protocolVersion.toString(),
    context.networkId,
    context.assetId.toString(),
    context.ledgerEpoch.toString(),
    context.root.digest,
    context.root.depth.toString(),
    context.publicFee.toString(),
    JSON.stringify(context.cIn1),
    JSON.stringify(context.cIn2),
    JSON.stringify(context.cOut1),
    JSON.stringify(context.cOut2),
    JSON.stringify(context.nf1),
    JSON.stringify(context.nf2),
    ...ctMerkleProofDigestArgs(proof),
  ];
}

export function ctVerifyMerkleEnvelope(
  m: number,
  n2: number,
  q: number,
  beta: number,
  gamma: number,
  k: number,
  ck: number[][],
  nk: number[][],
  ledger: number[][],
  spent: number[][],
  policy: TransactionContextPolicy,
  contextDigest: string,
  context: TransactionContext,
  proof: MerkleTransactionProof
): boolean {
  const output = runCli([
    'ct-verify-merkle-envelope',
    ...ctVerifyMerkleEnvelopeArgs(
      m,
      n2,
      q,
      beta,
      gamma,
      k,
      ck,
      nk,
      ledger,
      spent,
      policy,
      contextDigest,
      context,
      proof
    ),
  ]);
  return parseCliBool(output);
}
