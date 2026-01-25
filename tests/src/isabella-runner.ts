/**
 * Isabella Implementation Runner
 *
 * Utilities for calling our Haskell and OCaml implementations
 * to compare against noble-post-quantum.
 */

import { spawn, execSync } from 'child_process';
import * as path from 'path';
import { fileURLToPath } from 'url';

const __filename = fileURLToPath(import.meta.url);
const __dirname = path.dirname(__filename);
const projectRoot = path.join(__dirname, '..', '..');

/**
 * Run a command and return stdout
 */
function runCommand(cmd: string, args: string[], cwd: string): Promise<string> {
  return new Promise((resolve, reject) => {
    const proc = spawn(cmd, args, { cwd, shell: true });
    let stdout = '';
    let stderr = '';

    proc.stdout.on('data', (data) => {
      stdout += data.toString();
    });

    proc.stderr.on('data', (data) => {
      stderr += data.toString();
    });

    proc.on('close', (code) => {
      if (code === 0) {
        resolve(stdout.trim());
      } else {
        reject(new Error(`Command failed with code ${code}: ${stderr}`));
      }
    });

    proc.on('error', (err) => {
      reject(err);
    });
  });
}

/**
 * Check if Haskell implementation is available
 */
export async function isHaskellAvailable(): Promise<boolean> {
  try {
    const haskellDir = path.join(projectRoot, 'isabella.hs');
    await runCommand('cabal', ['build', 'isabella-cli'], haskellDir);
    return true;
  } catch {
    return false;
  }
}

/**
 * Check if OCaml implementation is available
 */
export async function isOCamlAvailable(): Promise<boolean> {
  try {
    const ocamlDir = path.join(projectRoot, 'isabella.ml');
    await runCommand('dune', ['build'], ocamlDir);
    return true;
  } catch {
    return false;
  }
}

/**
 * Kyber parameters for different security levels
 */
export interface KyberParams {
  n: number;
  q: number;
  k: number;
  eta1: number;
  eta2: number;
  du: number;
  dv: number;
}

export const KYBER_512_PARAMS: KyberParams = {
  n: 256,
  q: 3329,
  k: 2,
  eta1: 3,
  eta2: 2,
  du: 10,
  dv: 4,
};

export const KYBER_768_PARAMS: KyberParams = {
  n: 256,
  q: 3329,
  k: 3,
  eta1: 2,
  eta2: 2,
  du: 10,
  dv: 4,
};

export const KYBER_1024_PARAMS: KyberParams = {
  n: 256,
  q: 3329,
  k: 4,
  eta1: 2,
  eta2: 2,
  du: 11,
  dv: 5,
};

/**
 * NTT parameters for Kyber
 */
export const KYBER_NTT_PARAMS = {
  n: 256,
  q: 3329,
  omega: 17,  // primitive 256th root of unity mod 3329
};

/**
 * Modular arithmetic helpers (for validation)
 */
export function modCentered(x: number, q: number): number {
  const r = ((x % q) + q) % q;
  return r > Math.floor(q / 2) ? r - q : r;
}

/**
 * Reference NTT implementation for validation
 * This is a naive O(n^2) implementation for correctness checking
 */
export function nttNaive(a: number[], omega: number, q: number, n: number): number[] {
  const result: number[] = new Array(n);
  for (let k = 0; k < n; k++) {
    let sum = 0;
    for (let j = 0; j < n; j++) {
      const exp = (k * j) % n;
      const twiddle = powerMod(omega, exp, q);
      sum = (sum + a[j] * twiddle) % q;
    }
    result[k] = sum;
  }
  return result;
}

/**
 * Modular exponentiation
 */
export function powerMod(base: number, exp: number, mod: number): number {
  let result = 1;
  base = base % mod;
  while (exp > 0) {
    if (exp % 2 === 1) {
      result = (result * base) % mod;
    }
    exp = Math.floor(exp / 2);
    base = (base * base) % mod;
  }
  return result;
}

/**
 * Check if omega is a primitive n-th root of unity mod q
 */
export function isPrimitiveRoot(omega: number, n: number, q: number): boolean {
  // omega^n should be 1 (mod q)
  if (powerMod(omega, n, q) !== 1) return false;

  // omega^(n/p) should not be 1 for any prime factor p of n
  // For n = 256 = 2^8, only factor is 2
  for (let d = 1; d < n; d *= 2) {
    if (powerMod(omega, d, q) === 1) return false;
  }

  return true;
}

/**
 * Polynomial multiplication mod (X^n + 1) using schoolbook method
 * Used for validation against NTT-based multiplication
 */
export function polyMultNaive(a: number[], b: number[], q: number, n: number): number[] {
  const c = new Array(n).fill(0);
  for (let i = 0; i < n; i++) {
    for (let j = 0; j < n; j++) {
      const idx = i + j;
      if (idx < n) {
        c[idx] = (c[idx] + a[i] * b[j]) % q;
      } else {
        // X^n = -1 (mod X^n + 1)
        c[idx - n] = (c[idx - n] - a[i] * b[j] % q + q) % q;
      }
    }
  }
  return c;
}

/**
 * Vector dot product mod q
 */
export function dotProduct(a: number[], b: number[], q: number): number {
  let sum = 0;
  for (let i = 0; i < Math.min(a.length, b.length); i++) {
    sum = (sum + a[i] * b[i]) % q;
  }
  return sum;
}

/**
 * Matrix-vector multiplication mod q
 */
export function matVecMult(M: number[][], v: number[], q: number): number[] {
  return M.map(row => dotProduct(row, v, q));
}
