/**
 * Isabella - Verified Lattice Cryptography
 *
 * TypeScript bindings for formally verified lattice-based cryptography.
 * The underlying implementation is extracted from Isabelle/HOL proofs
 * and compiled to JavaScript via js_of_ocaml.
 */

// Load the compiled OCaml runtime
import './isabella.js';

declare global {
  const Isabella: IsabellaModule;
}

/** Integer vector (arbitrary precision) */
export type IntVec = number[];

/** Integer matrix (list of rows) */
export type IntMatrix = number[][];

/** LWE ciphertext */
export interface LweCiphertext {
  u: IntVec;
  v: number;
}

/** Isabella lattice cryptography module */
export interface IsabellaModule {
  /** Vector addition: xs + ys (component-wise) */
  vecAdd(xs: IntVec, ys: IntVec): IntVec;

  /** Vector modular reduction: each x_i mod q */
  vecMod(v: IntVec, q: number): IntVec;

  /** Inner product (dot product): sum(x_i * y_i) */
  innerProd(xs: IntVec, ys: IntVec): number;

  /** Matrix-vector multiplication: A * x */
  matVecMult(mat: IntMatrix, vec: IntVec): IntVec;

  /** Matrix transpose */
  transpose(mat: IntMatrix): IntMatrix;

  /** Encode a bit for LWE: false -> 0, true -> q/2 */
  encodeBit(q: number, bit: boolean): number;

  /** Decode a bit from LWE: < q/2 -> false, >= q/2 -> true */
  decodeBit(q: number, d: number): boolean;

  /**
   * LWE encryption (Regev scheme)
   * @param pkA - Public key matrix A (N x n)
   * @param pkB - Public key vector b = A*s + e (length N)
   * @param q - Modulus
   * @param r - Random binary vector (length N)
   * @param m - Message bit to encrypt
   * @returns Ciphertext {u, v}
   */
  lweEncrypt(pkA: IntMatrix, pkB: IntVec, q: number, r: IntVec, m: boolean): LweCiphertext;

  /**
   * LWE decryption (Regev scheme)
   * @param skS - Secret key vector s (length n)
   * @param q - Modulus
   * @param ctU - Ciphertext u component
   * @param ctV - Ciphertext v component
   * @returns Decrypted bit
   */
  lweDecrypt(skS: IntVec, q: number, ctU: IntVec, ctV: number): boolean;
}

// Re-export the global Isabella object with types
export const Lattice: IsabellaModule = (globalThis as any).Isabella;

// Convenience wrapper class
export class LweRegev {
  constructor(
    private readonly q: number,
    private readonly pkA: IntMatrix,
    private readonly pkB: IntVec,
    private readonly skS?: IntVec
  ) {}

  /** Encrypt a single bit */
  encrypt(message: boolean, randomVector: IntVec): LweCiphertext {
    return Lattice.lweEncrypt(this.pkA, this.pkB, this.q, randomVector, message);
  }

  /** Decrypt a ciphertext (requires secret key) */
  decrypt(ciphertext: LweCiphertext): boolean {
    if (!this.skS) {
      throw new Error('Secret key not available for decryption');
    }
    return Lattice.lweDecrypt(this.skS, this.q, ciphertext.u, ciphertext.v);
  }

  /** Get the modulus */
  get modulus(): number {
    return this.q;
  }
}
