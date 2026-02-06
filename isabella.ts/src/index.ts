/**
 * Isabella - Formally Verified Lattice Cryptography
 *
 * This library provides lattice-based cryptographic primitives that have been
 * formally verified in Isabelle/HOL. All functions are extracted from proven-correct
 * specifications and compiled to JavaScript via js_of_ocaml.
 *
 * @packageDocumentation
 *
 * Provenance: Wrapper over js_of_ocaml output generated from
 * Isabelle-exported OCaml Canon modules only.
 */

// Load the js_of_ocaml runtime (sets globalThis.Isabella)
// This import is handled by the runtime loader
import './runtime.cjs';

/** Integer vector type */
export type IntVec = number[];

/** Integer matrix type (list of rows) */
export type IntMatrix = number[][];

/**
 * Raw Isabella module interface (from js_of_ocaml)
 * @internal
 */
interface IsabellaRuntime {
  modCentered(x: number, q: number): number;
  vecMod(v: number[], q: number): number[];
  vecModCentered(v: number[], q: number): number[];
  dist0(q: number, x: number): number;
  encodeBit(q: number, b: boolean): number;
  decodeBit(q: number, x: number): boolean;
  vecAdd(v1: number[], v2: number[]): number[];
  vecSub(v1: number[], v2: number[]): number[];
  scalarMult(c: number, v: number[]): number[];
  vecNeg(v: number[]): number[];
  innerProd(v1: number[], v2: number[]): number;
  matVecMult(mat: number[][], vec: number[]): number[];
  matVecMultMod(mat: number[][], vec: number[], q: number): number[];
  transpose(mat: number[][]): number[][];
  validVec(n: number, v: number[]): boolean;
  validMatrix(m: number, n: number, mat: number[][]): boolean;
  vecConcat(v1: number[], v2: number[]): number[];
  splitVec(n: number, v: number[]): [number[], number[]];
}

// Access the global Isabella object that was set by js_of_ocaml
const Isabella: IsabellaRuntime = (globalThis as any).Isabella;

/**
 * Modular arithmetic operations over Z_q
 *
 * These functions provide operations for working with integers modulo q,
 * with a focus on centered representation used in lattice cryptography.
 */
export namespace Zq {
  /**
   * Centered modular reduction: maps x to (-q/2, q/2]
   *
   * @param x - Value to reduce
   * @param q - Modulus (must be positive)
   * @returns Centered representative
   *
   * @example
   * ```ts
   * Zq.modCentered(7, 5)  // => 2
   * Zq.modCentered(8, 5)  // => -2
   * ```
   */
  export function modCentered(x: number, q: number): number {
    return Isabella.modCentered(x, q);
  }

  /**
   * Apply modular reduction to each element of a vector
   *
   * @param v - Input vector
   * @param q - Modulus
   * @returns Vector with each element reduced mod q
   */
  export function vecMod(v: IntVec, q: number): IntVec {
    return Isabella.vecMod(v, q);
  }

  /**
   * Apply centered modular reduction to each element
   *
   * @param v - Input vector
   * @param q - Modulus
   * @returns Vector with centered representatives
   */
  export function vecModCentered(v: IntVec, q: number): IntVec {
    return Isabella.vecModCentered(v, q);
  }

  /**
   * Distance from zero in Z_q
   *
   * Computes |mod_centered(x, q)|, useful for decryption correctness.
   *
   * @param q - Modulus
   * @param x - Value
   * @returns Non-negative distance
   */
  export function dist0(q: number, x: number): number {
    return Isabella.dist0(q, x);
  }

  /**
   * Encode a bit for LWE encryption
   *
   * - false encodes to 0
   * - true encodes to q/2
   *
   * @param q - Modulus
   * @param bit - Bit to encode
   * @returns Encoded value
   */
  export function encodeBit(q: number, bit: boolean): number {
    return Isabella.encodeBit(q, bit);
  }

  /**
   * Decode a bit from LWE ciphertext
   *
   * Returns true if distance from zero exceeds q/4.
   *
   * @param q - Modulus
   * @param x - Value to decode
   * @returns Decoded bit
   */
  export function decodeBit(q: number, x: number): boolean {
    return Isabella.decodeBit(q, x);
  }

  /**
   * Matrix-vector multiplication modulo q
   *
   * @param mat - Matrix (m × n)
   * @param vec - Vector (length n)
   * @param q - Modulus
   * @returns Result vector (length m) with entries mod q
   */
  export function matVecMultMod(mat: IntMatrix, vec: IntVec, q: number): IntVec {
    return Isabella.matVecMultMod(mat, vec, q);
  }
}

/**
 * Vector and matrix operations
 *
 * Basic linear algebra over integers, matching the Isabelle formalization.
 */
export namespace Vec {
  /**
   * Element-wise vector addition
   *
   * @param v1 - First vector
   * @param v2 - Second vector (same length)
   * @returns Sum vector
   */
  export function add(v1: IntVec, v2: IntVec): IntVec {
    return Isabella.vecAdd(v1, v2);
  }

  /**
   * Element-wise vector subtraction
   *
   * @param v1 - First vector
   * @param v2 - Second vector (same length)
   * @returns Difference vector
   */
  export function sub(v1: IntVec, v2: IntVec): IntVec {
    return Isabella.vecSub(v1, v2);
  }

  /**
   * Scalar multiplication
   *
   * @param c - Scalar
   * @param v - Vector
   * @returns Scaled vector
   */
  export function scale(c: number, v: IntVec): IntVec {
    return Isabella.scalarMult(c, v);
  }

  /**
   * Vector negation
   *
   * @param v - Input vector
   * @returns Negated vector
   */
  export function neg(v: IntVec): IntVec {
    return Isabella.vecNeg(v);
  }

  /**
   * Inner product (dot product)
   *
   * @param v1 - First vector
   * @param v2 - Second vector (same length)
   * @returns Sum of element-wise products
   */
  export function dot(v1: IntVec, v2: IntVec): number {
    return Isabella.innerProd(v1, v2);
  }

  /**
   * Concatenate two vectors
   *
   * @param v1 - First vector
   * @param v2 - Second vector
   * @returns Concatenated vector
   */
  export function concat(v1: IntVec, v2: IntVec): IntVec {
    return Isabella.vecConcat(v1, v2);
  }

  /**
   * Split vector at position n
   *
   * @param n - Split position
   * @param v - Vector to split
   * @returns Tuple of [first n elements, remaining elements]
   */
  export function split(n: number, v: IntVec): [IntVec, IntVec] {
    return Isabella.splitVec(n, v);
  }

  /**
   * Check if vector has given dimension
   *
   * @param n - Expected dimension
   * @param v - Vector to check
   * @returns true if length equals n
   */
  export function isValid(n: number, v: IntVec): boolean {
    return Isabella.validVec(n, v);
  }
}

/**
 * Matrix operations
 */
export namespace Mat {
  /**
   * Matrix-vector multiplication
   *
   * @param mat - Matrix (m × n)
   * @param vec - Vector (length n)
   * @returns Result vector (length m)
   */
  export function vecMult(mat: IntMatrix, vec: IntVec): IntVec {
    return Isabella.matVecMult(mat, vec);
  }

  /**
   * Matrix transpose
   *
   * @param mat - Input matrix
   * @returns Transposed matrix
   */
  export function transpose(mat: IntMatrix): IntMatrix {
    return Isabella.transpose(mat);
  }

  /**
   * Check if matrix has dimensions m × n
   *
   * @param m - Expected rows
   * @param n - Expected columns
   * @param mat - Matrix to check
   * @returns true if dimensions match
   */
  export function isValid(m: number, n: number, mat: IntMatrix): boolean {
    return Isabella.validMatrix(m, n, mat);
  }
}

// Re-export everything for convenience
export { Isabella as runtime };
