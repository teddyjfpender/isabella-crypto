/**
 * FIPS 203 ML-KEM Byte Encoding
 *
 * This module provides byte-level encoding/decoding functions for ML-KEM
 * to enable testing against official NIST ACVP test vectors.
 *
 * FIPS 203 specifies:
 * - ByteEncode_d: Encode d-bit coefficients to bytes
 * - ByteDecode_d: Decode bytes to d-bit coefficients
 * - Compress_d / Decompress_d: Lossy coefficient compression
 *
 * For full ACVP compliance, we also need:
 * - SHAKE-128/256 for PRF/XOF
 * - G and H hash functions (SHA3-512, SHA3-256)
 * - CBD (Centered Binomial Distribution) sampling
 */

// ML-KEM Parameters per FIPS 203
export const ML_KEM_PARAMS = {
  '512': { k: 2, eta1: 3, eta2: 2, du: 10, dv: 4 },
  '768': { k: 3, eta1: 2, eta2: 2, du: 10, dv: 4 },
  '1024': { k: 4, eta1: 2, eta2: 2, du: 11, dv: 5 },
};

// Constants
export const N = 256;  // Polynomial degree
export const Q = 3329; // Modulus

/**
 * ByteEncode_d: Encode integer array to bytes (FIPS 203 Algorithm 4)
 *
 * Encodes d-bit integers into a byte array.
 * Used for serializing polynomial coefficients.
 *
 * @param coeffs Array of 256 integers in [0, 2^d)
 * @param d Number of bits per coefficient
 * @returns Byte array of length 32*d
 */
export function byteEncode(coeffs: number[], d: number): Uint8Array {
  if (coeffs.length !== N) {
    throw new Error(`Expected ${N} coefficients, got ${coeffs.length}`);
  }

  const totalBits = N * d;
  const bytes = new Uint8Array(totalBits / 8);

  let bitPos = 0;
  for (const coeff of coeffs) {
    // Ensure coefficient is in range
    const c = coeff & ((1 << d) - 1);

    // Write d bits starting at bitPos
    for (let b = 0; b < d; b++) {
      const bit = (c >> b) & 1;
      const byteIdx = Math.floor(bitPos / 8);
      const bitIdx = bitPos % 8;
      bytes[byteIdx] |= bit << bitIdx;
      bitPos++;
    }
  }

  return bytes;
}

/**
 * ByteDecode_d: Decode bytes to integer array (FIPS 203 Algorithm 5)
 *
 * Decodes a byte array into d-bit integers.
 *
 * @param bytes Byte array of length 32*d
 * @param d Number of bits per coefficient
 * @returns Array of 256 integers
 */
export function byteDecode(bytes: Uint8Array, d: number): number[] {
  const expectedLen = (N * d) / 8;
  if (bytes.length !== expectedLen) {
    throw new Error(`Expected ${expectedLen} bytes, got ${bytes.length}`);
  }

  const coeffs: number[] = new Array(N);
  let bitPos = 0;

  for (let i = 0; i < N; i++) {
    let coeff = 0;
    for (let b = 0; b < d; b++) {
      const byteIdx = Math.floor(bitPos / 8);
      const bitIdx = bitPos % 8;
      const bit = (bytes[byteIdx] >> bitIdx) & 1;
      coeff |= bit << b;
      bitPos++;
    }
    coeffs[i] = coeff;
  }

  return coeffs;
}

/**
 * Compress_d: Lossy compression of coefficient (FIPS 203 Section 4.2.1)
 *
 * Maps [0, q) to [0, 2^d) with rounding.
 */
export function compress(x: number, d: number): number {
  // compress_d(x) = round(2^d * x / q) mod 2^d
  const scaled = (x * (1 << d) + Math.floor(Q / 2)) / Q;
  return Math.floor(scaled) & ((1 << d) - 1);
}

/**
 * Decompress_d: Decompress coefficient (FIPS 203 Section 4.2.1)
 *
 * Maps [0, 2^d) back to [0, q) (approximate inverse of compress).
 */
export function decompress(y: number, d: number): number {
  // decompress_d(y) = round(q * y / 2^d)
  return Math.round((Q * y) / (1 << d));
}

/**
 * Encode polynomial with 12-bit coefficients (for public key t)
 */
export function encodePolynomial12(poly: number[]): Uint8Array {
  return byteEncode(poly.map(c => c % Q), 12);
}

/**
 * Decode polynomial with 12-bit coefficients
 */
export function decodePolynomial12(bytes: Uint8Array): number[] {
  return byteDecode(bytes, 12);
}

/**
 * Encode compressed polynomial (for ciphertext)
 */
export function encodeCompressed(poly: number[], d: number): Uint8Array {
  const compressed = poly.map(c => compress(c, d));
  return byteEncode(compressed, d);
}

/**
 * Decode and decompress polynomial (for ciphertext)
 */
export function decodeDecompressed(bytes: Uint8Array, d: number): number[] {
  const compressed = byteDecode(bytes, d);
  return compressed.map(c => decompress(c, d));
}

/**
 * Encode public key (encapsulation key ek)
 *
 * ek = ByteEncode_12(t̂[0]) || ... || ByteEncode_12(t̂[k-1]) || ρ
 *
 * Where:
 * - t̂ is the public vector (k polynomials in NTT domain)
 * - ρ is the 32-byte seed for matrix A
 */
export function encodePublicKey(
  t_hat: number[][],  // k polynomials
  rho: Uint8Array     // 32-byte seed
): Uint8Array {
  const k = t_hat.length;
  const polyBytes = 384; // 256 * 12 / 8
  const result = new Uint8Array(k * polyBytes + 32);

  for (let i = 0; i < k; i++) {
    const encoded = encodePolynomial12(t_hat[i]);
    result.set(encoded, i * polyBytes);
  }
  result.set(rho, k * polyBytes);

  return result;
}

/**
 * Decode public key
 */
export function decodePublicKey(
  ek: Uint8Array,
  k: number
): { t_hat: number[][]; rho: Uint8Array } {
  const polyBytes = 384;
  const t_hat: number[][] = [];

  for (let i = 0; i < k; i++) {
    const polyData = ek.slice(i * polyBytes, (i + 1) * polyBytes);
    t_hat.push(decodePolynomial12(polyData));
  }

  const rho = ek.slice(k * polyBytes, k * polyBytes + 32);

  return { t_hat, rho };
}

/**
 * Calculate expected key sizes for ML-KEM variants
 */
export function getKeySizes(variant: '512' | '768' | '1024'): {
  ekLen: number;  // Encapsulation key length
  dkLen: number;  // Decapsulation key length
  ctLen: number;  // Ciphertext length
} {
  const { k, du, dv } = ML_KEM_PARAMS[variant];

  // ek = k * 384 + 32 (k polynomials + seed)
  const ekLen = k * 384 + 32;

  // dk = k * 384 + ekLen + 32 + 32 (s + ek + H(ek) + z)
  const dkLen = k * 384 + ekLen + 32 + 32;

  // ct = k * 32 * du + 32 * dv (u + v compressed)
  const ctLen = k * 32 * du + 32 * dv;

  return { ekLen, dkLen, ctLen };
}

// Verify key sizes match FIPS 203 Table 2
export const EXPECTED_SIZES = {
  '512': { ekLen: 800, dkLen: 1632, ctLen: 768 },
  '768': { ekLen: 1184, dkLen: 2400, ctLen: 1088 },
  '1024': { ekLen: 1568, dkLen: 3168, ctLen: 1568 },
};

/**
 * TODO for full FIPS 203 compliance:
 *
 * 1. Implement SHAKE-128 and SHAKE-256 (XOF)
 *    - Used for PRF, XOF, and matrix generation
 *
 * 2. Implement G (SHA3-512) and H (SHA3-256)
 *    - Used for key derivation and hashing
 *
 * 3. Implement SampleNTT (Algorithm 6)
 *    - Generate matrix A from seed ρ using SHAKE-128
 *
 * 4. Implement SamplePolyCBD_η (Algorithm 7)
 *    - Sample from centered binomial distribution
 *
 * 5. Implement K-PKE.KeyGen, K-PKE.Encrypt, K-PKE.Decrypt
 *    - Core PKE operations
 *
 * 6. Implement ML-KEM.KeyGen, ML-KEM.Encaps, ML-KEM.Decaps
 *    - Full KEM with implicit rejection
 */
