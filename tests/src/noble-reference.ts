/**
 * Noble Post-Quantum Reference Implementation
 *
 * This module wraps noble-post-quantum to generate test vectors
 * and provide reference implementations for validation.
 */

import { ml_kem512, ml_kem768, ml_kem1024 } from '@noble/post-quantum/ml-kem';
import { ml_dsa44, ml_dsa65, ml_dsa87 } from '@noble/post-quantum/ml-dsa';

// Re-export the ML-KEM implementations
export { ml_kem512, ml_kem768, ml_kem1024 };

// Re-export the ML-DSA implementations
export { ml_dsa44, ml_dsa65, ml_dsa87 };

// Type definitions for ML-KEM
export interface MLKemKeyPair {
  publicKey: Uint8Array;
  secretKey: Uint8Array;
}

export interface MLKemEncapsulation {
  cipherText: Uint8Array;
  sharedSecret: Uint8Array;
}

export type MLKemVariant = typeof ml_kem512 | typeof ml_kem768 | typeof ml_kem1024;

/**
 * Generate a key pair using the specified ML-KEM variant
 */
export function generateKeyPair(variant: MLKemVariant, seed?: Uint8Array): MLKemKeyPair {
  // Generate random seed if not provided
  const actualSeed = seed ?? crypto.getRandomValues(new Uint8Array(64));
  const keys = variant.keygen(actualSeed);
  return {
    publicKey: keys.publicKey,
    secretKey: keys.secretKey,
  };
}

/**
 * Encapsulate a shared secret using the public key
 */
export function encapsulate(variant: MLKemVariant, publicKey: Uint8Array): MLKemEncapsulation {
  const result = variant.encapsulate(publicKey);
  return {
    cipherText: result.cipherText,
    sharedSecret: result.sharedSecret,
  };
}

/**
 * Decapsulate a shared secret using the secret key and ciphertext
 */
export function decapsulate(variant: MLKemVariant, cipherText: Uint8Array, secretKey: Uint8Array): Uint8Array {
  return variant.decapsulate(cipherText, secretKey);
}

/**
 * Generate test vectors for all ML-KEM variants
 */
export function generateTestVectors(count: number = 10): TestVector[] {
  const vectors: TestVector[] = [];
  const variants = [
    { name: 'ML-KEM-512', impl: ml_kem512 },
    { name: 'ML-KEM-768', impl: ml_kem768 },
    { name: 'ML-KEM-1024', impl: ml_kem1024 },
  ];

  for (const { name, impl } of variants) {
    for (let i = 0; i < count; i++) {
      const keyPair = generateKeyPair(impl);
      const encap = encapsulate(impl, keyPair.publicKey);
      const decapSecret = decapsulate(impl, encap.cipherText, keyPair.secretKey);

      vectors.push({
        variant: name,
        index: i,
        publicKey: Buffer.from(keyPair.publicKey).toString('hex'),
        secretKey: Buffer.from(keyPair.secretKey).toString('hex'),
        cipherText: Buffer.from(encap.cipherText).toString('hex'),
        sharedSecret: Buffer.from(encap.sharedSecret).toString('hex'),
        decapsulatedSecret: Buffer.from(decapSecret).toString('hex'),
        valid: Buffer.from(encap.sharedSecret).equals(Buffer.from(decapSecret)),
      });
    }
  }

  return vectors;
}

export interface TestVector {
  variant: string;
  index: number;
  publicKey: string;
  secretKey: string;
  cipherText: string;
  sharedSecret: string;
  decapsulatedSecret: string;
  valid: boolean;
}

// ============================================
// ML-DSA (Dilithium) Types and Functions
// ============================================

export type MLDsaVariant = typeof ml_dsa44 | typeof ml_dsa65 | typeof ml_dsa87;

export interface MLDsaKeyPair {
  publicKey: Uint8Array;
  secretKey: Uint8Array;
}

export interface MLDsaSignature {
  signature: Uint8Array;
}

/**
 * Generate an ML-DSA key pair
 */
export function generateDsaKeyPair(variant: MLDsaVariant, seed?: Uint8Array): MLDsaKeyPair {
  // Generate random seed if not provided
  const actualSeed = seed ?? crypto.getRandomValues(new Uint8Array(32));
  const keys = variant.keygen(actualSeed);
  return {
    publicKey: keys.publicKey,
    secretKey: keys.secretKey,
  };
}

/**
 * Sign a message using ML-DSA
 */
export function signMessage(variant: MLDsaVariant, secretKey: Uint8Array, message: Uint8Array): Uint8Array {
  return variant.sign(secretKey, message);
}

/**
 * Verify a signature using ML-DSA
 */
export function verifySignature(variant: MLDsaVariant, publicKey: Uint8Array, message: Uint8Array, signature: Uint8Array): boolean {
  return variant.verify(publicKey, message, signature);
}

/**
 * ML-DSA test vector
 */
export interface MLDsaTestVector {
  variant: string;
  index: number;
  publicKey: string;
  secretKey: string;
  message: string;
  signature: string;
  valid: boolean;
}

/**
 * Generate test vectors for all ML-DSA variants
 */
export function generateDsaTestVectors(count: number = 5): MLDsaTestVector[] {
  const vectors: MLDsaTestVector[] = [];
  const variants = [
    { name: 'ML-DSA-44', impl: ml_dsa44 },
    { name: 'ML-DSA-65', impl: ml_dsa65 },
    { name: 'ML-DSA-87', impl: ml_dsa87 },
  ];

  for (const { name, impl } of variants) {
    for (let i = 0; i < count; i++) {
      const keyPair = generateDsaKeyPair(impl);
      const message = new Uint8Array(32);
      // Fill with deterministic test data
      for (let j = 0; j < 32; j++) {
        message[j] = (i * 17 + j * 31) % 256;
      }

      const signature = signMessage(impl, keyPair.secretKey, message);
      const isValid = verifySignature(impl, keyPair.publicKey, message, signature);

      vectors.push({
        variant: name,
        index: i,
        publicKey: Buffer.from(keyPair.publicKey).toString('hex'),
        secretKey: Buffer.from(keyPair.secretKey).toString('hex'),
        message: Buffer.from(message).toString('hex'),
        signature: Buffer.from(signature).toString('hex'),
        valid: isValid,
      });
    }
  }

  return vectors;
}

/**
 * FIPS 204 expected key/signature sizes
 */
export const MLDSA_EXPECTED_SIZES = {
  '44': {
    publicKeyLen: 1312,
    secretKeyLen: 2560,
    signatureLen: 2420,
  },
  '65': {
    publicKeyLen: 1952,
    secretKeyLen: 4032,
    signatureLen: 3309,
  },
  '87': {
    publicKeyLen: 2592,
    secretKeyLen: 4896,
    signatureLen: 4627,
  },
} as const;

/**
 * Utility to convert hex string to Uint8Array
 */
export function hexToBytes(hex: string): Uint8Array {
  const bytes = new Uint8Array(hex.length / 2);
  for (let i = 0; i < bytes.length; i++) {
    bytes[i] = parseInt(hex.substr(i * 2, 2), 16);
  }
  return bytes;
}

/**
 * Utility to convert Uint8Array to hex string
 */
export function bytesToHex(bytes: Uint8Array): string {
  return Buffer.from(bytes).toString('hex');
}
