/**
 * Noble Post-Quantum Reference Implementation
 *
 * This module wraps noble-post-quantum to generate test vectors
 * and provide reference implementations for validation.
 */

import { ml_kem512, ml_kem768, ml_kem1024 } from '@noble/post-quantum/ml-kem';

// Re-export the ML-KEM implementations
export { ml_kem512, ml_kem768, ml_kem1024 };

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
  const keys = variant.keygen(seed);
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
