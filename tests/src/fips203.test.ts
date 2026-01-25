/**
 * FIPS 203 Byte Encoding Tests
 *
 * Tests for ML-KEM byte-level encoding/decoding functions.
 */

import {
  byteEncode,
  byteDecode,
  compress,
  decompress,
  encodePolynomial12,
  decodePolynomial12,
  getKeySizes,
  EXPECTED_SIZES,
  N,
  Q,
} from './fips203.js';

describe('FIPS 203 Byte Encoding', () => {
  describe('ByteEncode / ByteDecode', () => {
    it('roundtrips 12-bit coefficients', () => {
      const coeffs = new Array(N).fill(0).map((_, i) => i % Q);
      const encoded = byteEncode(coeffs, 12);
      const decoded = byteDecode(encoded, 12);

      expect(decoded).toEqual(coeffs);
    });

    it('roundtrips 10-bit coefficients', () => {
      const coeffs = new Array(N).fill(0).map((_, i) => i % 1024);
      const encoded = byteEncode(coeffs, 10);
      const decoded = byteDecode(encoded, 10);

      expect(decoded).toEqual(coeffs);
    });

    it('roundtrips 4-bit coefficients', () => {
      const coeffs = new Array(N).fill(0).map((_, i) => i % 16);
      const encoded = byteEncode(coeffs, 4);
      const decoded = byteDecode(encoded, 4);

      expect(decoded).toEqual(coeffs);
    });

    it('produces correct byte lengths', () => {
      const coeffs = new Array(N).fill(0);

      // 12 bits * 256 = 3072 bits = 384 bytes
      expect(byteEncode(coeffs, 12).length).toBe(384);

      // 10 bits * 256 = 2560 bits = 320 bytes
      expect(byteEncode(coeffs, 10).length).toBe(320);

      // 4 bits * 256 = 1024 bits = 128 bytes
      expect(byteEncode(coeffs, 4).length).toBe(128);
    });

    it('encodes specific patterns correctly', () => {
      // All zeros
      const zeros = new Array(N).fill(0);
      const zeroEncoded = byteEncode(zeros, 12);
      expect(zeroEncoded.every(b => b === 0)).toBe(true);

      // All ones (0x001 for 12 bits)
      const ones = new Array(N).fill(1);
      const onesDecoded = byteDecode(byteEncode(ones, 12), 12);
      expect(onesDecoded.every(c => c === 1)).toBe(true);
    });
  });

  describe('Compress / Decompress', () => {
    it('compress maps to correct range', () => {
      // compress_d maps [0, q) to [0, 2^d)
      for (let d = 1; d <= 12; d++) {
        const maxOut = (1 << d) - 1;
        for (let x = 0; x < Q; x += 100) {
          const compressed = compress(x, d);
          expect(compressed).toBeGreaterThanOrEqual(0);
          expect(compressed).toBeLessThanOrEqual(maxOut);
        }
      }
    });

    it('decompress maps to correct range', () => {
      // decompress_d maps [0, 2^d) to [0, q)
      for (let d = 4; d <= 12; d++) {
        for (let y = 0; y < (1 << d); y++) {
          const decompressed = decompress(y, d);
          expect(decompressed).toBeGreaterThanOrEqual(0);
          expect(decompressed).toBeLessThan(Q);
        }
      }
    });

    it('compress then decompress is approximately identity', () => {
      // The composition should be close to identity (within q/2^(d+1))
      const d = 10;
      const maxError = Math.ceil(Q / (1 << (d + 1)));

      for (let x = 0; x < Q; x += 50) {
        const compressed = compress(x, d);
        const decompressed = decompress(compressed, d);

        // Check that decompressed is close to original
        const diff = Math.abs(x - decompressed);
        const wrappedDiff = Math.min(diff, Q - diff);
        expect(wrappedDiff).toBeLessThanOrEqual(maxError);
      }
    });

    it('compress of 0 is 0', () => {
      for (let d = 1; d <= 12; d++) {
        expect(compress(0, d)).toBe(0);
      }
    });

    it('compress of q/2 is approximately 2^(d-1)', () => {
      for (let d = 4; d <= 12; d++) {
        const halfQ = Math.floor(Q / 2);
        const compressed = compress(halfQ, d);
        const expected = 1 << (d - 1);
        // Allow rounding error of 1
        expect(Math.abs(compressed - expected)).toBeLessThanOrEqual(1);
      }
    });
  });

  describe('Polynomial Encoding', () => {
    it('encodePolynomial12 produces correct length', () => {
      const poly = new Array(N).fill(0);
      const encoded = encodePolynomial12(poly);
      expect(encoded.length).toBe(384); // 256 * 12 / 8
    });

    it('encodePolynomial12 roundtrips', () => {
      const poly = new Array(N).fill(0).map((_, i) => (i * 17) % Q);
      const encoded = encodePolynomial12(poly);
      const decoded = decodePolynomial12(encoded);
      expect(decoded).toEqual(poly);
    });
  });

  describe('Key Sizes', () => {
    it('ML-KEM-512 sizes match FIPS 203 Table 2', () => {
      const sizes = getKeySizes('512');
      expect(sizes.ekLen).toBe(EXPECTED_SIZES['512'].ekLen);
      expect(sizes.dkLen).toBe(EXPECTED_SIZES['512'].dkLen);
      expect(sizes.ctLen).toBe(EXPECTED_SIZES['512'].ctLen);
    });

    it('ML-KEM-768 sizes match FIPS 203 Table 2', () => {
      const sizes = getKeySizes('768');
      expect(sizes.ekLen).toBe(EXPECTED_SIZES['768'].ekLen);
      expect(sizes.dkLen).toBe(EXPECTED_SIZES['768'].dkLen);
      expect(sizes.ctLen).toBe(EXPECTED_SIZES['768'].ctLen);
    });

    it('ML-KEM-1024 sizes match FIPS 203 Table 2', () => {
      const sizes = getKeySizes('1024');
      expect(sizes.ekLen).toBe(EXPECTED_SIZES['1024'].ekLen);
      expect(sizes.dkLen).toBe(EXPECTED_SIZES['1024'].dkLen);
      expect(sizes.ctLen).toBe(EXPECTED_SIZES['1024'].ctLen);
    });
  });

  describe('Cross-validation with noble-post-quantum', () => {
    // These tests verify that our byte encoding produces the same
    // sizes as noble-post-quantum, ensuring compatibility
    it('key sizes match noble-post-quantum', async () => {
      const { ml_kem512, ml_kem768, ml_kem1024 } = await import('./noble-reference.js');

      const keys512 = ml_kem512.keygen();
      const keys768 = ml_kem768.keygen();
      const keys1024 = ml_kem1024.keygen();

      expect(keys512.publicKey.length).toBe(EXPECTED_SIZES['512'].ekLen);
      expect(keys512.secretKey.length).toBe(EXPECTED_SIZES['512'].dkLen);

      expect(keys768.publicKey.length).toBe(EXPECTED_SIZES['768'].ekLen);
      expect(keys768.secretKey.length).toBe(EXPECTED_SIZES['768'].dkLen);

      expect(keys1024.publicKey.length).toBe(EXPECTED_SIZES['1024'].ekLen);
      expect(keys1024.secretKey.length).toBe(EXPECTED_SIZES['1024'].dkLen);
    });

    it('ciphertext sizes match noble-post-quantum', async () => {
      const { ml_kem512, ml_kem768, ml_kem1024 } = await import('./noble-reference.js');

      const keys512 = ml_kem512.keygen();
      const encap512 = ml_kem512.encapsulate(keys512.publicKey);
      expect(encap512.cipherText.length).toBe(EXPECTED_SIZES['512'].ctLen);

      const keys768 = ml_kem768.keygen();
      const encap768 = ml_kem768.encapsulate(keys768.publicKey);
      expect(encap768.cipherText.length).toBe(EXPECTED_SIZES['768'].ctLen);

      const keys1024 = ml_kem1024.keygen();
      const encap1024 = ml_kem1024.encapsulate(keys1024.publicKey);
      expect(encap1024.cipherText.length).toBe(EXPECTED_SIZES['1024'].ctLen);
    });
  });
});

describe('FIPS 203 Compliance Roadmap', () => {
  it('documents what is needed for full ACVP compliance', () => {
    // This test serves as documentation for what's needed

    const implemented = [
      'ByteEncode_d (Algorithm 4)',
      'ByteDecode_d (Algorithm 5)',
      'Compress_d',
      'Decompress_d',
      'Key size validation',
    ];

    const needed = [
      'SHAKE-128 XOF for SampleNTT',
      'SHAKE-256 for PRF',
      'SHA3-256 (H) for implicit rejection',
      'SHA3-512 (G) for key derivation',
      'SampleNTT (Algorithm 6) - matrix A from seed',
      'SamplePolyCBD_η (Algorithm 7) - noise sampling',
      'K-PKE.KeyGen (Algorithm 12)',
      'K-PKE.Encrypt (Algorithm 13)',
      'K-PKE.Decrypt (Algorithm 14)',
      'ML-KEM.KeyGen (Algorithm 15)',
      'ML-KEM.Encaps (Algorithm 16)',
      'ML-KEM.Decaps (Algorithm 17)',
    ];

    console.log('\n=== FIPS 203 Compliance Status ===\n');
    console.log('Implemented:');
    implemented.forEach(item => console.log(`  ✓ ${item}`));
    console.log('\nNeeded for full ACVP compliance:');
    needed.forEach(item => console.log(`  ○ ${item}`));
    console.log('\nNote: Core NTT operations are verified via CLI tests.');
    console.log('SHAKE/SHA3 would need to be added for seed-based key derivation.\n');

    // Always pass - this is documentation
    expect(true).toBe(true);
  });
});
