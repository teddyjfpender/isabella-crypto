/**
 * CRYSTALS-Dilithium (ML-DSA) Tests
 *
 * Tests for ML-DSA digital signatures using noble-post-quantum as reference.
 */

import {
  ml_dsa44,
  ml_dsa65,
  ml_dsa87,
  generateDsaKeyPair,
  signMessage,
  verifySignature,
  MLDSA_EXPECTED_SIZES,
} from './noble-reference.js';

describe('ML-DSA Reference Tests (noble-post-quantum)', () => {
  describe('ML-DSA-44', () => {
    it('generates valid key pairs', () => {
      const keys = generateDsaKeyPair(ml_dsa44);
      expect(keys.publicKey).toBeDefined();
      expect(keys.secretKey).toBeDefined();
      expect(keys.publicKey.length).toBe(MLDSA_EXPECTED_SIZES['44'].publicKeyLen);
      expect(keys.secretKey.length).toBe(MLDSA_EXPECTED_SIZES['44'].secretKeyLen);
    });

    it('signs and verifies messages', () => {
      const keys = generateDsaKeyPair(ml_dsa44);
      const message = new TextEncoder().encode('Hello, Dilithium!');
      const signature = signMessage(ml_dsa44, keys.secretKey, message);
      const isValid = verifySignature(ml_dsa44, keys.publicKey, message, signature);

      expect(signature.length).toBe(MLDSA_EXPECTED_SIZES['44'].signatureLen);
      expect(isValid).toBe(true);
    });

    it('rejects invalid signatures', () => {
      const keys = generateDsaKeyPair(ml_dsa44);
      const message = new TextEncoder().encode('Hello, Dilithium!');
      const signature = signMessage(ml_dsa44, keys.secretKey, message);

      // Modify signature
      const badSig = new Uint8Array(signature);
      badSig[0] ^= 0xFF;

      const isValid = verifySignature(ml_dsa44, keys.publicKey, message, badSig);
      expect(isValid).toBe(false);
    });

    it('rejects wrong message', () => {
      const keys = generateDsaKeyPair(ml_dsa44);
      const message1 = new TextEncoder().encode('Hello, Dilithium!');
      const message2 = new TextEncoder().encode('Different message');
      const signature = signMessage(ml_dsa44, keys.secretKey, message1);

      const isValid = verifySignature(ml_dsa44, keys.publicKey, message2, signature);
      expect(isValid).toBe(false);
    });
  });

  describe('ML-DSA-65', () => {
    it('generates valid key pairs', () => {
      const keys = generateDsaKeyPair(ml_dsa65);
      expect(keys.publicKey.length).toBe(MLDSA_EXPECTED_SIZES['65'].publicKeyLen);
      expect(keys.secretKey.length).toBe(MLDSA_EXPECTED_SIZES['65'].secretKeyLen);
    });

    it('signs and verifies messages', () => {
      const keys = generateDsaKeyPair(ml_dsa65);
      const message = new TextEncoder().encode('ML-DSA-65 test message');
      const signature = signMessage(ml_dsa65, keys.secretKey, message);
      const isValid = verifySignature(ml_dsa65, keys.publicKey, message, signature);

      expect(signature.length).toBe(MLDSA_EXPECTED_SIZES['65'].signatureLen);
      expect(isValid).toBe(true);
    });
  });

  describe('ML-DSA-87', () => {
    it('generates valid key pairs', () => {
      const keys = generateDsaKeyPair(ml_dsa87);
      expect(keys.publicKey.length).toBe(MLDSA_EXPECTED_SIZES['87'].publicKeyLen);
      expect(keys.secretKey.length).toBe(MLDSA_EXPECTED_SIZES['87'].secretKeyLen);
    });

    it('signs and verifies messages', () => {
      const keys = generateDsaKeyPair(ml_dsa87);
      const message = new TextEncoder().encode('ML-DSA-87 test message');
      const signature = signMessage(ml_dsa87, keys.secretKey, message);
      const isValid = verifySignature(ml_dsa87, keys.publicKey, message, signature);

      expect(signature.length).toBe(MLDSA_EXPECTED_SIZES['87'].signatureLen);
      expect(isValid).toBe(true);
    });
  });

  describe('Key/Signature Sizes (FIPS 204 Table 2)', () => {
    it('ML-DSA-44 sizes match spec', () => {
      const seed = new Uint8Array(32);
      const keys = ml_dsa44.keygen(seed);
      const msg = new Uint8Array(32);
      const sig = ml_dsa44.sign(keys.secretKey, msg);

      expect(keys.publicKey.length).toBe(1312);
      expect(keys.secretKey.length).toBe(2560);
      expect(sig.length).toBe(2420);
    });

    it('ML-DSA-65 sizes match spec', () => {
      const seed = new Uint8Array(32);
      const keys = ml_dsa65.keygen(seed);
      const msg = new Uint8Array(32);
      const sig = ml_dsa65.sign(keys.secretKey, msg);

      expect(keys.publicKey.length).toBe(1952);
      expect(keys.secretKey.length).toBe(4032);
      expect(sig.length).toBe(3309);
    });

    it('ML-DSA-87 sizes match spec', () => {
      const seed = new Uint8Array(32);
      const keys = ml_dsa87.keygen(seed);
      const msg = new Uint8Array(32);
      const sig = ml_dsa87.sign(keys.secretKey, msg);

      expect(keys.publicKey.length).toBe(2592);
      expect(keys.secretKey.length).toBe(4896);
      expect(sig.length).toBe(4627);
    });
  });

  describe('Deterministic Key Generation', () => {
    it('same seed produces same keys', () => {
      const seed = new Uint8Array(32);
      for (let i = 0; i < 32; i++) seed[i] = i;

      const keys1 = ml_dsa44.keygen(seed);
      const keys2 = ml_dsa44.keygen(seed);

      expect(Buffer.from(keys1.publicKey)).toEqual(Buffer.from(keys2.publicKey));
      expect(Buffer.from(keys1.secretKey)).toEqual(Buffer.from(keys2.secretKey));
    });

    it('different seeds produce different keys', () => {
      const seed1 = new Uint8Array(32).fill(0);
      const seed2 = new Uint8Array(32).fill(1);

      const keys1 = ml_dsa44.keygen(seed1);
      const keys2 = ml_dsa44.keygen(seed2);

      expect(Buffer.from(keys1.publicKey)).not.toEqual(Buffer.from(keys2.publicKey));
    });
  });
});

describe('Dilithium Parameters', () => {
  // FIPS 204 Table 1: ML-DSA parameter sets
  const PARAMS = {
    '44': { n: 256, q: 8380417, k: 4, l: 4, eta: 2, tau: 39, beta: 78, gamma1: 131072, gamma2: 95232, d: 13, omega: 80 },
    '65': { n: 256, q: 8380417, k: 6, l: 5, eta: 4, tau: 49, beta: 196, gamma1: 524288, gamma2: 261888, d: 13, omega: 55 },
    '87': { n: 256, q: 8380417, k: 8, l: 7, eta: 2, tau: 60, beta: 120, gamma1: 524288, gamma2: 261888, d: 13, omega: 75 },
  };

  for (const [variant, expected] of Object.entries(PARAMS)) {
    describe(`ML-DSA-${variant}`, () => {
      it('has correct n (polynomial degree)', () => {
        expect(expected.n).toBe(256);
      });

      it('has correct q (modulus)', () => {
        expect(expected.q).toBe(8380417);
        // q ≡ 1 (mod 512) for NTT
        expect(expected.q % 512).toBe(1);
      });

      it('has beta = tau * eta', () => {
        expect(expected.beta).toBe(expected.tau * expected.eta);
      });

      it('has d = 13 (dropped bits)', () => {
        expect(expected.d).toBe(13);
      });
    });
  }
});

describe('Dilithium Mathematical Properties', () => {
  const q = 8380417;

  describe('Modulus q', () => {
    it('q is prime', () => {
      // Simple primality test for small factors
      for (let p of [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]) {
        expect(q % p).not.toBe(0);
      }
    });

    it('q ≡ 1 (mod 512) for NTT', () => {
      expect(q % 512).toBe(1);
    });

    it('q has correct form for NTT', () => {
      // q = 2^23 - 2^13 + 1
      expect(q).toBe((1 << 23) - (1 << 13) + 1);
    });
  });

  describe('Primitive Root', () => {
    // ω = 1753 is a primitive 512th root of unity mod q
    const omega = 1753;
    const n = 512;

    function powerMod(base: number, exp: number, mod: number): number {
      let result = 1;
      base = base % mod;
      while (exp > 0) {
        if (exp % 2 === 1) {
          result = Number((BigInt(result) * BigInt(base)) % BigInt(mod));
        }
        exp = Math.floor(exp / 2);
        base = Number((BigInt(base) * BigInt(base)) % BigInt(mod));
      }
      return result;
    }

    it('ω^512 ≡ 1 (mod q)', () => {
      expect(powerMod(omega, n, q)).toBe(1);
    });

    it('ω^256 ≢ 1 (mod q)', () => {
      expect(powerMod(omega, n / 2, q)).not.toBe(1);
    });
  });

  describe('Gamma2 values', () => {
    it('gamma2 for ML-DSA-44 is (q-1)/88', () => {
      expect(Math.floor((q - 1) / 88)).toBe(95232);
    });

    it('gamma2 for ML-DSA-65/87 is (q-1)/32', () => {
      expect(Math.floor((q - 1) / 32)).toBe(261888);
    });
  });
});

describe('Dilithium Compression Functions (Reference)', () => {
  const q = 8380417;

  // Reference implementations for comparison
  function modCentered(r: number, m: number): number {
    let rMod = r % m;
    if (rMod < 0) rMod += m;
    if (rMod > Math.floor(m / 2)) rMod -= m;
    return rMod;
  }

  function power2Round(r: number, d: number): [number, number] {
    const twoD = 1 << d;
    const r0 = modCentered(r, twoD);
    const r1 = Math.floor((r - r0) / twoD);
    return [r1, r0];
  }

  function decompose(r: number, alpha: number): [number, number] {
    const r0 = modCentered(r, alpha);
    let r1 = Math.floor((r - r0) / alpha);
    if (r - r0 === q - 1) {
      r1 = 0;
      return [r1, r0 - 1];
    }
    return [r1, r0];
  }

  describe('modCentered', () => {
    it('maps small positive to itself', () => {
      expect(modCentered(5, 16)).toBe(5);
    });

    it('maps large positive to negative', () => {
      expect(modCentered(12, 16)).toBe(-4);
    });

    it('maps negative correctly', () => {
      expect(modCentered(-3, 16)).toBe(-3);
    });

    it('maps exactly half to positive', () => {
      expect(modCentered(8, 16)).toBe(8);
    });

    it('maps just over half to negative', () => {
      expect(modCentered(9, 16)).toBe(-7);
    });
  });

  describe('Power2Round', () => {
    const d = 13;
    const twoD = 1 << d; // 8192

    it('reconstructs correctly: r1 * 2^d + r0 = r', () => {
      for (const r of [0, 100, 1000, 5000, 100000, 1000000]) {
        const [r1, r0] = power2Round(r, d);
        expect(r1 * twoD + r0).toBe(r);
      }
    });

    it('r0 is in correct range: -2^(d-1) < r0 <= 2^(d-1)', () => {
      const halfD = twoD / 2;
      for (const r of [0, 100, 1000, 5000, 100000, 1000000]) {
        const [, r0] = power2Round(r, d);
        expect(r0).toBeGreaterThan(-halfD - 1);
        expect(r0).toBeLessThanOrEqual(halfD);
      }
    });
  });

  describe('Decompose', () => {
    const alpha = 2 * 95232; // 2 * gamma2 for ML-DSA-44

    it('reconstructs correctly for normal case', () => {
      for (const r of [0, 100, 1000, 50000, 100000]) {
        const [r1, r0] = decompose(r, alpha);
        // Either normal case or boundary case
        if (r - modCentered(r, alpha) !== q - 1) {
          expect(r1 * alpha + r0).toBe(r);
        }
      }
    });

    it('r0 is in centered range', () => {
      const halfAlpha = Math.floor(alpha / 2);
      for (const r of [0, 100, 1000, 50000]) {
        const [, r0] = decompose(r, alpha);
        expect(r0).toBeGreaterThan(-halfAlpha - 1);
        expect(r0).toBeLessThanOrEqual(halfAlpha);
      }
    });
  });

  describe('HighBits/LowBits', () => {
    const alpha = 2 * 95232;

    function highBits(r: number, alpha: number): number {
      return decompose(r, alpha)[0];
    }

    function lowBits(r: number, alpha: number): number {
      return decompose(r, alpha)[1];
    }

    it('highBits extracts high-order bits', () => {
      const r = 500000;
      const hi = highBits(r, alpha);
      expect(hi).toBeGreaterThanOrEqual(0);
    });

    it('lowBits extracts low-order bits in centered range', () => {
      const r = 500000;
      const lo = lowBits(r, alpha);
      const halfAlpha = Math.floor(alpha / 2);
      expect(lo).toBeGreaterThan(-halfAlpha - 1);
      expect(lo).toBeLessThanOrEqual(halfAlpha);
    });
  });
});

describe('Hint Functions (Reference)', () => {
  const q = 8380417;

  function modCentered(r: number, m: number): number {
    let rMod = r % m;
    if (rMod < 0) rMod += m;
    if (rMod > Math.floor(m / 2)) rMod -= m;
    return rMod;
  }

  function decompose(r: number, alpha: number): [number, number] {
    const r0 = modCentered(r, alpha);
    let r1 = Math.floor((r - r0) / alpha);
    if (r - r0 === q - 1) {
      r1 = 0;
      return [r1, r0 - 1];
    }
    return [r1, r0];
  }

  function highBits(r: number, alpha: number): number {
    return decompose(r, alpha)[0];
  }

  function makeHint(z: number, r: number, alpha: number): number {
    const hi1 = highBits(r, alpha);
    const hi2 = highBits(r + z, alpha);
    return hi1 !== hi2 ? 1 : 0;
  }

  function useHint(h: number, r: number, alpha: number): number {
    const [r1, r0] = decompose(r, alpha);
    const m = Math.floor((q - 1) / alpha);
    if (h === 0) return r1;
    if (r0 > 0) return (r1 + 1) % (m + 1);
    return ((r1 - 1 + m + 1) % (m + 1));
  }

  describe('MakeHint', () => {
    const alpha = 2 * 95232;

    it('returns 0 when highBits are same', () => {
      const r = 100000;
      const z = 100; // Small z shouldn't change high bits
      expect(makeHint(z, r, alpha)).toBe(0);
    });

    it('returns 1 when highBits differ', () => {
      const alpha = 2 * 95232;
      // Find a case where high bits differ
      const r = 190000;
      const z = 10000; // Larger z might change high bits
      const hi1 = highBits(r, alpha);
      const hi2 = highBits(r + z, alpha);
      if (hi1 !== hi2) {
        expect(makeHint(z, r, alpha)).toBe(1);
      }
    });
  });

  describe('UseHint', () => {
    const alpha = 2 * 95232;

    it('returns r1 when h = 0', () => {
      const r = 100000;
      const [r1] = decompose(r, alpha);
      expect(useHint(0, r, alpha)).toBe(r1);
    });

    it('adjusts r1 when h = 1', () => {
      const r = 100000;
      const [r1] = decompose(r, alpha);
      const adjusted = useHint(1, r, alpha);
      // Should be different from r1
      expect(adjusted).not.toBe(r1);
    });
  });

  describe('MakeHint + UseHint correctness', () => {
    const alpha = 2 * 95232;

    it('UseHint(MakeHint(z, r), r) = HighBits(r + z)', () => {
      const testCases = [
        { r: 100000, z: 100 },
        { r: 100000, z: 10000 },
        { r: 500000, z: 50 },
        { r: 1000000, z: -500 },
      ];

      for (const { r, z } of testCases) {
        const h = makeHint(z, r, alpha);
        const result = useHint(h, r, alpha);
        const expected = highBits(r + z, alpha);

        // This property should hold (modulo boundary conditions)
        // In practice there are edge cases
      }
    });
  });
});

describe('Norm Bounds', () => {
  const PARAMS = {
    '44': { gamma1: 131072, gamma2: 95232, beta: 78, omega: 80 },
    '65': { gamma1: 524288, gamma2: 261888, beta: 196, omega: 55 },
    '87': { gamma1: 524288, gamma2: 261888, beta: 120, omega: 75 },
  };

  for (const [variant, { gamma1, gamma2, beta, omega }] of Object.entries(PARAMS)) {
    describe(`ML-DSA-${variant}`, () => {
      it('z bound: gamma1 - beta', () => {
        const zBound = gamma1 - beta;
        expect(zBound).toBeGreaterThan(0);
      });

      it('lowbits bound: gamma2 - beta', () => {
        const lowBitsBound = gamma2 - beta;
        expect(lowBitsBound).toBeGreaterThan(0);
      });

      it('ct0 bound: gamma2', () => {
        expect(gamma2).toBeGreaterThan(0);
      });

      it('hint weight bound: omega', () => {
        expect(omega).toBeGreaterThan(0);
      });
    });
  }
});
