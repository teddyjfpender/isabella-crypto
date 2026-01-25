/**
 * NTT (Number Theoretic Transform) Tests
 *
 * Tests for the NTT operations used in Kyber/ML-KEM.
 * These validate our reference implementations before comparing
 * against the Isabelle-generated code.
 */

import {
  nttNaive,
  powerMod,
  isPrimitiveRoot,
  polyMultNaive,
  KYBER_NTT_PARAMS,
  modCentered,
} from './isabella-runner.js';

describe('NTT Primitives', () => {
  const { n, q, omega } = KYBER_NTT_PARAMS;

  describe('powerMod', () => {
    it('computes modular exponentiation correctly', () => {
      expect(powerMod(2, 10, 1000)).toBe(24);
      expect(powerMod(3, 5, 100)).toBe(43);
      expect(powerMod(17, 0, 3329)).toBe(1);
      expect(powerMod(17, 1, 3329)).toBe(17);
    });

    it('handles large exponents', () => {
      expect(powerMod(17, 256, 3329)).toBe(1); // omega^n = 1 mod q
    });
  });

  describe('isPrimitiveRoot', () => {
    it('validates that 17 is a primitive 256th root of unity mod 3329', () => {
      expect(isPrimitiveRoot(17, 256, 3329)).toBe(true);
    });

    it('rejects non-primitive roots', () => {
      expect(isPrimitiveRoot(1, 256, 3329)).toBe(false);
      expect(isPrimitiveRoot(3328, 256, 3329)).toBe(false); // -1 mod 3329
    });
  });

  describe('modCentered', () => {
    it('computes centered modular reduction', () => {
      expect(modCentered(0, 3329)).toBe(0);
      expect(modCentered(1664, 3329)).toBe(1664);
      expect(modCentered(1665, 3329)).toBe(-1664);
      expect(modCentered(3328, 3329)).toBe(-1);
      expect(modCentered(-1, 3329)).toBe(-1);
      expect(modCentered(-1664, 3329)).toBe(-1664);
    });
  });

  describe('nttNaive', () => {
    it('transforms zero polynomial to zero', () => {
      const zero = new Array(n).fill(0);
      const result = nttNaive(zero, omega, q, n);
      expect(result.every(x => x === 0)).toBe(true);
    });

    it('transforms constant polynomial correctly', () => {
      const constant = new Array(n).fill(0);
      constant[0] = 1; // f(x) = 1
      const result = nttNaive(constant, omega, q, n);
      // NTT of 1 is [1, 1, 1, ..., 1]
      expect(result.every(x => x === 1)).toBe(true);
    });

    it('is linear: NTT(a + b) = NTT(a) + NTT(b)', () => {
      const a = new Array(n).fill(0).map((_, i) => i % q);
      const b = new Array(n).fill(0).map((_, i) => (i * 2) % q);
      const sum = a.map((ai, i) => (ai + b[i]) % q);

      const nttA = nttNaive(a, omega, q, n);
      const nttB = nttNaive(b, omega, q, n);
      const nttSum = nttNaive(sum, omega, q, n);
      const nttAB = nttA.map((ai, i) => (ai + nttB[i]) % q);

      expect(nttSum).toEqual(nttAB);
    });
  });

  describe('polyMultNaive', () => {
    it('multiplies by 1 correctly', () => {
      const a = new Array(n).fill(0).map((_, i) => i % 10);
      const one = new Array(n).fill(0);
      one[0] = 1;

      const result = polyMultNaive(a, one, q, n);
      expect(result).toEqual(a);
    });

    it('multiplies by x correctly (shifts and negates due to X^n = -1)', () => {
      const a = new Array(n).fill(0);
      a[0] = 1; // f(x) = 1
      const x = new Array(n).fill(0);
      x[1] = 1; // g(x) = x

      const result = polyMultNaive(a, x, q, n);
      // 1 * x = x
      expect(result[1]).toBe(1);
      expect(result.filter((v, i) => i !== 1 && v !== 0).length).toBe(0);
    });

    it('handles X^n = -1 reduction correctly', () => {
      const xn_minus_1 = new Array(n).fill(0);
      xn_minus_1[n - 1] = 1; // X^(n-1)
      const x = new Array(n).fill(0);
      x[1] = 1; // X

      const result = polyMultNaive(xn_minus_1, x, q, n);
      // X^(n-1) * X = X^n = -1 (mod X^n + 1)
      expect(result[0]).toBe(q - 1); // -1 mod q
    });

    it('is commutative', () => {
      const a = new Array(n).fill(0).map((_, i) => i % 5);
      const b = new Array(n).fill(0).map((_, i) => (i * 3 + 2) % 7);

      const ab = polyMultNaive(a, b, q, n);
      const ba = polyMultNaive(b, a, q, n);

      expect(ab).toEqual(ba);
    });
  });
});

describe('Kyber NTT Parameters', () => {
  it('has correct parameters', () => {
    expect(KYBER_NTT_PARAMS.n).toBe(256);
    expect(KYBER_NTT_PARAMS.q).toBe(3329);
    expect(KYBER_NTT_PARAMS.omega).toBe(17);
  });

  it('q is prime', () => {
    const q = KYBER_NTT_PARAMS.q;
    // Simple primality check for small numbers
    for (let i = 2; i * i <= q; i++) {
      expect(q % i).not.toBe(0);
    }
  });

  it('q = 1 (mod n) for NTT to work', () => {
    const { n, q } = KYBER_NTT_PARAMS;
    // q = 3329 = 1 + 13 * 256 = 1 (mod 256)
    // This ensures n-th roots of unity exist in Z_q
    expect(q % n).toBe(1);
  });
});
