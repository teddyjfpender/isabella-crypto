/**
 * Dilithium CLI Integration Tests
 *
 * Tests that call our Isabelle-generated OCaml CLI and compare results
 * with reference implementations.
 */

import {
  isCliAvailable,
  dilParams,
  dilModCentered,
  dilPower2Round,
  dilDecompose,
  dilHighbits,
  dilLowbits,
  dilMakeHint,
  dilUseHint,
  dilCheckBound,
  dilHintWeight,
} from './isabella-cli.js';

const CLI_AVAILABLE = isCliAvailable();

// Skip all tests if CLI not available
const describeIfCli = CLI_AVAILABLE ? describe : describe.skip;

// Reference implementations for comparison
function refModCentered(r: number, m: number): number {
  let rMod = r % m;
  if (rMod < 0) rMod += m;
  if (rMod > Math.floor(m / 2)) rMod -= m;
  return rMod;
}

function refPower2Round(r: number, d: number): [number, number] {
  const twoD = 1 << d;
  const r0 = refModCentered(r, twoD);
  const r1 = Math.floor((r - r0) / twoD);
  return [r1, r0];
}

const q = 8380417;

function refDecompose(r: number, alpha: number): [number, number] {
  const r0 = refModCentered(r, alpha);
  let r1 = Math.floor((r - r0) / alpha);
  if (r - r0 === q - 1) {
    r1 = 0;
    return [r1, r0 - 1];
  }
  return [r1, r0];
}

function refHighbits(r: number, alpha: number): number {
  return refDecompose(r, alpha)[0];
}

function refLowbits(r: number, alpha: number): number {
  return refDecompose(r, alpha)[1];
}

function refMakeHint(z: number, r: number, alpha: number): number {
  const hi1 = refHighbits(r, alpha);
  const hi2 = refHighbits(r + z, alpha);
  return hi1 !== hi2 ? 1 : 0;
}

function refUseHint(h: number, r: number, alpha: number): number {
  const [r1, r0] = refDecompose(r, alpha);
  const m = Math.floor((q - 1) / alpha);
  if (h === 0) return r1;
  if (r0 > 0) return (r1 + 1) % (m + 1);
  return ((r1 - 1 + m + 1) % (m + 1));
}

describeIfCli('Dilithium CLI Integration Tests', () => {
  describe('dil-params', () => {
    it('returns correct ML-DSA-44 parameters', () => {
      const params = dilParams('44');
      expect(params.n).toBe(256);
      expect(params.q).toBe(8380417);
      expect(params.k).toBe(4);
      expect(params.l).toBe(4);
      expect(params.eta).toBe(2);
      expect(params.tau).toBe(39);
      expect(params.beta).toBe(78);
      expect(params.gamma1).toBe(131072);
      expect(params.gamma2).toBe(95232);
      expect(params.d).toBe(13);
      expect(params.omega).toBe(80);
    });

    it('returns correct ML-DSA-65 parameters', () => {
      const params = dilParams('65');
      expect(params.n).toBe(256);
      expect(params.q).toBe(8380417);
      expect(params.k).toBe(6);
      expect(params.l).toBe(5);
      expect(params.eta).toBe(4);
      expect(params.tau).toBe(49);
      expect(params.beta).toBe(196);
      expect(params.gamma1).toBe(524288);
      expect(params.gamma2).toBe(261888);
      expect(params.d).toBe(13);
      expect(params.omega).toBe(55);
    });

    it('returns correct ML-DSA-87 parameters', () => {
      const params = dilParams('87');
      expect(params.n).toBe(256);
      expect(params.q).toBe(8380417);
      expect(params.k).toBe(8);
      expect(params.l).toBe(7);
      expect(params.eta).toBe(2);
      expect(params.tau).toBe(60);
      expect(params.beta).toBe(120);
      expect(params.gamma1).toBe(524288);
      expect(params.gamma2).toBe(261888);
      expect(params.d).toBe(13);
      expect(params.omega).toBe(75);
    });
  });

  describe('dil-mod-centered', () => {
    it('matches reference for positive values', () => {
      const testCases = [
        { r: 5, m: 16 },
        { r: 12, m: 16 },
        { r: 100, m: 256 },
        { r: 200, m: 256 },
      ];

      for (const { r, m } of testCases) {
        const cliResult = dilModCentered(r, m);
        const refResult = refModCentered(r, m);
        expect(cliResult).toBe(refResult);
      }
    });

    it('matches reference for negative values', () => {
      const testCases = [
        { r: -3, m: 16 },
        { r: -10, m: 16 },
        { r: -100, m: 256 },
      ];

      for (const { r, m } of testCases) {
        const cliResult = dilModCentered(r, m);
        const refResult = refModCentered(r, m);
        expect(cliResult).toBe(refResult);
      }
    });

    it('handles boundary cases', () => {
      // Exactly at m/2
      expect(dilModCentered(8, 16)).toBe(refModCentered(8, 16));
      // Just over m/2
      expect(dilModCentered(9, 16)).toBe(refModCentered(9, 16));
    });
  });

  describe('dil-power2round', () => {
    const d = 13;
    const twoD = 1 << d;

    it('matches reference implementation', () => {
      const testCases = [0, 100, 1000, 5000, 10000, 100000, 1000000];

      for (const r of testCases) {
        const cliResult = dilPower2Round(r, d);
        const [refR1, refR0] = refPower2Round(r, d);

        expect(cliResult.r1).toBe(refR1);
        expect(cliResult.r0).toBe(refR0);
      }
    });

    it('satisfies reconstruction property', () => {
      const testCases = [0, 100, 5000, 100000, 1234567];

      for (const r of testCases) {
        const result = dilPower2Round(r, d);
        expect(result.r1 * twoD + result.r0).toBe(r);
      }
    });

    it('r0 is in correct range', () => {
      const halfD = twoD / 2;
      const testCases = [0, 100, 5000, 100000, 1234567];

      for (const r of testCases) {
        const result = dilPower2Round(r, d);
        expect(result.r0).toBeGreaterThan(-halfD - 1);
        expect(result.r0).toBeLessThanOrEqual(halfD);
      }
    });
  });

  describe('dil-decompose', () => {
    const alpha = 2 * 95232; // 2 * gamma2 for ML-DSA-44

    it('matches reference for standard values', () => {
      const testCases = [0, 100, 1000, 50000, 100000, 500000];

      for (const r of testCases) {
        const cliResult = dilDecompose(r, alpha);
        const [refR1, refR0] = refDecompose(r, alpha);

        expect(cliResult.r1).toBe(refR1);
        expect(cliResult.r0).toBe(refR0);
      }
    });
  });

  describe('dil-highbits / dil-lowbits', () => {
    const alpha = 2 * 95232;

    it('highbits matches decompose', () => {
      const testCases = [100, 1000, 50000, 100000];

      for (const r of testCases) {
        const hi = dilHighbits(r, alpha);
        const decomp = dilDecompose(r, alpha);
        expect(hi).toBe(decomp.r1);
      }
    });

    it('lowbits matches decompose', () => {
      const testCases = [100, 1000, 50000, 100000];

      for (const r of testCases) {
        const lo = dilLowbits(r, alpha);
        const decomp = dilDecompose(r, alpha);
        expect(lo).toBe(decomp.r0);
      }
    });

    it('highbits matches reference', () => {
      const testCases = [100, 1000, 50000, 100000];

      for (const r of testCases) {
        expect(dilHighbits(r, alpha)).toBe(refHighbits(r, alpha));
      }
    });

    it('lowbits matches reference', () => {
      const testCases = [100, 1000, 50000, 100000];

      for (const r of testCases) {
        expect(dilLowbits(r, alpha)).toBe(refLowbits(r, alpha));
      }
    });
  });

  describe('dil-makehint / dil-usehint', () => {
    const alpha = 2 * 95232;

    it('makehint returns 0 for small z', () => {
      // Small z shouldn't change high bits
      const r = 100000;
      const z = 100;
      const h = dilMakeHint(z, r, alpha);
      expect(h).toBe(refMakeHint(z, r, alpha));
    });

    it('makehint matches reference', () => {
      const testCases = [
        { z: 100, r: 100000 },
        { z: 1000, r: 100000 },
        { z: 10000, r: 500000 },
        { z: -500, r: 1000000 },
      ];

      for (const { z, r } of testCases) {
        expect(dilMakeHint(z, r, alpha)).toBe(refMakeHint(z, r, alpha));
      }
    });

    it('usehint matches reference', () => {
      const testCases = [
        { h: 0, r: 100000 },
        { h: 1, r: 100000 },
        { h: 0, r: 500000 },
        { h: 1, r: 500000 },
      ];

      for (const { h, r } of testCases) {
        expect(dilUseHint(h, r, alpha)).toBe(refUseHint(h, r, alpha));
      }
    });
  });

  describe('dil-check-bound', () => {
    it('returns true when |value| < bound', () => {
      expect(dilCheckBound(50, 100)).toBe(true);
      expect(dilCheckBound(-50, 100)).toBe(true);
      expect(dilCheckBound(0, 100)).toBe(true);
    });

    it('returns false when |value| >= bound', () => {
      expect(dilCheckBound(100, 100)).toBe(false);
      expect(dilCheckBound(-100, 100)).toBe(false);
      expect(dilCheckBound(150, 100)).toBe(false);
    });

    it('handles boundary cases', () => {
      expect(dilCheckBound(99, 100)).toBe(true);
      expect(dilCheckBound(-99, 100)).toBe(true);
    });
  });

  describe('dil-hint-weight', () => {
    it('counts total hint bits', () => {
      expect(dilHintWeight([[1, 0, 1], [0, 1, 0]])).toBe(3);
      expect(dilHintWeight([[0, 0, 0], [0, 0, 0]])).toBe(0);
      expect(dilHintWeight([[1, 1, 1], [1, 1, 1]])).toBe(6);
    });

    it('handles single row', () => {
      expect(dilHintWeight([[1, 0, 1, 0, 1]])).toBe(3);
    });

    it('handles empty hints', () => {
      expect(dilHintWeight([[0], [0]])).toBe(0);
    });
  });
});

describeIfCli('Dilithium Cross-Validation', () => {
  describe('Power2Round reconstruction property', () => {
    const d = 13;
    const twoD = 1 << d;

    it('CLI and reference agree on reconstruction', () => {
      const testValues = [0, 1, 100, 1000, 8191, 8192, 8193, 100000, 1000000, 4190208];

      for (const r of testValues) {
        // CLI result
        const cliResult = dilPower2Round(r, d);

        // Reference result
        const [refR1, refR0] = refPower2Round(r, d);

        // Both should match
        expect(cliResult.r1).toBe(refR1);
        expect(cliResult.r0).toBe(refR0);

        // Both should reconstruct correctly
        expect(cliResult.r1 * twoD + cliResult.r0).toBe(r);
        expect(refR1 * twoD + refR0).toBe(r);
      }
    });
  });

  describe('Decompose with different alpha values', () => {
    it('works with ML-DSA-44 alpha = 2*gamma2', () => {
      const alpha = 2 * 95232;
      const testValues = [0, 100, 1000, 50000, 100000];

      for (const r of testValues) {
        const cliResult = dilDecompose(r, alpha);
        const [refR1, refR0] = refDecompose(r, alpha);

        expect(cliResult.r1).toBe(refR1);
        expect(cliResult.r0).toBe(refR0);
      }
    });

    it('works with ML-DSA-65/87 alpha = 2*gamma2', () => {
      const alpha = 2 * 261888;
      const testValues = [0, 100, 1000, 50000, 100000, 500000];

      for (const r of testValues) {
        const cliResult = dilDecompose(r, alpha);
        const [refR1, refR0] = refDecompose(r, alpha);

        expect(cliResult.r1).toBe(refR1);
        expect(cliResult.r0).toBe(refR0);
      }
    });
  });

  describe('Hint correctness property', () => {
    const alpha = 2 * 95232;

    it('UseHint(MakeHint(z, r), r) recovers HighBits(r + z)', () => {
      const testCases = [
        { r: 100000, z: 100 },
        { r: 100000, z: 1000 },
        { r: 500000, z: 500 },
        { r: 1000000, z: -100 },
      ];

      for (const { r, z } of testCases) {
        const h = dilMakeHint(z, r, alpha);
        const recovered = dilUseHint(h, r, alpha);
        const expected = dilHighbits(r + z, alpha);

        expect(recovered).toBe(expected);
      }
    });
  });
});

if (!CLI_AVAILABLE) {
  describe('CLI Integration Tests', () => {
    it('CLI not available - skipping integration tests', () => {
      console.warn('OCaml CLI not available. Run `cd isabella.ml && dune build` to enable integration tests.');
      expect(true).toBe(true);
    });
  });
}
