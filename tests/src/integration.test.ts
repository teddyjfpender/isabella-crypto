/**
 * Integration Tests - Isabella CLI vs Reference Implementations
 *
 * These tests call our Isabelle-generated OCaml CLI and compare
 * results against our TypeScript reference implementations.
 */

import {
  isCliAvailable,
  nttFast,
  inttFast,
  nttPointwise,
  powerMod,
  modInverse,
  isPrimitiveRoot,
  polyMult,
  ringMult,
  kyberNtt,
  kyberIntt,
  kyberPolyMult,
  kyberEncodeMsg,
  kyberDecodeMsg,
} from './isabella-cli.js';

import {
  nttNaive,
  powerMod as refPowerMod,
  isPrimitiveRoot as refIsPrimitiveRoot,
  polyMultNaive,
  KYBER_NTT_PARAMS,
} from './isabella-runner.js';

// Check if CLI is available before running tests
const CLI_AVAILABLE = isCliAvailable();

const describeIf = (condition: boolean) => condition ? describe : describe.skip;

describeIf(CLI_AVAILABLE)('Isabella CLI Integration', () => {
  describe('Basic Math Operations', () => {
    it('powerMod matches reference', () => {
      const testCases = [
        [2, 10, 1000],
        [3, 5, 100],
        [17, 0, 3329],
        [17, 1, 3329],
        [17, 256, 3329],
      ];

      for (const [a, k, m] of testCases) {
        const cliResult = powerMod(a, k, m);
        const refResult = refPowerMod(a, k, m);
        expect(cliResult).toBe(refResult);
      }
    });

    it('modInverse is correct', () => {
      // Test that a * a^(-1) = 1 (mod m)
      const testCases = [
        [17, 3329],
        [256, 3329],
        [3, 7],
        [5, 11],
      ];

      for (const [a, m] of testCases) {
        const inv = modInverse(a, m);
        expect((a * inv) % m).toBe(1);
      }
    });

    it('isPrimitiveRoot validates correctly', () => {
      // 17 is a primitive 256th root of unity mod 3329
      expect(isPrimitiveRoot(17, 256, 3329)).toBe(true);
      expect(isPrimitiveRoot(1, 256, 3329)).toBe(false);
    });
  });

  describe('NTT Operations', () => {
    const { omega, q } = KYBER_NTT_PARAMS;

    it('nttFast transforms small vectors', () => {
      const n = 4;
      const smallOmega = refPowerMod(omega, 256 / n, q); // omega^64 for n=4
      const input = [1, 2, 3, 4];

      const result = nttFast(input, smallOmega, q, n);

      expect(result.input).toEqual(input);
      expect(result.output.length).toBe(n);
    });

    it('NTT roundtrip preserves values', () => {
      const n = 4;
      const smallOmega = refPowerMod(omega, 256 / n, q);
      const input = [1, 2, 3, 4];

      const nttResult = nttFast(input, smallOmega, q, n);
      const inttResult = inttFast(nttResult.output, smallOmega, q, n);

      expect(inttResult.output).toEqual(input);
    });

    it('NTT of zero polynomial is zero', () => {
      const n = 8;
      const smallOmega = refPowerMod(omega, 256 / n, q);
      const input = new Array(n).fill(0);

      const result = nttFast(input, smallOmega, q, n);

      expect(result.output.every(x => x === 0)).toBe(true);
    });

    it('nttPointwise multiplies correctly', () => {
      const a = [1, 2, 3, 4];
      const b = [5, 6, 7, 8];

      const result = nttPointwise(a, b, q);

      // Pointwise: [1*5, 2*6, 3*7, 4*8] mod q
      const expected = [5, 12, 21, 32].map(x => x % q);
      expect(result.result).toEqual(expected);
    });
  });

  describe('Polynomial Operations', () => {
    it('polyMult multiplies correctly', () => {
      // (1 + 2x) * (3 + 4x) = 3 + 10x + 8x^2
      const a = [1, 2];
      const b = [3, 4];

      const result = polyMult(a, b);

      expect(result.result).toEqual([3, 10, 8]);
    });

    it('polyMult matches manual calculation', () => {
      // (1 + 2x + 3x^2) * (4 + 5x + 6x^2)
      // = 4 + 5x + 6x^2 + 8x + 10x^2 + 12x^3 + 12x^2 + 15x^3 + 18x^4
      // = 4 + 13x + 28x^2 + 27x^3 + 18x^4
      const a = [1, 2, 3];
      const b = [4, 5, 6];

      const cliResult = polyMult(a, b);

      expect(cliResult.result).toEqual([4, 13, 28, 27, 18]);
    });

    it('ringMult reduces mod X^n + 1', () => {
      const n = 4;
      const q = 17;
      // X^3 * X^2 = X^5 = X * (-1) = -X (mod X^4 + 1)
      const a = [0, 0, 0, 1]; // X^3
      const b = [0, 0, 1, 0]; // X^2

      const result = ringMult(a, b, n, q);

      // X^5 = -X (mod X^4 + 1) = [0, -1, 0, 0]
      // OCaml may return -1 or 16 (both are -1 mod 17)
      const coeff = result.result[1];
      expect(coeff === -1 || coeff === q - 1).toBe(true);
    });
  });

  describe('Kyber Operations', () => {
    it('kyberNtt and kyberIntt roundtrip (small test)', () => {
      // Create a 256-element polynomial
      const input = new Array(256).fill(0);
      input[0] = 1;
      input[1] = 2;

      const nttResult = kyberNtt(input);
      expect(nttResult.output.length).toBe(256);

      const inttResult = kyberIntt(nttResult.output);
      expect(inttResult.output).toEqual(input);
    });

    it('kyberPolyMult via NTT', () => {
      // Test multiplication of simple polynomials
      const a = new Array(256).fill(0);
      const b = new Array(256).fill(0);
      a[0] = 1; // f(x) = 1
      b[0] = 1; // g(x) = 1

      const result = kyberPolyMult(a, b);

      // 1 * 1 = 1
      expect(result.result[0]).toBe(1);
      expect(result.result.slice(1).every(x => x === 0)).toBe(true);
    });

    it('kyberEncodeMsg encodes bits correctly', () => {
      const msg = new Array(256).fill(0);
      msg[0] = 1;
      msg[1] = 0;
      msg[2] = 1;

      const result = kyberEncodeMsg(msg);

      // Bit 1 encodes as ~q/2 = 1665
      const halfQ = Math.floor((3329 + 1) / 2);
      expect(result.output[0]).toBe(halfQ);
      expect(result.output[1]).toBe(0);
      expect(result.output[2]).toBe(halfQ);
    });

    it('kyberDecodeMsg roundtrip (no noise)', () => {
      const msg = new Array(256).fill(0);
      // Random bits
      for (let i = 0; i < 32; i++) {
        msg[i] = i % 2;
      }

      const encoded = kyberEncodeMsg(msg);
      const decoded = kyberDecodeMsg(encoded.output);

      expect(decoded.output).toEqual(msg);
    });

    it('kyberDecodeMsg tolerates small noise', () => {
      const msg = new Array(256).fill(0);
      msg[0] = 1;
      msg[1] = 0;

      const encoded = kyberEncodeMsg(msg);

      // Add small noise (less than q/4 = 832)
      const noisy = encoded.output.map((x, i) => {
        if (i < 2) return (x + 100) % 3329;
        return x;
      });

      const decoded = kyberDecodeMsg(noisy);

      expect(decoded.output[0]).toBe(1);
      expect(decoded.output[1]).toBe(0);
    });
  });
});

// Test to verify CLI is available
describe('CLI Availability', () => {
  it('reports CLI availability status', () => {
    console.log(`Isabella CLI available: ${CLI_AVAILABLE}`);
    if (!CLI_AVAILABLE) {
      console.log('Skipping integration tests - CLI not built');
      console.log('Run: cd isabella.ml && dune build');
    }
  });
});
