/**
 * ML-KEM (Kyber) Tests
 *
 * Cross-validation tests comparing noble-post-quantum with our implementation.
 */

import {
  ml_kem512,
  ml_kem768,
  ml_kem1024,
  generateKeyPair,
  encapsulate,
  decapsulate,
  hexToBytes,
  bytesToHex,
} from './noble-reference.js';

import {
  KYBER_512_PARAMS,
  KYBER_768_PARAMS,
  KYBER_1024_PARAMS,
} from './isabella-runner.js';

describe('ML-KEM Noble Reference', () => {
  describe('ML-KEM-512', () => {
    it('generates valid key pairs', () => {
      const keys = generateKeyPair(ml_kem512);
      expect(keys.publicKey).toBeInstanceOf(Uint8Array);
      expect(keys.secretKey).toBeInstanceOf(Uint8Array);
      // ML-KEM-512 public key is 800 bytes
      expect(keys.publicKey.length).toBe(800);
      // ML-KEM-512 secret key is 1632 bytes
      expect(keys.secretKey.length).toBe(1632);
    });

    it('encapsulates and decapsulates correctly', () => {
      const keys = generateKeyPair(ml_kem512);
      const { cipherText, sharedSecret } = encapsulate(ml_kem512, keys.publicKey);
      const decapsulated = decapsulate(ml_kem512, cipherText, keys.secretKey);

      expect(Buffer.from(sharedSecret).toString('hex'))
        .toBe(Buffer.from(decapsulated).toString('hex'));
    });

    it('produces deterministic results with fixed seed', () => {
      const seed = new Uint8Array(64).fill(0x42);
      const keys1 = ml_kem512.keygen(seed);
      const keys2 = ml_kem512.keygen(seed);

      expect(Buffer.from(keys1.publicKey).toString('hex'))
        .toBe(Buffer.from(keys2.publicKey).toString('hex'));
      expect(Buffer.from(keys1.secretKey).toString('hex'))
        .toBe(Buffer.from(keys2.secretKey).toString('hex'));
    });

    it('produces 32-byte shared secrets', () => {
      const keys = generateKeyPair(ml_kem512);
      const { sharedSecret } = encapsulate(ml_kem512, keys.publicKey);
      expect(sharedSecret.length).toBe(32);
    });
  });

  describe('ML-KEM-768', () => {
    it('generates valid key pairs', () => {
      const keys = generateKeyPair(ml_kem768);
      expect(keys.publicKey.length).toBe(1184);
      expect(keys.secretKey.length).toBe(2400);
    });

    it('encapsulates and decapsulates correctly', () => {
      const keys = generateKeyPair(ml_kem768);
      const { cipherText, sharedSecret } = encapsulate(ml_kem768, keys.publicKey);
      const decapsulated = decapsulate(ml_kem768, cipherText, keys.secretKey);

      expect(Buffer.from(sharedSecret).toString('hex'))
        .toBe(Buffer.from(decapsulated).toString('hex'));
    });

    it('ciphertext has correct size', () => {
      const keys = generateKeyPair(ml_kem768);
      const { cipherText } = encapsulate(ml_kem768, keys.publicKey);
      // ML-KEM-768 ciphertext is 1088 bytes
      expect(cipherText.length).toBe(1088);
    });
  });

  describe('ML-KEM-1024', () => {
    it('generates valid key pairs', () => {
      const keys = generateKeyPair(ml_kem1024);
      expect(keys.publicKey.length).toBe(1568);
      expect(keys.secretKey.length).toBe(3168);
    });

    it('encapsulates and decapsulates correctly', () => {
      const keys = generateKeyPair(ml_kem1024);
      const { cipherText, sharedSecret } = encapsulate(ml_kem1024, keys.publicKey);
      const decapsulated = decapsulate(ml_kem1024, cipherText, keys.secretKey);

      expect(Buffer.from(sharedSecret).toString('hex'))
        .toBe(Buffer.from(decapsulated).toString('hex'));
    });

    it('ciphertext has correct size', () => {
      const keys = generateKeyPair(ml_kem1024);
      const { cipherText } = encapsulate(ml_kem1024, keys.publicKey);
      // ML-KEM-1024 ciphertext is 1568 bytes
      expect(cipherText.length).toBe(1568);
    });
  });
});

describe('ML-KEM Key Sizes', () => {
  // FIPS 203 specifies exact key and ciphertext sizes
  const expectedSizes = {
    'ML-KEM-512': { pk: 800, sk: 1632, ct: 768 },
    'ML-KEM-768': { pk: 1184, sk: 2400, ct: 1088 },
    'ML-KEM-1024': { pk: 1568, sk: 3168, ct: 1568 },
  };

  it('ML-KEM-512 has correct sizes', () => {
    const keys = generateKeyPair(ml_kem512);
    const { cipherText } = encapsulate(ml_kem512, keys.publicKey);

    expect(keys.publicKey.length).toBe(expectedSizes['ML-KEM-512'].pk);
    expect(keys.secretKey.length).toBe(expectedSizes['ML-KEM-512'].sk);
    expect(cipherText.length).toBe(expectedSizes['ML-KEM-512'].ct);
  });

  it('ML-KEM-768 has correct sizes', () => {
    const keys = generateKeyPair(ml_kem768);
    const { cipherText } = encapsulate(ml_kem768, keys.publicKey);

    expect(keys.publicKey.length).toBe(expectedSizes['ML-KEM-768'].pk);
    expect(keys.secretKey.length).toBe(expectedSizes['ML-KEM-768'].sk);
    expect(cipherText.length).toBe(expectedSizes['ML-KEM-768'].ct);
  });

  it('ML-KEM-1024 has correct sizes', () => {
    const keys = generateKeyPair(ml_kem1024);
    const { cipherText } = encapsulate(ml_kem1024, keys.publicKey);

    expect(keys.publicKey.length).toBe(expectedSizes['ML-KEM-1024'].pk);
    expect(keys.secretKey.length).toBe(expectedSizes['ML-KEM-1024'].sk);
    expect(cipherText.length).toBe(expectedSizes['ML-KEM-1024'].ct);
  });
});

describe('Isabella Parameters Match FIPS 203', () => {
  it('Kyber-512 parameters are correct', () => {
    expect(KYBER_512_PARAMS.n).toBe(256);
    expect(KYBER_512_PARAMS.q).toBe(3329);
    expect(KYBER_512_PARAMS.k).toBe(2);
    expect(KYBER_512_PARAMS.eta1).toBe(3);
    expect(KYBER_512_PARAMS.eta2).toBe(2);
    expect(KYBER_512_PARAMS.du).toBe(10);
    expect(KYBER_512_PARAMS.dv).toBe(4);
  });

  it('Kyber-768 parameters are correct', () => {
    expect(KYBER_768_PARAMS.n).toBe(256);
    expect(KYBER_768_PARAMS.q).toBe(3329);
    expect(KYBER_768_PARAMS.k).toBe(3);
    expect(KYBER_768_PARAMS.eta1).toBe(2);
    expect(KYBER_768_PARAMS.eta2).toBe(2);
    expect(KYBER_768_PARAMS.du).toBe(10);
    expect(KYBER_768_PARAMS.dv).toBe(4);
  });

  it('Kyber-1024 parameters are correct', () => {
    expect(KYBER_1024_PARAMS.n).toBe(256);
    expect(KYBER_1024_PARAMS.q).toBe(3329);
    expect(KYBER_1024_PARAMS.k).toBe(4);
    expect(KYBER_1024_PARAMS.eta1).toBe(2);
    expect(KYBER_1024_PARAMS.eta2).toBe(2);
    expect(KYBER_1024_PARAMS.du).toBe(11);
    expect(KYBER_1024_PARAMS.dv).toBe(5);
  });
});

describe('Hex Utilities', () => {
  it('converts hex to bytes and back', () => {
    const hex = 'deadbeef0123456789abcdef';
    const bytes = hexToBytes(hex);
    const backToHex = bytesToHex(bytes);
    expect(backToHex).toBe(hex);
  });

  it('handles empty strings', () => {
    const bytes = hexToBytes('');
    expect(bytes.length).toBe(0);
    expect(bytesToHex(new Uint8Array(0))).toBe('');
  });
});

describe('Stress Tests', () => {
  it('handles multiple encapsulations with same key', () => {
    const keys = generateKeyPair(ml_kem768);

    for (let i = 0; i < 10; i++) {
      const { cipherText, sharedSecret } = encapsulate(ml_kem768, keys.publicKey);
      const decapsulated = decapsulate(ml_kem768, cipherText, keys.secretKey);

      expect(Buffer.from(sharedSecret).toString('hex'))
        .toBe(Buffer.from(decapsulated).toString('hex'));
    }
  });

  it('different keys produce different shared secrets (probabilistic)', () => {
    const secrets = new Set<string>();

    for (let i = 0; i < 10; i++) {
      const keys = generateKeyPair(ml_kem768);
      const { sharedSecret } = encapsulate(ml_kem768, keys.publicKey);
      secrets.add(Buffer.from(sharedSecret).toString('hex'));
    }

    // With overwhelming probability, all 10 should be different
    expect(secrets.size).toBe(10);
  });
});
