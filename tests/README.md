# Isabella Tests

Cross-validation test suite for Isabella against [noble-post-quantum](https://github.com/paulmillr/noble-post-quantum).

## Overview

This test harness validates our Isabelle-generated ML-KEM (Kyber) and ML-DSA (Dilithium) implementations by:

1. **Reference comparison** - Comparing our NTT/polynomial operations against noble-post-quantum
2. **CLI integration** - Calling our OCaml CLI with specific inputs and validating outputs
3. **FIPS 203/204 compliance** - Verifying byte encoding and key sizes match the standards

## Prerequisites

- Bun 1.3+
- OCaml with opam (for CLI integration tests)
- Isabella OCaml library built (`cd isabella.ml && dune build`)
- Optional: LaZer Python bindings built locally (for `test:lazer`)

## Setup

```bash
cd tests
bun install
```

Or from the project root:

```bash
make test-validation  # Runs Bun-based cross-validation tests
```

## Running Tests

```bash
# Run all tests
bun test

# Run specific test suites
bun run test:ntt    # NTT operation tests
bun run test:kyber  # ML-KEM tests
bun run test:lazer  # Optional LaZer cross-comparison

# Watch mode for development
bun run test:watch
```

## Test Suites

### NTT Tests (`ntt.test.ts`)

Tests for Number Theoretic Transform operations:
- Modular arithmetic (`powerMod`, `modCentered`)
- Primitive root validation
- NTT correctness (linearity, zero/constant polynomials)
- Polynomial multiplication in the ring Z_q[X]/(X^n + 1)

### Kyber Tests (`kyber.test.ts`)

Tests for ML-KEM key encapsulation using noble-post-quantum:
- Key generation for all parameter sets (512, 768, 1024)
- Encapsulation/decapsulation roundtrips
- Key and ciphertext size validation against FIPS 203
- Deterministic key generation with fixed seeds
- Parameter validation matching our Isabelle implementation

### Integration Tests (`integration.test.ts`)

Tests that call our Isabelle-generated OCaml CLI and compare results:
- Basic math operations (powerMod, modInverse, isPrimitiveRoot)
- NTT operations (nttFast, inttFast, ntt roundtrip)
- Polynomial operations (polyMult, ringMult)
- Kyber operations (kyberNtt, kyberIntt, kyberPolyMult, encode/decode)

### LaZer Comparison Tests (`lazer-comparison.test.ts`)

Optional deterministic cross-checks against [lazer-crypto/lazer](https://github.com/lazer-crypto/lazer):
- Ring multiplication in `R_q = Z_q[X]/(X^n + 1)` on deterministic fixture input
- Matrix-vector multiplication over `R_q` on deterministic fixture input
- Centered modular reduction semantics alignment

The suite is **skip-safe**:
- If Isabella CLI is not built, the suite is skipped.
- If LaZer Python bindings are not importable, the suite is skipped.

Enable it by setting one of:
- `LAZER_ROOT=/absolute/path/to/lazer` (expects bindings in `$LAZER_ROOT/python`)
- `LAZER_PYTHON=/absolute/path/to/lazer/python`

### FIPS 203 Tests (`fips203.test.ts`)

Tests for FIPS 203 byte-level encoding:
- ByteEncode/ByteDecode roundtrips for various bit widths
- Compress/Decompress coefficient mapping
- Polynomial encoding (12-bit coefficients)
- Key size validation against FIPS 203 Table 2
- Cross-validation with noble-post-quantum key/ciphertext sizes

### Dilithium Tests (`dilithium.test.ts`)

Tests for ML-DSA (Dilithium) digital signatures using noble-post-quantum:
- Key generation for all parameter sets (ML-DSA-44, ML-DSA-65, ML-DSA-87)
- Sign/verify roundtrips
- Invalid signature rejection
- Key and signature size validation against FIPS 204 Table 2
- Deterministic key generation with fixed seeds
- Parameter validation (n=256, q=8380417, etc.)
- Compression function reference implementations (modCentered, Power2Round, Decompose)
- HighBits/LowBits extraction
- MakeHint/UseHint correctness
- Norm bound validation

### Dilithium Integration Tests (`dilithium-integration.test.ts`)

Tests that call our Isabelle-generated OCaml CLI for Dilithium operations:
- Parameter retrieval for all ML-DSA variants
- Centered modular reduction (`dil-mod-centered`)
- Power2Round compression (`dil-power2round`)
- Decompose function (`dil-decompose`)
- HighBits/LowBits extraction (`dil-highbits`, `dil-lowbits`)
- Hint creation/usage (`dil-makehint`, `dil-usehint`)
- Bound checking (`dil-check-bound`)
- Hint weight calculation (`dil-hint-weight`)
- Cross-validation with TypeScript reference implementations

## Generating Test Vectors

Generate test vectors from noble-post-quantum for offline validation:

```bash
bun run generate-vectors
```

This creates JSON files in `vectors/`:
- `ml-kem-vectors.json` - Combined test vectors
- `ml_kem_512_vectors.json` - ML-KEM-512 specific vectors
- `ml_kem_768_vectors.json` - ML-KEM-768 specific vectors
- `ml_kem_1024_vectors.json` - ML-KEM-1024 specific vectors
- `deterministic-vectors.json` - Vectors with fixed seeds

## Test Vector Format

```json
{
  "variant": "ML-KEM-768",
  "index": 0,
  "publicKey": "hex...",
  "secretKey": "hex...",
  "cipherText": "hex...",
  "sharedSecret": "hex...",
  "decapsulatedSecret": "hex...",
  "valid": true
}
```

## Validation Strategy

### Current (Option B)
- Use noble-post-quantum as the reference implementation
- Validate our core operations (NTT, polynomial arithmetic)
- Generate test vectors for comparison

### Future (Option A)
To add full FIPS 203 compliance:
1. Implement SHAKE-128/256 for PRF/XOF
2. Add byte-level encoding/decoding
3. Implement seed-based key derivation
4. Test against official NIST ACVP vectors

## Project Structure

```
tests/
├── src/
│   ├── noble-reference.ts           # Noble post-quantum wrapper (ML-KEM + ML-DSA)
│   ├── isabella-runner.ts           # Reference implementations for validation
│   ├── isabella-cli.ts              # CLI wrapper for integration tests
│   ├── generate-vectors.ts          # Test vector generation
│   ├── fips203.ts                   # FIPS 203 byte encoding utilities
│   ├── ntt.test.ts                  # NTT tests
│   ├── kyber.test.ts                # ML-KEM tests
│   ├── integration.test.ts          # CLI integration tests (Kyber)
│   ├── fips203.test.ts              # FIPS 203 byte encoding tests
│   ├── dilithium.test.ts            # ML-DSA tests (noble-post-quantum)
│   └── dilithium-integration.test.ts # ML-DSA CLI integration tests
├── vectors/                         # Generated test vectors
├── package.json
├── bun.lock
├── tsconfig.json
└── README.md
```

## Current Test Coverage

- **156 tests passing** across 6 test suites
- Core NTT operations validated via CLI integration
- Kyber encode/decode validated via CLI integration
- Dilithium compression functions validated via CLI integration
- Key/signature sizes validated against FIPS 203/204 Tables
- Cross-validated with noble-post-quantum (ML-KEM + ML-DSA)

## FIPS 203 Compliance Status (ML-KEM)

### Implemented
- ByteEncode_d / ByteDecode_d (Algorithms 4, 5)
- Compress_d / Decompress_d
- Key size validation
- Core NTT operations (via Isabelle-generated code)

### Needed for Full ACVP Test Vectors
- SHAKE-128/256 for PRF/XOF
- SHA3-256 (H) / SHA3-512 (G) for key derivation
- SampleNTT (Algorithm 6) - matrix A from seed
- SamplePolyCBD_η (Algorithm 7) - noise sampling
- Complete K-PKE and ML-KEM interfaces

## FIPS 204 Compliance Status (ML-DSA)

### Implemented
- Parameter sets (ML-DSA-44, ML-DSA-65, ML-DSA-87)
- Centered modular reduction
- Power2Round (Algorithm 29)
- Decompose (Algorithm 30)
- HighBits / LowBits (Algorithms 31, 32)
- MakeHint / UseHint (Algorithms 33, 34)
- Infinity norm bound checking
- NTT for Dilithium (n=256, q=8380417, ω=1753)

### Needed for Full ACVP Test Vectors
- SHAKE-256 for H, ExpandMask, etc.
- SampleInBall (Algorithm 22) - challenge generation
- ExpandA (Algorithm 24) - matrix A from seed
- ExpandS (Algorithm 25) - secret vector sampling
- ExpandMask (Algorithm 26) - mask generation
- Complete KeyGen / Sign / Verify interfaces

## Isabella CLI Commands

The integration tests use these CLI commands (available via `isabella_cli`):

### NTT Commands
```bash
# Fast NTT (Cooley-Tukey O(n log n))
isabella_cli --json ntt-fast "[1,2,3,4]" 17 3329 4

# Inverse NTT
isabella_cli --json intt-fast "[10,3293,3327,32]" 17 3329 4

# Pointwise multiplication in NTT domain
isabella_cli --json ntt-pointwise "[1,2,3,4]" "[5,6,7,8]" 3329
```

### Kyber Commands
```bash
# Kyber NTT (n=256, q=3329, omega=17)
isabella_cli --json kyber-ntt "[1,0,0,...,0]"  # 256 coefficients

# Kyber polynomial multiplication via NTT
isabella_cli --json kyber-poly-mult "[...]" "[...]"

# Message encoding/decoding
isabella_cli --json kyber-encode-msg "[0,1,0,1,...]"  # 256 bits
isabella_cli --json kyber-decode-msg "[...]"         # 256 coefficients
```

### Utility Commands
```bash
# Modular exponentiation
isabella_cli --json power-mod 17 256 3329  # => {"result":1}

# Modular inverse
isabella_cli --json mod-inverse 17 3329

# Check primitive root
isabella_cli --json is-primitive-root 17 256 3329  # => {"result":true}
```

### Dilithium Commands
```bash
# Get ML-DSA parameters (44, 65, or 87)
isabella_cli --json dil-params 44

# Centered modular reduction
isabella_cli --json dil-mod-centered 200 256  # => {"result":-56}

# Power2Round: split r into (r1, r0) where r = r1 * 2^d + r0
isabella_cli --json dil-power2round 100000 13

# Decompose: split r using alpha
isabella_cli --json dil-decompose 500000 190464

# HighBits / LowBits extraction
isabella_cli --json dil-highbits 500000 190464
isabella_cli --json dil-lowbits 500000 190464

# MakeHint / UseHint for hint mechanism
isabella_cli --json dil-makehint 100 100000 190464
isabella_cli --json dil-usehint 1 100000 190464

# Check if |value| < bound
isabella_cli --json dil-check-bound 50 100  # => {"result":true}

# Compute total hint weight
isabella_cli --json dil-hint-weight "[[1,0,1],[0,1,0]]"  # => {"result":3}
```

## Next Steps

1. Add SHAKE-128/256 for deterministic key derivation
2. Implement SampleNTT to generate matrix A from seed
3. Add full K-PKE.KeyGen/Encrypt/Decrypt
4. Test against official NIST ACVP test vectors

## References

- [FIPS 203](https://csrc.nist.gov/pubs/fips/203/final) - ML-KEM Standard (Kyber)
- [FIPS 204](https://csrc.nist.gov/pubs/fips/204/final) - ML-DSA Standard (Dilithium)
- [noble-post-quantum](https://github.com/paulmillr/noble-post-quantum) - Reference implementation
- [NIST ACVP](https://github.com/usnistgov/ACVP-Server) - Official test vectors
