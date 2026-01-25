# Isabella (Haskell)

Formally verified lattice cryptography library extracted from Isabelle/HOL.

## Overview

Isabella provides lattice-based cryptographic primitives that have been
formally verified in Isabelle/HOL. Every function in this library is
generated from proven-correct specifications, ensuring mathematical
correctness.

## Modules

- **Canon** - Re-exports all functionality
- **Canon.Algebra.Zq** - Modular arithmetic over Z_q
- **Canon.Linear.ListVec** - Vector and matrix operations

## Installation

```bash
cabal build
```

## Usage

### As a Library

```haskell
import Canon

-- Centered modular reduction
x = mod_centered 7 5  -- Result: 2

-- Bit encoding for LWE
encoded = encode_bit 256 True   -- Result: 128
decoded = decode_bit 256 130    -- Result: True

-- Vector operations
v1 = [1, 2, 3]
v2 = [4, 5, 6]
dot = inner_prod v1 v2  -- Result: 32

-- Matrix-vector multiplication mod q
result = mat_vec_mult_mod [[1,2],[3,4]] [5,6] 10
```

### Command-Line Interface

```bash
# Run examples
cabal run isabella-cli -- examples

# Use specific functions
cabal run isabella-cli -- mod-centered 7 5
cabal run isabella-cli -- dist0 256 130
cabal run isabella-cli -- encode-bit 256 1
cabal run isabella-cli -- decode-bit 256 130
cabal run isabella-cli -- inner-prod "[1,2,3]" "[4,5,6]"
```

## Verified Properties

All functions come with machine-checked proofs in Isabelle/HOL:

### Centered Modular Reduction
- `mod_centered x q mod q = x mod q`
- `|mod_centered x q| <= q/2`
- `mod_centered 0 q = 0`

### Distance Function
- `dist0 q x >= 0`
- `dist0 q x <= q/2`
- `dist0 q 0 = 0`

### Bit Encoding/Decoding
- `decode_bit q (encode_bit q b) = b` (for q > 2)
- Small noise tolerance: if `|x| < q/4` then `decode_bit q (encode_bit q b + x) = b`

## Testing

```bash
cabal test
```

## License

MIT License - see [LICENSE](LICENSE)
