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
- **Canon.Zq** - OCaml-aligned alias for modular arithmetic
- **Canon.Listvec** - OCaml-aligned alias for vector and matrix operations
- **Canon.Dilithium** - Raw generated ML-DSA surface plus native `Int`-based wrappers
- **Canon.Confidential_balance** - Native confidential-balance proof helpers over SIS commitments
- **Canon.Confidential_range** - Native confidential-range proof helpers over SIS commitments
- **Canon.Confidential_transaction** - Native nullifier, membership, and ledger-validity proof helpers

Compatibility note:
- Legacy confidential-balance proofs are exposed as `{ a, z }`.
- The repaired sigma-style balance surface may move to repeated rounds with
  explicit JSON-friendly proof lists such as `{ rounds = [...] }` or
  `{ as = [...], zs = [...], challenges = [...] }`.
- Legacy confidential-range proofs are still expected as a single record with
  `bits`, `comps`, `amountA`, `amountZ`, `pairAs`, and `pairZs`.
- Repaired confidential-range proofs may instead use repeated rounds
  `{ bits, comps, rounds = [...] }` or explicit list fields
  `{ bits, comps, amountAs, amountZs, pairAss, pairZss, challenges = [...] }`.
- Legacy nullifier proofs use `{ aCommit, aNullifier, zMsg, zRand }`.
- Repaired nullifier proofs may instead use repeated rounds `{ rounds = [...] }`
  or explicit list fields
  `{ aCommits, aNullifiers, zMsgs, zRands, challenges = [...] }`.
- Validation harnesses should treat snapshot `ledgerValid` separately from the
  Merkle-backed ledger-step verifier, exported on the TS surface as
  `ConfidentialTransaction.semanticStepValid` and
  `ConfidentialTransaction.ledgerStepValid`.

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

For the complete namespace-safe surface, prefer the OCaml-aligned aliases:

```haskell
import qualified Canon.Zq as Zq
import qualified Canon.Dilithium as Dilithium
import qualified Canon.Confidential_balance as ConfidentialBalance
import qualified Canon.Confidential_range as ConfidentialRange
import qualified Canon.Confidential_transaction as ConfidentialTransaction

params44 = Dilithium.mldsa44Params
x = Zq.mod_centered 7 5
y = Dilithium.modCentered 1234567 (2 * Dilithium.dilGamma2 params44)
params = ConfidentialBalance.makeScalarCommitParams 2 2 17 3
one = ConfidentialRange.oneOpening params
nk = [[0,1,0],[1,0,0]]
nf = ConfidentialTransaction.nullifier params nk one
```

`Canon.Dilithium` also exposes native Haskell wrappers for the shared SDK
surface:

```haskell
import qualified Canon.Dilithium as Dilithium

params44 = Dilithium.mldsa44Params
split = Dilithium.power2Round 1234567 (Dilithium.dilD params44)
hint = Dilithium.makeHint 2000 100000 (2 * Dilithium.dilGamma2 params44)
```

These wrapper functions use ordinary Haskell `Int`s. Inputs that correspond to
Isabelle `nat` values are normalized with `max 0` before crossing into the
generated code.

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
cabal run isabella-cli -- --json dil-params 44
cabal run isabella-cli -- --json dil-power2round 1234567 13
cabal run isabella-cli -- --json cb-prove 2 2 17 3 5 "[[1,0,0],[0,1,0]]" "[0,1]" "[1,2]" "[0,1]"
cabal run isabella-cli -- --json cr-prove 2 2 17 6 5 3 "[[1,0,0],[0,1,0]]" "[5,1]" 5 "[1,2]" "[1,0,1]" "[[1,0],[0,1],[1,1]]" "[0,1,0]" "[[0,1],[1,0],[0,-1]]" "[0,1]" "[[1,0],[0,0],[1,-1]]"
cabal run isabella-cli -- --json ct-nullifier 2 2 17 6 "[[0,1,0],[1,0,0]]" 5 "[1,2]"
cabal run isabella-cli -- --json ct-member-prove 2 2 17 6 "[[13,8],[4,3]]" "[13,8]"
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

The CLI also supports `--json` for deterministic machine-readable validation:

```bash
cabal run isabella-cli -- --json mod-centered 7 5
```

## License

MIT License - see [LICENSE](LICENSE)
