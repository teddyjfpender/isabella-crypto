# Isabella

[![CI](https://github.com/anthropics/isabella-crypto/actions/workflows/ci.yml/badge.svg)](https://github.com/anthropics/isabella-crypto/actions/workflows/ci.yml)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)

***Isab***elle + ***Latt***ice Cryptography = ***Isabella***

Formally verified lattice-based cryptography in Isabelle/HOL with multi-language code generation.

## Overview

Isabella provides formally verified implementations of lattice-based cryptographic primitives. All code is extracted from machine-checked Isabelle/HOL proofs, guaranteeing mathematical correctness.

**Libraries:**
- **isabella.hs** - Haskell library with CLI
- **isabella.ml** - OCaml library with CLI
- **isabella.ts** - TypeScript/JavaScript library (via js_of_ocaml)

**Source:**
- **Canon/** - The verified Isabelle/HOL theories

## Quick Start

### Prerequisites

- [Isabelle](https://isabelle.in.tum.de/) 2024+ (2025-2 recommended)
- [GHC](https://www.haskell.org/ghc/) 9.4+ and [Cabal](https://www.haskell.org/cabal/) 3.0+ (for Haskell)
- [opam](https://opam.ocaml.org/) with OCaml 4.14+ (for OCaml/TypeScript)
- Node.js 16+ (for TypeScript)

### Building Everything

```bash
make all          # Build Canon + all libraries
make test         # Run all tests
make examples     # Run examples in all languages
```

### Individual Targets

```bash
make canon        # Build Isabelle theories
make haskell      # Build Haskell library
make ocaml        # Build OCaml library
make typescript   # Build TypeScript library
```

### Code Generation

To regenerate the Haskell and OCaml libraries from Isabelle:

```bash
./generate.sh                 # Full pipeline: build Canon + generate + compile
./generate.sh --build-only    # Skip Isabelle, just compile existing code
./generate.sh --run-examples  # Generate + build + run examples
./generate.sh --lang haskell  # Only Haskell
./generate.sh --lang ocaml    # Only OCaml
./generate.sh --clean         # Clean generated artifacts
```

## Project Structure

```
isabella-crypto/
├── Canon/                     # Verified Isabelle theories (source of truth)
│   ├── ROOT                   # Session definitions
│   ├── Prelude.thy            # Named theorems, mod utilities
│   ├── Algebra/
│   │   └── Zq.thy             # Modular arithmetic Z_q
│   ├── Linear/
│   │   └── ListVec.thy        # Vector/matrix operations
│   ├── Analysis/
│   │   └── Norms.thy          # L-infinity norm, bounds
│   ├── Gadgets/
│   │   └── Decomp.thy         # Base-B gadget decomposition
│   ├── Hardness/
│   │   ├── LWE_Def.thy        # LWE problem definition
│   │   └── SIS_Def.thy        # SIS problem definition
│   ├── Rings/
│   │   ├── PolyMod.thy        # Polynomial rings Z_q[X]/(X^n+1)
│   │   ├── ModuleLWE.thy      # Module-LWE and Module-SIS
│   │   └── NTT.thy            # Number Theoretic Transform (O(n log n))
│   └── Crypto/
│       ├── Regev_PKE.thy      # Regev public-key encryption
│       ├── Commit_SIS.thy     # SIS-based commitments
│       └── Kyber.thy          # CRYSTALS-Kyber (ML-KEM)
│
├── isabella.hs/               # Haskell library
│   ├── src/Canon/             # Generated/maintained modules
│   │   ├── Algebra/Zq.hs
│   │   ├── Linear/ListVec.hs
│   │   ├── Analysis/Norms.hs
│   │   ├── Gadgets/Decomp.hs
│   │   ├── Hardness/LWE_Def.hs
│   │   ├── Hardness/SIS_Def.hs
│   │   ├── Rings/PolyMod.hs
│   │   ├── Rings/ModuleLWE.hs
│   │   ├── Rings/NTT.hs
│   │   ├── Crypto/Regev_PKE.hs
│   │   ├── Crypto/Commit_SIS.hs
│   │   └── Crypto/Kyber.hs
│   ├── app/                   # CLI application
│   └── test/                  # Test suite
│
├── isabella.ml/               # OCaml library
│   ├── src/canon/             # Generated/maintained modules
│   │   ├── zq.ml
│   │   ├── listvec.ml
│   │   ├── norms.ml
│   │   ├── decomp.ml
│   │   ├── lwe_def.ml
│   │   ├── sis_def.ml
│   │   ├── polymod.ml
│   │   ├── modulelwe.ml
│   │   ├── ntt.ml
│   │   ├── regev_pke.ml
│   │   ├── commit_sis.ml
│   │   └── kyber.ml
│   ├── src/cli/               # CLI application
│   └── src/js/                # js_of_ocaml bindings
│
├── isabella.ts/               # TypeScript library (via js_of_ocaml)
│   ├── src/                   # TypeScript wrappers
│   └── examples/              # Tests and examples
│
├── Makefile                   # Build orchestration
├── generate.sh                # Code generation script
│
├── eval/                      # Evaluation harness
├── ralph/                     # Iterative proof orchestrator
├── bench/                     # Cross-language benchmarks
└── old/                       # Legacy code (archived)
```

## Available Modules

### Algebra & Analysis

| Module | Description | Key Functions |
|--------|-------------|---------------|
| `Zq` | Modular arithmetic over Z_q | `mod_centered`, `vec_mod`, `encode_bit`, `decode_bit` |
| `ListVec` | Vector and matrix operations | `vec_add`, `inner_prod`, `mat_vec_mult`, `transpose` |
| `Norms` | Vector norms and bounds | `linf_norm`, `all_bounded` |

### Hardness Assumptions

| Module | Description | Key Types |
|--------|-------------|-----------|
| `LWE_Def` | Learning With Errors problem | `LWEParams`, `LWEInstance`, `lwe_sample` |
| `SIS_Def` | Short Integer Solution problem | `SISParams`, `SISInstance`, `is_sis_solution` |

### Gadgets

| Module | Description | Key Functions |
|--------|-------------|---------------|
| `Decomp` | Base-B gadget decomposition | `digit`, `decomp_base`, `recompose`, `gadget_vec` |

### Polynomial Rings

| Module | Description | Key Functions |
|--------|-------------|---------------|
| `PolyMod` | Polynomial ring Z_q[X]/(X^n+1) | `poly_mult`, `ring_mod`, `ring_mult` |
| `ModuleLWE` | Module-LWE and Module-SIS | `mod_inner_prod`, `mod_mat_vec_mult`, `mlwe_sample` |
| `NTT` | Number Theoretic Transform | `ntt_fast`, `intt_fast`, `ntt_pointwise_mult` |

### Cryptographic Schemes

| Module | Description | Key Functions |
|--------|-------------|---------------|
| `Regev_PKE` | Regev public-key encryption | `regev_keygen`, `regev_encrypt`, `regev_decrypt` |
| `Commit_SIS` | SIS-based commitment scheme | `commit`, `verify_opening` |
| `Kyber` | CRYSTALS-Kyber (ML-KEM) | `kyber_keygen`, `kyber_encrypt`, `kyber_decrypt`, `kyber_encaps_simple` |

## Using the Libraries

### Haskell

```haskell
import Canon

-- Basic modular arithmetic
let x = mod_centered 15 17        -- => -2
let encoded = encode_bit 97 True  -- => 48

-- Vector operations
let dot = inner_prod [1,2,3] [4,5,6]  -- => 32

-- Gadget decomposition (base-2, 8 digits)
let digits = decomp_base 2 8 42   -- => [0,1,0,1,0,1,0,0]
let back = recompose 2 digits     -- => 42

-- NTT operations (O(n log n) Cooley-Tukey)
import Canon.Rings.NTT
let a_hat = ntt_fast [1,2,3,4] 17 3329 4
let a_back = intt_fast a_hat 17 3329 4

-- Kyber KEM
import Canon.Crypto.Kyber
-- Use kyber768Params for NIST Level 3 security
```

```bash
# Run CLI
cd isabella.hs && cabal run isabella-cli -- examples
```

### OCaml

```ocaml
open Canon

(* Basic modular arithmetic *)
let x = Zq.mod_centered 15 17        (* => -2 *)
let encoded = Zq.encode_bit 97 true  (* => 48 *)

(* Vector operations *)
let dot = Listvec.inner_prod [1;2;3] [4;5;6]  (* => 32 *)

(* Gadget decomposition *)
let digits = Decomp.decomp_base 2 8 42
let back = Decomp.recompose 2 digits  (* => 42 *)

(* NTT operations *)
let a_hat = Ntt.ntt_fast [1;2;3;4] 17 3329 4
let a_back = Ntt.intt_fast a_hat 17 3329 4
```

```bash
# Run CLI
cd isabella.ml && dune exec isabella_cli -- examples
```

### TypeScript

```typescript
import { Zq, Vec, Mat } from '@isabella/canon';

// Basic modular arithmetic
const x = Zq.modCentered(15, 17);     // => -2
const encoded = Zq.encodeBit(97, true); // => 48

// Vector operations
const dot = Vec.dot([1,2,3], [4,5,6]); // => 32

// Matrix operations
const A = [[1,2,3], [4,5,6]];
const Ax = Mat.vecMult(A, [1,1,1]);    // => [6, 15]
```

```bash
# Run examples
cd isabella.ts && node examples/example.mjs
```

## Canon - Verified Theories

The Canon is the source of truth - all library code corresponds to these formally verified Isabelle theories.

### Building Canon

```bash
cd Canon && isabelle build -D .
```

Or using the Makefile:

```bash
make canon
```

### Session Structure

Canon is organized into multiple Isabelle sessions:

| Session | Dependencies | Contents |
|---------|--------------|----------|
| `Canon_Base` | HOL | Prelude, ListVec, Zq, Norms |
| `Canon_Hardness` | Canon_Base | LWE_Def, SIS_Def |
| `Canon_Gadgets` | Canon_Base | Decomp |
| `Canon_Rings` | Canon_Hardness | PolyMod, ModuleLWE, NTT |
| `Canon_Crypto` | Canon_Rings | Regev_PKE, Commit_SIS, Kyber |

### Code Generation

Each theory includes `export_code` commands that specify what to export:

```isabelle
(* From NTT.thy *)
export_code
  ntt_params.make valid_ntt_params
  ntt_n ntt_q ntt_omega
  power_mod is_primitive_root
  twiddle twiddle_factors
  ntt_naive ntt_coeff
  intt_naive intt_coeff mod_inverse
  ntt_pointwise_mult
  butterfly ntt_fast intt_fast
  kyber_ntt_params dilithium_ntt_params
  in Haskell module_name "Canon.Rings.NTT"
```

## Development Workflow

### Adding a New Theory

1. Create the theory in `Canon/`:
   ```isabelle
   theory MyTheory
     imports Canon_Base.Prelude Canon_Base.ListVec
   begin
   (* definitions and proofs *)
   export_code my_function in Haskell module_name "Canon.MyTheory"
   end
   ```

2. Add to `Canon/ROOT`:
   ```
   session Canon_MySession in "MyDir" = Canon_Base +
     theories MyTheory
   ```

3. Build and verify:
   ```bash
   make canon
   ```

4. Create corresponding Haskell module in `isabella.hs/src/Canon/MyTheory.hs`

5. Create corresponding OCaml module in `isabella.ml/src/canon/mytheory.ml`

6. Update module lists in:
   - `isabella.hs/isabella.cabal` (exposed-modules)
   - `isabella.ml/src/canon/dune` (modules)
   - `isabella.hs/src/Canon.hs` (re-exports)
   - `isabella.ml/src/canon/canon.ml` (re-exports)

7. Build and test:
   ```bash
   make all
   make test
   ```

### Ralph Loop (Automated Theory Generation)

The Ralph Loop iteratively generates Isabelle theories with complete proofs:

```bash
ralph/isabella-loop.sh \
    --prompt canon-zq \
    --skill isabelle-basics \
    --skill isabelle-proofs \
    --iterations 5
```

### Step Loop (Incremental Development)

For incremental theory development:

```bash
ralph/step-loop.sh --prompt canon-linear-listvec \
    --output-dir Canon --theory-name ListVec --theory-path Linear \
    --session Canon_Base
```

### Benchmarks

Compare performance across languages:

```bash
./bench/run-benchmarks.sh
./bench/summarize.sh
```

## Tests

```bash
make test              # All tests
make test-haskell      # Haskell only
make test-ocaml        # OCaml only
make test-typescript   # TypeScript only
```

## Kyber (ML-KEM) Support

Isabella includes a complete implementation of CRYSTALS-Kyber (FIPS 203 ML-KEM):

```haskell
import Canon.Crypto.Kyber

-- Parameter sets
kyber512Params   -- NIST Level 1 (k=2)
kyber768Params   -- NIST Level 3 (k=3)
kyber1024Params  -- NIST Level 5 (k=4)

-- Key generation (requires randomness: matrix A, secret s, error e)
let (pk, sk) = kyber_keygen matrixA secretS errorE

-- Encryption (requires randomness: r, e1, e2)
let ciphertext = kyber_encrypt pk message randR errorE1 errorE2

-- Decryption
let recovered = kyber_decrypt sk ciphertext
```

The implementation uses O(n log n) NTT via Cooley-Tukey for efficient polynomial multiplication.

## Contributing

1. Add/modify theories in `Canon/`
2. Build and verify: `make canon`
3. Create/update library modules in `isabella.hs/` and `isabella.ml/`
4. Build libraries: `make all`
5. Run tests: `make test`

## License

MIT
