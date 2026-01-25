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

- [Isabelle](https://isabelle.in.tum.de/) 2024+
- [GHC](https://www.haskell.org/ghc/) and [Cabal](https://www.haskell.org/cabal/) (for Haskell)
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

## Project Structure

```
isabella-crypto/
├── Canon/                 # Verified Isabelle theories (source of truth)
│   ├── ROOT               # Session definitions
│   ├── Prelude.thy        # Named theorems, mod utilities
│   ├── Linear/            # Vector/matrix operations (ListVec.thy)
│   └── Algebra/           # Z_q arithmetic (Zq.thy)
│
├── isabella.hs/           # Haskell library (generated from Canon)
│   ├── src/Canon/         # Generated modules
│   ├── app/               # CLI application
│   └── test/              # Test suite
│
├── isabella.ml/           # OCaml library (generated from Canon)
│   ├── src/canon/         # Generated modules
│   ├── src/cli/           # CLI application
│   └── src/js/            # js_of_ocaml bindings
│
├── isabella.ts/           # TypeScript library (via js_of_ocaml)
│   ├── src/               # TypeScript wrappers
│   └── examples/          # Tests and examples
│
├── Makefile               # Build orchestration
├── generate.sh            # Code generation from Isabelle
│
├── eval/                  # Evaluation harness
├── ralph/                 # Iterative proof orchestrator
├── bench/                 # Cross-language benchmarks
└── old/                   # Legacy code (archived)
```

## Using the Libraries

### Haskell

```haskell
import qualified Canon.Algebra.Zq as Zq
import qualified Canon.Linear.ListVec as Vec

-- Centered modular reduction
let x = Zq.mod_centered 15 17  -- => -2

-- Vector operations
let v1 = [1, 2, 3]
let v2 = [4, 5, 6]
let sum = Vec.vec_add v1 v2    -- => [5, 7, 9]
let dot = Vec.inner_prod v1 v2 -- => 32

-- LWE bit encoding
let encoded = Zq.encode_bit 97 True   -- => 48
let decoded = Zq.decode_bit 97 48     -- => True
```

```bash
# Run CLI
cd isabella.hs && cabal run isabella-cli -- examples
```

### OCaml

```ocaml
open Canon

(* Centered modular reduction *)
let x = Zq.mod_centered 15 17  (* => -2 *)

(* Vector operations *)
let v1 = [1; 2; 3]
let v2 = [4; 5; 6]
let sum = Listvec.vec_add v1 v2    (* => [5; 7; 9] *)
let dot = Listvec.inner_prod v1 v2 (* => 32 *)

(* LWE bit encoding *)
let encoded = Zq.encode_bit 97 true   (* => 48 *)
let decoded = Zq.decode_bit 97 48     (* => true *)
```

```bash
# Run CLI
cd isabella.ml && dune exec isabella_cli -- examples
```

### TypeScript

```typescript
import { Zq, Vec, Mat } from '@isabella/canon';

// Centered modular reduction
const x = Zq.modCentered(15, 17);  // => -2

// Vector operations
const v1 = [1, 2, 3];
const v2 = [4, 5, 6];
const sum = Vec.add(v1, v2);    // => [5, 7, 9]
const dot = Vec.dot(v1, v2);    // => 32

// LWE bit encoding
const encoded = Zq.encodeBit(97, true);   // => 48
const decoded = Zq.decodeBit(97, 48);     // => true

// Matrix operations
const A = [[1, 2, 3], [4, 5, 6]];
const Ax = Mat.vecMult(A, [1, 1, 1]);     // => [6, 15]
const AxMod = Zq.matVecMultMod(A, [1, 1, 1], 10);  // => [6, 5]
```

```bash
# Run examples
cd isabella.ts && node examples/example.mjs
```

## Available Functions

### Zq - Modular Arithmetic

| Function | Description |
|----------|-------------|
| `mod_centered(x, q)` | Centered reduction to (-q/2, q/2] |
| `vec_mod(v, q)` | Element-wise modular reduction |
| `vec_mod_centered(v, q)` | Element-wise centered reduction |
| `dist0(q, x)` | Distance from zero in Z_q |
| `encode_bit(q, b)` | Encode bit for LWE (false→0, true→q/2) |
| `decode_bit(q, x)` | Decode bit from LWE |
| `mat_vec_mult_mod(A, v, q)` | Matrix-vector multiplication mod q |

### Vec - Vector Operations

| Function | Description |
|----------|-------------|
| `vec_add(v1, v2)` | Element-wise addition |
| `vec_sub(v1, v2)` | Element-wise subtraction |
| `scalar_mult(c, v)` | Scalar multiplication |
| `vec_neg(v)` | Negation |
| `inner_prod(v1, v2)` | Inner product (dot product) |
| `vec_concat(v1, v2)` | Concatenation |
| `split_vec(n, v)` | Split at position n |
| `valid_vec(n, v)` | Check dimension |

### Mat - Matrix Operations

| Function | Description |
|----------|-------------|
| `mat_vec_mult(A, v)` | Matrix-vector multiplication |
| `transpose(A)` | Matrix transpose |
| `valid_matrix(m, n, A)` | Check dimensions |

## Canon - Verified Theories

The Canon is the source of truth - all library code is extracted from these formally verified Isabelle theories.

### Building Canon

```bash
cd Canon && isabelle build -D .
```

### Structure

| Theory | Contents |
|--------|----------|
| `Prelude.thy` | Named theorems, utility lemmas |
| `Linear/ListVec.thy` | Vector/matrix operations with proofs |
| `Algebra/Zq.thy` | Z_q arithmetic, LWE encoding/decoding |

### Code Generation

Isabelle's `export_code` generates verified code:

```isabelle
export_code
  mod_centered vec_mod encode_bit decode_bit
  vec_add inner_prod mat_vec_mult transpose
  in Haskell module_name Canon
  in OCaml module_name Canon
```

## Development

### Ralph Loop

The Ralph Loop iteratively generates Isabelle theories with complete proofs:

```bash
ralph/isabella-loop.sh \
    --prompt canon-zq \
    --skill isabelle-basics \
    --skill isabelle-proofs \
    --iterations 5
```

### Step Loop

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
make test-haskell      # Haskell only (28 tests)
make test-ocaml        # OCaml only
make test-typescript   # TypeScript only (28 tests)
```

## Contributing

1. Add/modify theories in `Canon/`
2. Build and verify: `make canon`
3. Generate code: `./generate.sh`
4. Build libraries: `make all`
5. Run tests: `make test`

## License

MIT
