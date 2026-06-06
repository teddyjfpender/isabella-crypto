<div align="center">

```
██╗███████╗ █████╗ ██████╗ ███████╗██╗     ██╗      █████╗
██║██╔════╝██╔══██╗██╔══██╗██╔════╝██║     ██║     ██╔══██╗
██║███████╗███████║██████╔╝█████╗  ██║     ██║     ███████║
██║╚════██║██╔══██║██╔══██╗██╔══╝  ██║     ██║     ██╔══██║
██║███████║██║  ██║██████╔╝███████╗███████╗███████╗██║  ██║
╚═╝╚══════╝╚═╝  ╚═╝╚═════╝ ╚══════╝╚══════╝╚══════╝╚═╝  ╚═╝
```

**Formally Verified Lattice Cryptography**

*Isab*elle + *Latt*ice = **Isabella**

[![CI](https://img.shields.io/github/actions/workflow/status/teddyjfpender/isabella-crypto/ci.yml?branch=main&label=CI&logo=github)](https://github.com/teddyjfpender/isabella-crypto/actions/workflows/ci.yml)
[![License](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)
[![Isabelle](https://img.shields.io/badge/Isabelle-2025-blue.svg)](https://isabelle.in.tum.de/)
[![Tests](https://img.shields.io/badge/Tests-156%20passing-brightgreen.svg)](#tests)

</div>

---

## Overview

Isabella provides formally verified implementations of post-quantum cryptographic primitives. All code is extracted from machine-checked Isabelle/HOL proofs, guaranteeing mathematical correctness.

| Component | Description |
|-----------|-------------|
| **Canon/** | Verified Isabelle/HOL theories (source of truth) |
| **isabella.hs/** | Haskell library with CLI |
| **isabella.ml/** | OCaml library with CLI |
| **isabella.ts/** | TypeScript/JavaScript library (via js_of_ocaml) |
| **tests/** | Cross-validation against noble-post-quantum |

### Supported Algorithms

| Algorithm | Standard | Status |
|-----------|----------|--------|
| **ML-KEM** (Kyber) | FIPS 203 | Verified |
| **ML-DSA** (Dilithium) | FIPS 204 | Verified |
| **NTT** | - | O(n log n) Cooley-Tukey |
| **Regev PKE** | - | Verified |
| **SIS Commitments** | - | Verified |
| **Confidential Proof Slices** | - | SIS-note balance/range/nullifier MVP with 128-round domain-separated transcript challenges |

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
make test-sdk-equivalence  # Check shared SDK surface across targets
```

### Code Generation

`generate.sh` is fail-fast and export-only: it validates Isabelle exports and
library surfaces, then builds targets. It does not create handwritten fallback
stubs.

```bash
./generate.sh                 # Full pipeline: build Canon + verify exports + compile
./generate.sh --build-only    # Skip Isabelle, verify existing artifacts + compile
./generate.sh --run-examples  # Verify + build + run examples
./generate.sh --lang haskell  # Only Haskell
./generate.sh --lang ocaml    # Only OCaml
./generate.sh --lang typescript  # Only TypeScript/JS wrapper build
./generate.sh --clean         # Clean build artifacts
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
│       ├── Kyber.thy          # CRYSTALS-Kyber (ML-KEM / FIPS 203)
│       └── Dilithium.thy      # CRYSTALS-Dilithium (ML-DSA / FIPS 204)
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
│   │   ├── Crypto/Kyber.hs
│   │   └── Crypto/Dilithium.hs
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
│   │   ├── kyber.ml
│   │   └── dilithium.ml
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
└── bench/                     # Cross-language benchmarks
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
| `Kyber` | CRYSTALS-Kyber (ML-KEM / FIPS 203) | `kyber_keygen`, `kyber_encrypt`, `kyber_decrypt`, `kyber_encaps_simple` |
| `Dilithium` | CRYSTALS-Dilithium (ML-DSA / FIPS 204) | `power2round`, `decompose`, `highbits`, `lowbits`, `make_hint`, `use_hint` |

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

For namespace-safe parity with the OCaml `Canon.<Module>` surface, the Haskell
package also exposes alias modules such as `Canon.Zq`, `Canon.Kyber`, and
`Canon.Dilithium`:

```haskell
import qualified Canon.Zq as Zq
import qualified Canon.Dilithium as Dilithium
import qualified Canon.Confidential_balance as ConfidentialBalance
import qualified Canon.Confidential_range as ConfidentialRange
import qualified Canon.Confidential_transaction as ConfidentialTransaction

x = Zq.mod_centered 7 5
y = Dilithium.modCentered 1234567 (2 * Dilithium.dilGamma2 Dilithium.mldsa44Params)
z = Dilithium.power2Round 1234567 (Dilithium.dilD Dilithium.mldsa44Params)
params = ConfidentialBalance.makeScalarCommitParams 2 2 17 3
one = ConfidentialRange.oneOpening params
nk = [[0,1,0],[1,0,0]]
nf = ConfidentialTransaction.nullifier params nk one
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
import { Zq, Vec, Mat, Dilithium, ConfidentialBalance, ConfidentialRange, ConfidentialTransaction } from '@isabella/canon';

// Basic modular arithmetic
const x = Zq.modCentered(15, 17);     // => -2
const encoded = Zq.encodeBit(97, true); // => 48

// Vector operations
const dot = Vec.dot([1,2,3], [4,5,6]); // => 32

// Matrix operations
const A = [[1,2,3], [4,5,6]];
const Ax = Mat.vecMult(A, [1,1,1]);    // => [6, 15]

// ML-DSA helper surface
const params44 = Dilithium.params('44');
const split = Dilithium.power2Round(1234567, params44.d);
const hint = Dilithium.makeHint(2000, 100000, 2 * params44.gamma2);

// Confidential-balance proof slice
const cbParams = ConfidentialBalance.makeParams(2, 2, 17, 3);
const cbCommitment = ConfidentialBalance.randCommit(cbParams, [[5, 1, 2], [4, -1, 3]], [1, 2]);

// Confidential-range proof slice
const crParams = ConfidentialBalance.makeParams(2, 2, 17, 6);
const amountOpening = { msg: [5], rand: [1, 2] };
const bits = [
  { msg: [1], rand: [1, 0] },
  { msg: [0], rand: [0, 1] },
  { msg: [1], rand: [1, 1] },
];
const comps = [
  { msg: [0], rand: [0, 1] },
  { msg: [1], rand: [1, 0] },
  { msg: [0], rand: [0, -1] },
];
const cAmount = Zq.matVecMultMod([[5, 1, 2], [4, -1, 3]], Vec.concat(amountOpening.msg, amountOpening.rand), crParams.q);
const rangeProof = ConfidentialRange.fsProve(
  crParams,
  5,
  bits.length,
  [[5, 1, 2], [4, -1, 3]],
  cAmount,
  amountOpening,
  bits,
  comps,
  [0, 1],
  [[1, 0], [0, 0], [1, -1]]
);

// Confidential-transaction proof slice
const nk = [[2, 1, 0], [3, 1, 1]];
const nullifier = ConfidentialTransaction.nullifier(crParams, nk, amountOpening);
const semanticStep = ConfidentialTransaction.semanticStepValid;
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
| `Canon_Crypto` | Canon_Rings | Regev_PKE, Commit_SIS, Kyber, Dilithium |

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

### Theory Development

Canon theories are authored directly under `Canon/<Subdir>/<Theory>.thy` and
verified incrementally with Isabelle builds.

## End-to-End Algorithm Development

This section documents the complete workflow for adding a new formally verified cryptographic algorithm to Isabella, from initial specification to tested multi-language implementation.

### Overview

The pipeline consists of six stages:

```
┌─────────────┐    ┌─────────────┐    ┌─────────────┐
│  1. Spec    │───▶│  2. Theory  │───▶│ 3. Isabelle │
│   Design    │    │  Authoring  │    │    Proof    │
└─────────────┘    └─────────────┘    └─────────────┘
                                            │
┌─────────────┐    ┌─────────────┐    ┌─────────────┐
│  6. Test    │◀───│  5. Code    │◀───│ 4. Library  │
│   Harness   │    │   Export    │    │ Integration │
└─────────────┘    └─────────────┘    └─────────────┘
```

### Stage 1: Prompt Design

Create a structured algorithm specification in your PR notes or project docs.

The prompt should include:
- **Theory name and session**: Where it fits in the Canon hierarchy
- **Imports**: Dependencies from existing Canon theories
- **Step-by-step structure**: Incremental definitions with proofs
- **Parameters and types**: Data structures for the algorithm
- **Key operations**: Functions to implement with their specifications
- **Correctness properties**: Lemmas to prove
- **Export specification**: What to export for code generation

### Stage 2: Theory Authoring

Implement the theory directly in `Canon/<Subdir>/<Theory>.thy` and iterate in
small, semantics-preserving proof steps.

Typical loop:
1. Add definitions and lemmas for one logical step
2. Build the target session
3. Resolve proof obligations
4. Continue to the next step on success

**Handling failures**: If a step fails repeatedly, manual intervention may be needed:
- Check if required lemmas exist in `Canon/Prelude.thy`
- Look for similar patterns in existing theories (e.g., `Kyber.thy`)
- Simplify the proof goal or add helper lemmas

### Stage 3: Isabelle Proof Verification

Once the theory compiles, verify the full session:

```bash
cd Canon && isabelle build -v -D .
```

Key checks:
- All lemmas prove without `sorry`
- No `quick_and_dirty` mode in production
- Export code commands are present and correct

### Stage 4: Library Integration

Add the theory to each language library:

**Haskell** (`isabella.hs/`):
```bash
# Create module at src/Canon/Crypto/Dilithium.hs
# Add to isabella.cabal exposed-modules
# Add to src/Canon.hs re-exports
```

**OCaml** (`isabella.ml/`):
```bash
# Create module at src/canon/dilithium.ml
# Add to src/canon/dune modules list
# Add to src/canon/canon.ml re-exports
```

**CLI Commands**: Add operations to `isabella.ml/bin/isabella_cli.ml`:
```ocaml
let cmd_dil_power2round args = ...
(* Register in command dispatch *)
| "dil-power2round" -> cmd_dil_power2round args
```

### Stage 5: Code Export

Run the code generation pipeline:

```bash
./generate.sh              # Full rebuild
# or
make haskell ocaml         # Just the libraries
```

**Note**: Isabelle's raw export may use `zarith` types. Hand-written wrapper modules often provide cleaner interfaces:
```ocaml
(* dilithium.ml - Clean interface wrapping raw Isabelle export *)
let power2round_coeff r d =
  let two_d = 1 lsl d in
  let r0 = mod_centered r two_d in
  let r1 = (r - r0) / two_d in
  (r1, r0)
```

### Stage 6: Test Harness Validation

Add comprehensive tests in `tests/`:

**Reference tests** (`tests/src/dilithium.test.ts`):
```typescript
// Compare against noble-post-quantum or other reference implementations
import { ml_dsa44 } from '@noble/post-quantum/ml-dsa';

it('signs and verifies', () => {
  const keys = generateDsaKeyPair(ml_dsa44);
  const sig = signMessage(ml_dsa44, keys.secretKey, message);
  expect(verifySignature(ml_dsa44, keys.publicKey, message, sig)).toBe(true);
});
```

**CLI integration tests** (`tests/src/dilithium-integration.test.ts`):
```typescript
// Validate CLI against reference implementations
it('power2round matches reference', () => {
  const cliResult = dilPower2Round(100000, 13);
  const refResult = refPower2Round(100000, 13);
  expect(cliResult.r1).toBe(refResult[0]);
  expect(cliResult.r0).toBe(refResult[1]);
});
```

**CLI wrappers** (`tests/src/isabella-cli.ts`):
```typescript
export function dilPower2Round(r: number, d: number): Power2RoundResult {
  const output = runCli(['dil-power2round', r.toString(), d.toString()]);
  return parseCliResult<Power2RoundResult>(output);
}
```

Run the full test suite:
```bash
cd tests && bun test
```

### Example: Dilithium (ML-DSA)

The CRYSTALS-Dilithium implementation followed this exact workflow:

1. **Specification**: 12-step design for `Canon/Crypto/Dilithium.thy`
2. **Theory Authoring**: Implemented proofs directly in `Canon/Crypto/Dilithium.thy`
3. **Verification**: Built with `isabelle build -d Canon Canon_Crypto`
4. **Integration**:
   - `isabella.ml/src/canon/dilithium.ml` - OCaml wrapper
   - 10 CLI commands (`dil-params`, `dil-power2round`, etc.)
5. **Export**: Haskell/OCaml code generation
6. **Testing**:
   - 49 reference tests against noble-post-quantum
   - 27 CLI integration tests
   - Cross-validation of compression functions

### Quick Reference

| Stage | Command | Output |
|-------|---------|--------|
| Spec | Write algorithm spec in notes/docs | Specification file |
| Author | Edit `Canon/<Path>/<Theory>.thy` | Proven theory |
| Verify | `isabelle build -D Canon` | Proof checking |
| Integrate | Manual module creation | `isabella.{hs,ml}/` modules |
| Export | `./generate.sh` | Compiled libraries |
| Test | `cd tests && bun test` | Test results |

### Benchmarks

Compare performance across languages:

```bash
./bench/run-benchmarks.sh
./bench/summarize.sh
```

For the repaired confidential-token proving slice, use the deterministic
TypeScript benchmark harness:

```bash
make bench-typescript-confidential
cd isabella.ts && npm run bench:confidential -- --iterations 20 --warmup 5
cd isabella.ts && npm run bench:confidential -- --case transaction_fs_prove --iterations 5 --warmup 1
```

The harness measures the stable public proving entrypoints
`membershipProve`, `nullifierFsProve`, `ConfidentialBalance.fsProve`,
`ConfidentialRange.fsProve`, `ConfidentialTransaction.fsProve`, and one
end-to-end proving flow. Every timed proof is re-verified immediately, so the
benchmark fails if any benchmarked artifact is invalid.

For verifier hot paths, compare the current js_of_ocaml-backed TypeScript
runtime against native OCaml and Haskell CLI loops that parse the proof once
and benchmark `range_fs_verify` / `transaction_fs_verify` in-process:

```bash
make bench-confidential-verify
cd isabella.ts && npm run bench:verify -- --iterations 2 --warmup 0
```

The native benchmark commands are `cr-verify-bench` and
`ct-verify-bench-scaffold`. The scaffold transaction verifier is intentionally
named as scaffold-only; production transaction validation uses the Merkle
envelope verifier rather than the algebraic ledger-hash path.

## Tests

```bash
make test              # All tests
make test-haskell      # Haskell only
make test-ocaml        # OCaml only
make test-typescript   # TypeScript only
make test-validation   # Cross-validation against noble-post-quantum
```

### Cross-Validation Test Harness

The `tests/` directory contains a comprehensive test suite that validates the Isabelle-generated code against reference implementations:

- **156 tests** across 6 test suites
- Cross-validation with [noble-post-quantum](https://github.com/paulmillr/noble-post-quantum)
- CLI integration tests calling the OCaml executable
- FIPS 203 (ML-KEM) and FIPS 204 (ML-DSA) compliance checks

```bash
cd tests && bun install && bun test
```

See `tests/README.md` for detailed test documentation.

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

## Dilithium (ML-DSA) Support

Isabella includes compression and hint functions for CRYSTALS-Dilithium (FIPS 204 ML-DSA):

```ocaml
open Canon.Dilithium

(* Parameter sets *)
mldsa44_params   (* NIST Level 2: k=4, l=4 *)
mldsa65_params   (* NIST Level 3: k=6, l=5 *)
mldsa87_params   (* NIST Level 5: k=8, l=7 *)

(* Compression functions *)
let (r1, r0) = power2round_coeff r 13   (* Power2Round *)
let (r1, r0) = decompose r alpha        (* Decompose with alpha = 2*gamma2 *)
let hi = highbits r alpha               (* Extract high bits *)
let lo = lowbits r alpha                (* Extract low bits *)

(* Hint mechanism *)
let h = make_hint z r alpha             (* Create hint bit *)
let recovered = use_hint h r alpha      (* Recover high bits using hint *)

(* Bounds checking *)
let ok = check_bound value bound        (* Check |value| < bound *)
```

## Confidential Proof Slices

Isabella includes deterministic confidential-balance, confidential-range, and
confidential-transaction verifier slices over SIS commitments. The balance
slice proves that an aggregate input/output commitment opens to zero amount.
The range slice extends that with a bounded-amount proof by committing to bits
and complement bits and checking only zero-message residual commitments in the
Fiat-Shamir verifier. The confidential-transaction slice adds nullifiers,
membership witnesses against a commitment ledger, and a combined
ledger-validity-preserving transfer proof with explicit proof objects that can
be serialized across Haskell, OCaml, wasm, and TypeScript.

Current status and roadmap:
- [Confidential transfer roadmap](plan/CONFIDENTIAL_TRANSFERS_ROADMAP.md)
- [Confidential transfer production-readiness ledger](plan/CONFIDENTIAL_TRANSFERS_PRODUCTION_READINESS.md)
- [Confidential transfer protocol specification](plan/CONFIDENTIAL_TRANSFERS_PROTOCOL.md)
- The Fiat-Shamir layer now uses 128 domain-separated binary transcript rounds,
  and runtime backends use canonical transcript encoding with SHA3-256
  counter-mode challenge expansion. The HOL theory still treats Fiat-Shamir as
  a proof abstraction until a full security model is connected.
- Soundness and HVZK are stated as explicit extractor/simulator assumptions for
  the concrete proof slices; they are not yet full LaZer-grade proofs.
- The executable ledger hash remains a scaffold and is explicitly marked
  non-production; `Canon/ZK/Authenticated_Merkle.thy` is the checked target
  model for the cryptographic Merkle/hash replacement, with SHA3-256 encoding
  vectors in `tests/fixtures/confidential-merkle-vectors.json` and
  TypeScript/OCaml/Haskell Merkle APIs for leaf/node/root/path checks plus a
  separate Merkle-backed transaction verifier path. Native OCaml/Haskell CLI
  conformance now covers Merkle transaction proving and verification against
  the TypeScript SDK. The stable semantic ledger-step API now defaults to the
  Merkle-backed verifier; scaffold ledger-step calls remain available only as
  explicit compatibility APIs until they are retired.
- The transaction vector fixture also pins wallet proof request bytes for the
  SIS-note MVP: canonical context digest, accepted-root window, and
  spent-nullifier snapshot. TypeScript, OCaml, and Haskell expose matching
  digest APIs; consensus/indexer API contracts are still open production
  blockers.
- `bench/data/confidential-balance-realistic.json` records a 1024x1024
  `ct_sis_note_mvp_v0` balance proof-size/runtime benchmark; it is not a
  replacement for the external lattice-estimator and LaZer parameter gates.

System diagram:
- [Confidential token ASCII flow](docs/confidential-tokens-ascii.md)

Validation note:
- The repair path keeps proof objects JSON-friendly.
- Legacy balance proofs use `{ a, z }`.
- The in-flight repaired balance protocol may instead expose repeated rounds as
  `{ rounds: [{ a, z, challenge? }, ...] }` or `{ as, zs, challenges? }`.
- Legacy range proofs currently use
  `{ bits, comps, amountA, amountZ, pairAs, pairZs }`.
- Repaired range proofs may also appear as repeated rounds
  `{ bits, comps, rounds: [{ amountA, amountZ, pairAs, pairZs, challenge? }, ...] }`
  or as explicit list fields
  `{ bits, comps, amountAs, amountZs, pairAss, pairZss, challenges? }`.
- Legacy nullifier proofs use `{ aCommit, aNullifier, zMsg, zRand }`.
- Repaired nullifier proofs may also appear as repeated rounds
  `{ rounds: [{ aCommit, aNullifier, zMsg, zRand, challenge? }, ...] }`
  or as explicit list fields
  `{ aCommits, aNullifiers, zMsgs, zRands, challenges? }`.
- The audit and SDK-equivalence harnesses detect these proof surfaces explicitly
  and route them through the current CLI/runtime boundary without flattening
  them silently.
- Snapshot well-formedness (`ledgerValid`) is tracked separately from the
  semantic ledger-step verifier, exported on the stable TypeScript surface as
  Merkle-backed `ConfidentialTransaction.semanticStepValid` and
  `ConfidentialTransaction.ledgerStepValid`. The algebraic scaffold path
  remains available only through the explicit
  `ledgerStepValidScaffold` and `semanticStepValidScaffold` names.

```typescript
const params = ConfidentialBalance.makeParams(2, 2, 17, 3);
const ck = [[5, 1, 2], [4, -1, 3]];
const r = [1, 2];
const y = Array.from({ length: ConfidentialBalance.fsRounds() }, () => [0, 1]);
const c = ConfidentialBalance.randCommit(params, ck, r);
const proof = ConfidentialBalance.fsProve(params, 5, ck, c, r, y);
const ok = proof !== null && ConfidentialBalance.fsVerify(params, 5, ck, c, proof);

const rangeParams = ConfidentialBalance.makeParams(2, 2, 17, 6);
const amountOpening = { msg: [5], rand: [1, 2] };
const bitOpenings = [
  { msg: [1], rand: [1, 0] },
  { msg: [0], rand: [0, 1] },
  { msg: [1], rand: [1, 1] },
];
const compOpenings = [
  { msg: [0], rand: [0, 1] },
  { msg: [1], rand: [1, 0] },
  { msg: [0], rand: [0, -1] },
];
const cAmount = Zq.matVecMultMod(ck, Vec.concat(amountOpening.msg, amountOpening.rand), rangeParams.q);
const rangeProof = ConfidentialRange.fsProve(
  rangeParams,
  5,
  bitOpenings.length,
  ck,
  cAmount,
  amountOpening,
  bitOpenings,
  compOpenings,
  [0, 1],
  [[1, 0], [0, 0], [1, -1]]
);
const rangeOk = rangeProof !== null && ConfidentialRange.fsVerify(rangeParams, 5, ck, cAmount, rangeProof);

const nk = [[2, 1, 0], [3, 1, 1]];
const nf = ConfidentialTransaction.nullifier(rangeParams, nk, amountOpening);
const ledger = [
  cAmount,
  Zq.matVecMultMod(ck, Vec.concat([3], [0, 1]), rangeParams.q),
];
const membershipProof = ConfidentialTransaction.membershipProve(rangeParams, ledger, cAmount);
const nullifierOk = nf.length === rangeParams.m;
const membershipOk = membershipProof !== null
  && ConfidentialTransaction.membershipVerify(rangeParams, cAmount, membershipProof);
const semanticStep = ConfidentialTransaction.semanticStepValid;
// The full deterministic confidential-transfer fixture is exercised in
// isabella.ts/examples/test.mjs and the cross-SDK harnesses in tests/src/.
```

## Contributing

1. Add/modify theories in `Canon/`
2. Build and verify: `make canon`
3. Create/update library modules in `isabella.hs/` and `isabella.ml/`
4. Build libraries: `make all`
5. Run tests: `make test`

## License

MIT
