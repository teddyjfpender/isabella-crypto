# Lattice Crypto Canon

A layered Isabelle library for formally verified lattice-based cryptography.

## Overview

The Canon provides a structured foundation for lattice cryptography proofs, from basic mathematical infrastructure up to zero-knowledge proof systems.

## Architecture

```
┌─────────────────────────────────────────────────────────────────┐
│                         Canon_ZK                                 │
│                      (Sigma_Base)                                │
├─────────────────────────────────────────────────────────────────┤
│                        Canon_Rings                               │
│                   (PolyMod, ModuleLWE)                          │
├─────────────────────────────────────────────────────────────────┤
│                        Canon_Crypto                              │
│              (Regev_PKE, Commit_SIS, Decomp)                    │
├─────────────────────────────────────────────────────────────────┤
│                       Canon_Hardness                             │
│              (LWE_Def, SIS_Def, NormalForms)                    │
├─────────────────────────────────────────────────────────────────┤
│                        Canon_Base                                │
│         (Prelude, ListVec, Zq, Norms, DiscreteBasics)           │
└─────────────────────────────────────────────────────────────────┘
```

## Sessions

| Session | Parent | Description |
|---------|--------|-------------|
| `Canon_Base` | HOL | Mathematical infrastructure |
| `Canon_Hardness` | Canon_Base | Hardness assumptions (LWE, SIS) |
| `Canon_Crypto` | Canon_Hardness | Cryptographic constructions |
| `Canon_Rings` | Canon_Crypto | Ring/module variants |
| `Canon_ZK` | Canon_Rings | Zero-knowledge proofs |

## Theories

### Canon_Base

| Theory | Description |
|--------|-------------|
| `Prelude` | Named theorem collections, `mod_centered`, `abs_mod_less` |
| `Linear/ListVec` | List-based vectors and matrices with dimension discipline |
| `Algebra/Zq` | Modular arithmetic, `dist0`, `encode_bit`, `decode_bit` |
| `Analysis/Norms` | Infinity and L2 norms, bounds |
| `Prob/DiscreteBasics` | Discrete distributions for noise sampling |

### Canon_Hardness

| Theory | Description |
|--------|-------------|
| `Hardness/LWE_Def` | Learning With Errors problem definition |
| `Hardness/SIS_Def` | Short Integer Solution problem definition |
| `Hardness/NormalForms` | Hermite normal form, LWE variants |

### Canon_Crypto

| Theory | Description |
|--------|-------------|
| `Gadgets/Decomp` | Gadget matrices, bit decomposition |
| `Crypto/Regev_PKE` | Regev public-key encryption |
| `Crypto/Commit_SIS` | SIS-based commitment scheme |

### Canon_Rings (Future)

| Theory | Description |
|--------|-------------|
| `Rings/PolyMod` | Polynomial ring Z_q[X]/(X^n + 1) |
| `Rings/ModuleLWE` | Module-LWE for Kyber/Dilithium |

### Canon_ZK (Future)

| Theory | Description |
|--------|-------------|
| `ZK/Sigma_Base` | Sigma protocol framework |

## Building

```bash
# Build base layer
isabelle build -d . Canon_Base

# Build with hardness (requires Canon_Base)
isabelle build -d . Canon_Hardness

# Build everything
isabelle build -d . Canon_Full
```

## Development Workflow

New theories are added using the step-loop:

```bash
# 1. Create prompt in eval/prompts/canon-<name>.md
# 2. Run step-loop
ralph/step-loop.sh --prompt canon-<name> \
    --output-dir Canon \
    --theory-name <Name> \
    --theory-path <Subdir> \
    --session Canon_Base \
    --imports 'Canon_Base.Prelude' \
    --parent-session Canon_Base \
    --session-dir Canon

# 3. Update ROOT to include new theory
# 4. Verify session builds
isabelle build -d . Canon_Base
```

## Importing Canon Theories

To use Canon theories in your own development:

```isabelle
theory MyTheory
  imports Canon_Base.Prelude Canon_Base.ListVec
begin
  (* Your development here *)
end
```

Build with:
```bash
isabelle build -d /path/to/Canon -d . MySession
```

## Design Principles

### Proof Robustness

Canon proofs follow strict robustness guidelines:

1. **Explicit case splits** for conditionals (`if-then-else`)
2. **Type annotations** for numeric types (e.g., `(n::int)`)
3. **Prefer `arith` over `auto`** for div/mod arithmetic
4. **Named intermediate facts** for readability

### Named Theorem Collections

Prelude defines theorem collections for organized simplification:

```isabelle
named_theorems mod_simp   (* modular arithmetic rules *)
named_theorems vec_simp   (* vector operation rules *)
named_theorems mat_simp   (* matrix operation rules *)
named_theorems dim_simp   (* dimension preservation rules *)
named_theorems dist_simp  (* distance and decoding rules *)
```

Use in proofs:
```isabelle
by (simp add: mod_simp vec_simp)
```

### Dimension Discipline

Vector and matrix operations carry dimension constraints:

```isabelle
locale lwe_dims =
  fixes n m q :: nat
  assumes q_pos: "q > 2"
  assumes dims: "n > 0" "m > 0"
```

## Code Generation

Canon theories support Haskell code extraction:

```isabelle
export_code
  mod_centered vec_mod dist0 encode_bit decode_bit
  in Haskell module_name "Canon.Algebra.Zq"
```

After building, collect generated code:
```bash
./collect.sh --lang haskell
```

## Progress

See `plan/PROGRESS.md` for current implementation status.

| Layer | Status |
|-------|--------|
| Canon_Base | In Progress |
| Canon_Hardness | Planned |
| Canon_Crypto | Planned |
| Canon_Rings | Planned |
| Canon_ZK | Planned |
