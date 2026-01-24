---
name: isabelle-canon
description: Infrastructure and patterns for the Lattice Crypto Canon - named theorems, locales, and layered architecture.
---

# Isabelle Canon Infrastructure

## Overview

The Canon is a layered Isabelle library for lattice cryptography. This skill covers:
- Named theorem collections for organized simp rules
- Locale-based dimension tracking
- Layer dependencies and import patterns
- Code export conventions

## Canon Architecture

```
Canon/
├── Prelude.thy           # named_theorems, common lemmas
├── Linear/
│   └── ListVec.thy       # vectors, matrices, locales
├── Algebra/
│   └── Zq.thy            # mod arithmetic, dist0, decode_bit
├── Analysis/
│   └── Norms.thy         # L2/L∞ norms, bounds
├── Hardness/
│   ├── LWE_Def.thy       # LWE problem definition
│   ├── SIS_Def.thy       # SIS problem definition
│   └── NormalForms.thy   # NFSIS ↔ SIS
├── Crypto/
│   ├── Regev_PKE.thy     # Regev encryption
│   └── Commit_SIS.thy    # SIS-based commitments
├── Gadgets/
│   └── Decomp.thy        # Base-B decomposition
├── Rings/
│   ├── PolyMod.thy       # R_q = Z_q[X]/(X^n+1)
│   └── ModuleLWE.thy     # Module-LWE/SIS
└── ZK/
    └── Sigma_Base.thy    # Σ-protocol framework
```

## Named Theorem Collections

Use named_theorems to organize simp rules:

```isabelle
named_theorems mod_simp "modular arithmetic simplification"
named_theorems vec_simp "vector operation simplification"
named_theorems mat_simp "matrix operation simplification"
named_theorems dim_simp "dimension preservation"
named_theorems dist_simp "distance and decoding"
```

Declare lemmas into collections:
```isabelle
lemma vec_add_length [dim_simp]: "length (vec_add v w) = min (length v) (length w)"
```

Use collections in proofs:
```isabelle
by (simp add: dim_simp mod_simp)
```

## Locale Pattern for Dimensions

The `lwe_dims` locale packages dimension constraints:

```isabelle
locale lwe_dims = mat_space +
  fixes A :: int_matrix and s r e :: int_vec
  assumes A_valid: "valid_matrix A m n"
  assumes s_valid: "valid_vec s n"
  assumes r_valid: "valid_vec r m"
  assumes e_valid: "valid_vec e m"
begin
  (* Derived lemmas available here *)
  lemma len_A: "length A = m"
  lemma len_s: "length s = n"

  (* The key identity *)
  lemma iprod_transpose:
    "inner_prod s (mat_transpose_vec_mult A r) = inner_prod (mat_vec_mult A s) r"
end
```

Use locale context in proofs:
```isabelle
context lwe_dims
begin
  lemma correctness: ...
    using iprod_transpose by ...
end
```

## Import Patterns

Each layer imports from previous layers:

```isabelle
(* In Algebra/Zq.thy *)
theory Zq
  imports "../Prelude" "../Linear/ListVec"
begin

(* In Hardness/LWE_Def.thy *)
theory LWE_Def
  imports "../Prelude" "../Linear/ListVec" "../Algebra/Zq" "../Analysis/Norms"
begin
```

**Rule**: Never skip layers. If you need Zq, also import ListVec.

## Code Export Conventions

Export to Canon namespace:
```isabelle
export_code
  definitions...
  in Haskell module_name "Canon.Linear.ListVec"
  in SML module_name ListVec
  in OCaml module_name ListVec
  in Scala module_name ListVec
```

## Critical Lemma Patterns

### Dimension Preservation
```isabelle
lemma operation_length [dim_simp]:
  "length (operation v) = length v"
```

### Bilinearity
```isabelle
lemma inner_prod_vec_add [vec_simp]:
  "length x = length y ⟹ length x = length r ⟹
   inner_prod (vec_add x y) r = inner_prod x r + inner_prod y r"
```

### Distance/Decoding
```isabelle
lemma dist0_small [dist_simp]:
  "q > 0 ⟹ |x| < q div 4 ⟹ dist0 q x = |x|"
```

## Response Checklist

- [ ] Theory name matches filename and session configuration
- [ ] Imports follow layer hierarchy (no skipping layers)
- [ ] Named theorems declared for key lemma categories
- [ ] Dimension lemmas marked [dim_simp]
- [ ] Locale used for packaging dimension constraints
- [ ] NO sorry/oops - complete proofs only
- [ ] Code export uses Canon.Section.Theory naming
- [ ] Proofs use appropriate collections (dim_simp, mod_simp, etc.)

## Quick Reference: Common Proofs

**Dimension preservation:**
```isabelle
by (simp add: operation_def)
```

**Bilinearity:**
```isabelle
by (induct v) (auto simp: inner_prod_def)
```

**Modular arithmetic:**
```isabelle
by (simp add: mod_simp)
```

**Transpose identity:**
```isabelle
unfolding inner_prod_def mat_vec_mult_def mat_transpose_vec_mult_def
by (auto simp: sum_list_swap)
```
