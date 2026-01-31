# Remaining Sorry Placeholder Proofs

This document tracks the remaining `sorry` placeholders that need to be completed for full formal verification.

## Status Overview

| File | Line | Lemma | Status |
|------|------|-------|--------|
| PolyMod.thy | 1011 | `ring_mult_add_right` | ⏳ Pending |
| PolyMod.thy | 1018 | `ring_mult_add_left` | ⏳ Pending |
| ModuleLWE.thy | 139 | `ring_mod_coeff_pad_zero` | ⏳ Pending |
| ModuleLWE.thy | 416 | `mod_mat_vec_mult_scale` | ⏳ Pending |
| Sigma_Base.thy | 412 | `linear_verify` | ⏳ Pending |
| Dilithium.thy | 340 | `usehint_makehint_correct` | ⏳ Pending |
| Dilithium.thy | 604 | `dilithium_correctness` | ⏳ Pending |

## Dependency Chain

```
PolyMod distributivity (ring_mult_add_right/left)
           ↓
ModuleLWE operations (ring_mod_coeff_pad_zero, mod_mat_vec_mult_scale)
           ↓
Sigma_Base completeness (linear_verify)

Hint mechanism (usehint_makehint_correct)
           ↓
Dilithium correctness (dilithium_correctness)
```

## Approach Notes

### PolyMod Distributivity
- Use `poly_mult_add_right`, `ring_mod_add`, `poly_mod` properties
- Requires showing that multiplying by reduced representative gives same result as sum of products
- Key insight: quotient ring structure preserves distributivity

### ModuleLWE Operations
- `ring_mod_coeff_pad_zero`: poly_coeff (poly_add p (replicate m 0)) k = poly_coeff p k
- `mod_mat_vec_mult_scale`: Factor scalar out using ring commutativity

### Sigma Protocol Completeness
- Depends on ModuleLWE lemmas
- Uses: `mod_mat_vec_mult_add_right`, `mod_mat_vec_mult_scale`

### Dilithium Correctness
- Hint mechanism: case analysis on hint bit values
- Main theorem: algebraic expansion + hint correctness
