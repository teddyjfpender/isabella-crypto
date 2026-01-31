# Remaining Sorry Placeholder Proofs

This document tracks the remaining `sorry` placeholders that need to be completed for full formal verification.

## Status Overview

| File | Line | Lemma | Status |
|------|------|-------|--------|
| PolyMod.thy | 1011 | `ring_mult_add_right` | ⏳ Pending - needs quotient ring infrastructure |
| PolyMod.thy | 1018 | `ring_mult_add_left` | ⏳ Pending - symmetric to above |
| ModuleLWE.thy | 139 | `ring_mod_coeff_add_zeros` | ✅ Completed |
| ModuleLWE.thy | 550 | `mod_mat_vec_mult_scale` | ⏳ Pending - blocked by distributivity |
| Sigma_Base.thy | 412 | `linear_verify` | ⏳ Pending - blocked by ModuleLWE |
| Dilithium.thy | 370 | `usehint_makehint_correct` (inner case) | ⏳ Partial - needs arithmetic reasoning |
| Dilithium.thy | 636 | `dilithium_correctness` | ⏳ Pending - blocked by hint correctness |

## Dependency Chain

```
PolyMod distributivity (ring_mult_add_right/left)
           ↓
ModuleLWE operations (mod_mat_vec_mult_scale)
           ↓
Sigma_Base completeness (linear_verify)

Hint mechanism (usehint_makehint_correct)
           ↓
Dilithium correctness (dilithium_correctness)
```

## Progress Notes

### Completed
- **ring_mod_coeff_add_zeros** (ModuleLWE.thy:139): Proven that adding zeros to a polynomial
  does not change its ring_mod_coeff. Key insight: poly_coeff returns 0 beyond length, so
  the sum of alternating terms is unaffected.

### PolyMod Distributivity (BLOCKED)

The key missing infrastructure is a lemma showing that multiplication respects the quotient ring
equivalence:

```isabelle
poly_mod (ring_mod (poly_mult a x) n) q =
poly_mod (ring_mod (poly_mult a (poly_mod (ring_mod x n) q)) n) q
```

This would allow proving that `ring_mult a (ring_add b c n q) n q` equals the reduced form
of multiplying by the unreduced sum.

**Required new lemmas:**
1. `ring_mult_poly_mod_equiv`: Multiplying by equivalent representatives gives equivalent results
2. `ring_mod_poly_mult`: How ring_mod interacts with poly_mult (coefficient-wise analysis)

### Dilithium Hint Mechanism (PARTIAL)

The `usehint_makehint_correct` lemma is partially structured:
- Case 1 (highbits equal): trivially follows from equality
- Case 2 (highbits differ): requires arithmetic reasoning about centered mod and decomposition

The case 2 proof needs to show that when highbits differ:
- If r0 > 0: (r1 + 1) mod (m + 1) = highbits(r + z)
- If r0 ≤ 0: (r1 - 1 + m + 1) mod (m + 1) = highbits(r + z)

This requires understanding the boundary behavior of the decompose function.

## Next Steps

1. **For PolyMod distributivity**: Develop the quotient ring equivalence lemmas. This is
   foundational infrastructure that enables the rest of the proofs.

2. **For Dilithium hint**: Complete the case analysis with explicit arithmetic reasoning
   about centered modular arithmetic.

3. Once distributivity is proven, the remaining proofs should follow more easily through
   the dependency chain.
