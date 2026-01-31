# Remaining Sorry Placeholder Proofs

This document tracks the remaining `sorry` placeholders that need to be completed for full formal verification.

## Status Overview

| File | Line | Lemma | Status |
|------|------|-------|--------|
| PolyMod.thy | 1011 | `ring_mult_add_right` | ⏳ Pending - needs quotient ring infrastructure |
| PolyMod.thy | 1018 | `ring_mult_add_left` | ⏳ Pending - symmetric to above |
| QuotientRing.thy | 258 | `ring_mod_coeff_mod_cong` | ⏳ Partial - structural proof done, inner sorry |
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

### QuotientRing Infrastructure (NEW - Partial)

Created `QuotientRing.thy` with key lemmas for quotient ring equivalence:

**Proven lemmas:**
- `poly_coeff_poly_mod`: Coefficient extraction commutes with poly_mod
- `sum_poly_coeff_mod_eq`: Sum of coefficient products with modded terms equals sum of unmodded (by induction)
- `poly_mult_coeff_poly_mod_eq`: Polynomial multiplication coefficient is unchanged when second operand is pre-reduced
- `poly_mod_poly_mult_poly_mod`: `poly_mod (poly_mult a (poly_mod b q)) q = poly_mod (poly_mult a b) q`
- `sum_list_signed_mod_eq`: Signed sums preserve mod equivalence
- `ring_mult_poly_mod_right`: `ring_mult a (poly_mod b q) n q = ring_mult a b n q`

**Remaining sorry (structural):**
- `ring_mod_coeff_mod_cong`: Shows ring_mod_coeff preserves mod equivalence when coefficients agree.
  The proof structure is complete (shows linearity argument), inner sorry for sum bound extension.

### AFP Integration (AVAILABLE)

AFP is now installed and configured:
- Location: `/Applications/AFP/thys`
- Configured in `~/.isabelle/Isabelle2025-2/ROOTS`

Relevant AFP entries for completing proofs:
- **CRYSTALS-Kyber**: Quotient ring `qr` type with `to_qr`/`of_qr` conversions
- **Berlekamp-Zassenhaus**: `Poly_Mod` locale with `mult_Mp` simp rules

The AFP's `mult_Mp` lemma directly proves our key property using the same approach
we've taken, which validates our proof structure.

### PolyMod Distributivity (BLOCKED)

The key missing infrastructure is showing multiplication respects the full quotient ring
equivalence (both mod q and mod X^n+1):

```isabelle
ring_mult a (ring_add b c n q) n q = ring_add (ring_mult a b n q) (ring_mult a c n q) n q
```

With `ring_mult_poly_mod_right` proven, the remaining piece is:
```isabelle
ring_mult a (ring_mod b n) n q = ring_mult a b n q
```

This requires showing that X^n ≡ -1 propagates through multiplication.

### Dilithium Hint Mechanism (PARTIAL)

The `usehint_makehint_correct` lemma is partially structured:
- Case 1 (highbits equal): trivially follows from equality
- Case 2 (highbits differ): requires arithmetic reasoning about centered mod and decomposition

The case 2 proof needs to show that when highbits differ:
- If r0 > 0: (r1 + 1) mod (m + 1) = highbits(r + z)
- If r0 ≤ 0: (r1 - 1 + m + 1) mod (m + 1) = highbits(r + z)

This requires understanding the boundary behavior of the decompose function.

## Next Steps

1. **Complete ring_mod_coeff_mod_cong**: The inner sorry involves showing that extending
   a signed sum to a common bound doesn't change the result mod q (since extra terms are 0).

2. **For full distributivity**: Prove `ring_mult a (ring_mod b n) n q = ring_mult a b n q`
   by showing multiplication respects the X^n ≡ -1 reduction.

3. **For Dilithium hint**: Complete the case analysis with explicit arithmetic reasoning
   about centered modular arithmetic.

4. **AFP Integration (Optional)**: Consider importing AFP's CRYSTALS-Kyber quotient type
   infrastructure for a cleaner approach to the remaining distributivity proofs.
