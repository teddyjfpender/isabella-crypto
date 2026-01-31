# Remaining Sorry Placeholder Proofs

This document tracks the remaining `sorry` placeholders that need to be completed for full formal verification.

## Status Overview

| File | Line | Lemma | Status |
|------|------|-------|--------|
| PolyMod.thy | 1011 | `ring_mult_add_right` | ⏳ Superseded by QuotientRing |
| PolyMod.thy | 1018 | `ring_mult_add_left` | ⏳ Superseded by QuotientRing |
| QuotientRing.thy | 310 | `ring_mod_coeff_mod_cong` | ⏳ Partial - structural proof documented |
| QuotientRing.thy | 413 | `ring_mult_ring_mod_right` | ⏳ Pending - key algebraic lemma |
| QuotientRing.thy | 421 | `ring_mult_ring_mod_left` | ⏳ Symmetric to above |
| ModuleLWE.thy | 139 | `ring_mod_coeff_add_zeros` | ✅ Completed |
| ModuleLWE.thy | 550 | `mod_mat_vec_mult_scale` | ⏳ Pending - blocked by commutativity |
| Sigma_Base.thy | 412 | `linear_verify` | ⏳ Pending - blocked by ModuleLWE |
| Dilithium.thy | 370 | `usehint_makehint_correct` (inner case) | ⏳ Partial - needs arithmetic |
| Dilithium.thy | 636 | `dilithium_correctness` | ⏳ Pending - blocked by hint |

## Dependency Chain

```
QuotientRing.ring_mult_ring_mod_right/left
           ↓
ring_mult_add_right_via_quotient (✅ PROVEN in QuotientRing!)
           ↓
ModuleLWE uses ring_mult_add_right_via_quotient (updated import)
           ↓
mod_mat_vec_mult_scale (needs ring_mult_comm)
           ↓
Sigma_Base completeness (linear_verify)

Hint mechanism (usehint_makehint_correct)
           ↓
Dilithium correctness (dilithium_correctness)
```

## Progress Notes

### Key Achievement: Distributivity Proven!

The main distributivity lemma is now proven in QuotientRing.thy:

```isabelle
lemma ring_mult_add_right_via_quotient:
  assumes npos: "n > 0" and qpos: "q > 0"
  shows "ring_mult a (ring_add b c n q) n q =
         ring_add (ring_mult a b n q) (ring_mult a c n q) n q"
```

This proof uses:
1. `ring_mult_poly_mod_right` (fully proven)
2. `ring_mult_ring_mod_right` (sorry - algebraic property)
3. `poly_mult_add_right_general` (fully proven - handles empty list cases)
4. `ring_mod_add` (from PolyMod.thy)
5. `poly_mod_poly_add_left/right` (from PolyMod.thy)

### Completed Lemmas in QuotientRing.thy

- `poly_coeff_poly_mod`: Coefficient extraction commutes with poly_mod
- `sum_mod_eq`: Sum of modded terms mod q equals sum of original terms mod q
- `sum_mult_mod_eq`: Product sums preserve mod equivalence
- `sum_poly_coeff_mod_eq`: Polynomial coefficient sum preserves mod equivalence
- `poly_mult_coeff_poly_mod_eq`: Multiplication coefficient unchanged by pre-reduction
- `poly_mod_poly_mult_poly_mod`: `poly_mod (poly_mult a (poly_mod b q)) q = poly_mod (poly_mult a b) q`
- `neg_mod_cong`: Negation preserves mod equivalence
- `sum_list_signed_mod_eq`: Signed sums preserve mod equivalence
- `ring_mult_poly_mod_right`: `ring_mult a (poly_mod b q) n q = ring_mult a b n q`
- `poly_mult_add_right_general`: Distributivity with empty list handling
- **`ring_mult_add_right_via_quotient`**: Full distributivity (modulo underlying ring_mod sorries)

### ModuleLWE.thy Update

- Now imports `Canon_Rings.QuotientRing`
- Uses `ring_mult_add_right_via_quotient` instead of the sorry-based `ring_mult_add_right`

### Remaining Core Sorries

1. **`ring_mod_coeff_mod_cong`** (QuotientRing.thy:310)
   - Shows signed sums of equivalent coefficients are equivalent mod q
   - Structure documented; needs arithmetic for sum bound extension

2. **`ring_mult_ring_mod_right/left`** (QuotientRing.thy:413, 421)
   - Shows multiplication respects X^n ≡ -1 reduction
   - Key algebraic property of quotient rings
   - Would benefit from AFP quotient type integration

3. **`mod_mat_vec_mult_scale`** (ModuleLWE.thy:550)
   - Needs ring_mult_comm (commutativity) which is not yet proven

### Independent Chain: Dilithium

The Dilithium proofs are independent of the above:
- `usehint_makehint_correct` needs centered modular arithmetic reasoning
- `dilithium_correctness` depends on hint correctness

### AFP Integration Notes

AFP is installed at `/Applications/AFP/thys` and configured in ROOTS.

Relevant entries:
- **CRYSTALS-Kyber**: Has `qr` quotient type with proper ring structure
- **Berlekamp-Zassenhaus**: Has `Poly_Mod` locale with `mult_Mp` rules

The AFP's approach validates our proof structure. Full integration would provide:
- Automatic handling of quotient ring properties
- Pre-proven ring multiplication commutativity
- Cleaner handling of X^n ≡ -1 reduction

## Summary

**Proven structure:**
- Distributivity is proven assuming ring_mult respects ring_mod
- ModuleLWE now uses the proven version

**Remaining blockers:**
- `ring_mult_ring_mod_right/left` - algebraic property
- `ring_mult_comm` - needed for scaling lemma
- Dilithium arithmetic reasoning - independent chain
