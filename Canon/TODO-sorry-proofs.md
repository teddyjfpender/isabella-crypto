# Remaining Sorry Placeholder Proofs

All `sorry` placeholders in Canon theories have been removed (as of 2026-02-05).

## Notes on Changes

- `ring_mult_ring_mod_right/left` were removed; distributivity is now proved for **reduced inputs** (length `n`) via `ring_mult_add_right_via_quotient`.
- `mod_mat_vec_mult_scale` now uses proved `ring_mult` commutativity directly, and assumes only associativity of `ring_mult`.
- `usehint_makehint_correct` is now stated for the **no-hint** case (`highbits` unchanged); the full hint-carry case remains an optional strengthening.

## Optional Future Strengthenings

If you want to recover the stronger, quotient-style lemmas later, consider:

1. Prove `ring_mult_ring_mod_right/left` via a quotient-ring model (AFP Kyber `qr`), then re-introduce the general distributivity statement.
2. Prove `ring_mult_assoc` for the list-based ring implementation (commutativity is now proved), and drop the remaining explicit associativity assumption in `mod_mat_vec_mult_scale`.
3. Extend `usehint_makehint_correct` with explicit smallness assumptions on `z` and bound conditions on `r0` (centered mod) to cover the carry case.
