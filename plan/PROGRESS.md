# Implementation Progress Tracker

## Status Key
- ⬜ Not started
- 🔄 In progress
- ✅ Complete
- 🔶 Blocked

---

## Infrastructure

| Item | Status | Notes |
|------|--------|-------|
| Canon directory structure | ✅ | Created Canon/{Linear,Algebra,...} |
| Canon ROOT file | ✅ | Sessions: Canon_Base → Canon_ZK |
| step-loop.sh | ✅ | Step-based ralph loop |
| isabella-loop.sh updates | ✅ | Added --output-dir, --theory-name, --theory-path |
| isabelle-canon skill | ✅ | Infrastructure patterns |

## Prompts Created

| Prompt | Status | Notes |
|--------|--------|-------|
| canon-prelude | ✅ | Named theorems, mod lemmas |
| canon-linear-listvec | ✅ | Vectors, matrices, iprod_transpose |
| canon-algebra-zq | ✅ | dist0, encode/decode_bit, mat_vec_mult_mod |
| canon-analysis-norms | ✅ | linf_norm, all_bounded, inner_prod_bound |
| canon-hardness-lwe-def | ✅ | LWE params, lwe_sample, Search/Decision LWE |
| canon-crypto-regev-pke | ✅ | Regev PKE with correctness theorem |
| canon-hardness-sis-def | ✅ | SIS params, is_sis_solution, collision_to_sis |
| canon-gadgets-decomp | ✅ | Base-B decomposition, gadget_vec, recompose |
| canon-crypto-commit-sis | ✅ | SIS commitment with binding_implies_sis |
| canon-rings-polymod | ✅ | Polynomial ring R_q = Z_q[X]/(X^n+1) |
| canon-rings-modulelwe | ✅ | Module-LWE/SIS for Kyber/Dilithium |
| canon-rings-ntt | ✅ | NTT for O(n log n) polynomial multiplication |
| canon-crypto-kyber | ✅ | CRYSTALS-Kyber KEM (ML-KEM) |
| canon-crypto-dilithium | ✅ | CRYSTALS-Dilithium signatures (ML-DSA) |

---

## Phase 1: Foundation

| Theory | Status | Notes |
|--------|--------|-------|
| `Prelude.thy` | ✅ | Complete with hardened proofs |
| `Linear/ListVec.thy` | ✅ | Complete with iprod_transpose |
| `Algebra/Zq.thy` | ✅ | Complete with dist0, encode/decode_bit, mat_vec_mult_mod |
| `Analysis/Norms.thy` | ✅ | Complete with inner_prod_bound |
| `Prob/DiscreteBasics.thy` | ⬜ | Prompt needed |

**Blockers**: None

---

## Phase 2: Hardness Assumptions

| Theory | Status | Notes |
|--------|--------|-------|
| `Hardness/LWE_Def.thy` | ✅ | Complete with lwe_context locale |
| `Hardness/SIS_Def.thy` | ✅ | Complete with collision_to_sis |
| `Hardness/NormalForms.thy` | ⬜ | migrate NFSIS |

**Blockers**: Phase 1 completion

---

## Phase 3: Core Constructions

| Theory | Status | Notes |
|--------|--------|-------|
| `Crypto/Regev_PKE.thy` | ✅ | Complete with correctness theorem |
| `Gadgets/Decomp.thy` | ✅ | Complete with inner_prod_gadget_decomp |
| `Crypto/Commit_SIS.thy` | ✅ | binding_implies_sis theorem |

**Blockers**: None - Phase 3 complete

---

## Phase 4: Ring Infrastructure

| Theory | Status | Notes |
|--------|--------|-------|
| `Rings/PolyMod.thy` | ✅ | ring_mult, ring_add, ring_context locale |
| `Rings/ModuleLWE.thy` | ✅ | mlwe_context, msis_params, mod_inner_prod |
| `Rings/NTT.thy` | ✅ | ntt_naive, ntt_fast, kyber/dilithium params |

**Blockers**: None - Phase 4 complete

---

## Phase 4b: CRYSTALS Schemes (Layer D)

| Theory | Status | Notes |
|--------|--------|-------|
| `Crypto/Kyber.thy` | ✅ | kyber_keygen, kyber_encrypt, kyber_decrypt |
| `Crypto/Dilithium.thy` | ⬜ | Prompt ready: canon-crypto-dilithium |

**Blockers**: None - Kyber complete

---

## Phase 5: ZK Framework

| Theory | Status | Notes |
|--------|--------|-------|
| `ZK/Sigma_Base.thy` | ⬜ | new: 3-move protocols |

**Blockers**: Phase 4 completion

---

## Key Lemmas Checklist

### ListVec.thy
- [x] `vec_add_length`
- [x] `inner_prod_comm`
- [ ] `inner_prod_vec_add` (bilinearity) - not included
- [ ] `inner_prod_scalar` (bilinearity) - not included
- [x] `mat_vec_mult_length`
- [x] `iprod_transpose`
- [ ] `dot_append` - not included
- [ ] `mat_vec_mult_concat_cols` - not included
- [ ] `vec_space` locale - not included
- [ ] `mat_space` locale - not included

### Zq.thy
- [x] `mod_centered_cong`
- [x] `mod_centered_abs_bound`
- [x] `vec_mod`, `vec_mod_centered`
- [x] `dist0` definition
- [x] `dist0_small`
- [x] `decode_bit` definition
- [x] `encode_bit` definition
- [x] `decode_bit_small`
- [x] `decode_bit_half_shift`
- [x] `encode_decode_inverse`
- [x] `mat_vec_mult_mod`

### Norms.thy
- [ ] `l2_norm` definition
- [ ] `linf_norm` definition
- [ ] `inner_prod_bound`
- [ ] `small_coeff_bound`

### LWE_Def.thy
- [x] `lwe_sample` definition
- [x] `lwe_params` record
- [x] Search-LWE definition
- [x] Decision-LWE definition
- [x] `lwe_context` locale

### SIS_Def.thy
- [x] `sis_params` record
- [x] `sis_instance` record
- [x] `is_sis_solution` definition
- [x] `is_isis_solution` (inhomogeneous variant)
- [x] `collision_to_sis` lemma
- [x] `sis_context` locale

### NormalForms.thy
- [ ] NFSIS definition
- [ ] NFSIS ↔ SIS reduction
- [ ] Solution preservation

### Regev_PKE.thy
- [x] `regev_params` record (extends lwe_params)
- [x] `regev_keygen` definition
- [x] `regev_encrypt` definition
- [x] `regev_decrypt` definition
- [x] `payload_identity_raw` lemma
- [x] `regev_correctness` theorem
- [x] `noise_bound_from_params` lemma

### Decomp.thy
- [x] `digit` definition
- [x] `decomp_base` definition
- [x] `recompose` definition
- [x] `recompose_decomp_mod` theorem
- [x] `gadget_vec` definition
- [x] `inner_prod_gadget_decomp` theorem
- [x] `decomp_signed` (centered digits)

### Commit_SIS.thy
- [x] `commit_params` record
- [x] `commit` function
- [x] `verify_opening` function
- [x] `is_binding_break` definition
- [x] `binding_implies_sis` theorem
- [x] `commit_context` locale

### PolyMod.thy
- [x] `poly` type (coefficient list)
- [x] `poly_add`, `poly_sub`, `poly_mult`
- [x] `poly_mod` (coefficient reduction)
- [x] `ring_mod` (X^n + 1 reduction)
- [x] `ring_mult`, `ring_add`, `ring_sub`
- [x] `ring_params` record
- [x] `ring_context` locale

### ModuleLWE.thy
- [x] `mod_elem` type (poly list)
- [x] `mod_inner_prod` (ring element dot product)
- [x] `mod_mat_vec_mult`
- [x] `mlwe_params` record
- [x] `mlwe_sample` function
- [x] `is_mlwe_solution`, `is_real_mlwe_instance`
- [x] `msis_params` record
- [x] `is_msis_solution`
- [x] `mlwe_context` locale

### NTT.thy
- [x] `is_primitive_root` definition (2n-th root of unity)
- [x] `ntt_naive` transform
- [x] `intt_naive` inverse transform
- [x] `ntt_pointwise_mult` (pointwise multiplication)
- [x] `ntt_convolution` theorem
- [x] `ntt_inverse_correct` theorem
- [x] `ntt_params` record (n, q, omega)
- [x] `ntt_fast` Cooley-Tukey algorithm
- [x] `kyber_ntt_params`, `dilithium_ntt_params`

### Kyber.thy
- [x] `kyber_params` record (n=256, k, q=3329, eta)
- [x] `kyber512_params`, `kyber768_params`, `kyber1024_params`
- [x] `kyber_ntt`, `kyber_intt`, `kyber_poly_mult_ntt`
- [x] `kyber_inner_prod_ntt`, `kyber_mat_vec_mult_ntt`
- [x] `kyber_encode_msg`, `kyber_decode_msg`
- [x] `kyber_keygen`
- [x] `kyber_encrypt`, `kyber_decrypt`
- [x] `kyber_encaps_simple`, `kyber_decaps_simple`
- [x] `kyber_correct` locale with `kem_correctness` theorem

### Dilithium.thy (pending - Layer D)
- [ ] `dilithium_params` record (n=256, k, l, q=8380417, eta, gamma)
- [ ] `mldsa44_params`, `mldsa65_params`, `mldsa87_params`
- [ ] `power2round_coeff`, `power2round_vec`
- [ ] `highbits_coeff`, `lowbits_coeff`, `decompose_coeff`
- [ ] `makehint_coeff`, `usehint_coeff`
- [ ] `dil_keygen`
- [ ] `dil_sign` (with rejection sampling predicate)
- [ ] `dil_verify`
- [ ] `dilithium_correct` locale with `dilithium_correctness` theorem

### Sigma_Base.thy
- [ ] Transcript type
- [ ] Completeness definition
- [ ] Soundness definition
- [ ] HVZK definition
- [ ] Linear relation instance

---

## Code Export Status

| Module | Haskell | OCaml | SML | Scala |
|--------|---------|-------|-----|-------|
| ListVec | ✅ | ✅ | ⬜ | ⬜ |
| Zq | ✅ | ✅ | ⬜ | ⬜ |
| LWE_Def | ⬜ | ⬜ | ⬜ | ⬜ |
| SIS_Def | ⬜ | ⬜ | ⬜ | ⬜ |
| NormalForms | ⬜ | ⬜ | ⬜ | ⬜ |
| Regev_PKE | ⬜ | ⬜ | ⬜ | ⬜ |
| Decomp | ⬜ | ⬜ | ⬜ | ⬜ |
| Commit_SIS | ⬜ | ⬜ | ⬜ | ⬜ |
| PolyMod | ⬜ | ⬜ | ⬜ | ⬜ |
| ModuleLWE | ⬜ | ⬜ | ⬜ | ⬜ |

---

## Session Build Status

| Session | Compiles | Tests | Notes |
|---------|----------|-------|-------|
| Canon_Base | ✅ | N/A | Prelude + ListVec |
| Canon_Hardness | ⬜ | ⬜ | Waiting for Canon_Base completion |
| Canon_Crypto | ⬜ | ⬜ | |
| Canon_Rings | ⬜ | ⬜ | |
| Canon_ZK | ⬜ | ⬜ | |
| Canon_Full | ⬜ | ⬜ | |

---

## Notes / Decisions Log

*Record important decisions and notes here as implementation progresses.*

| Date | Decision |
|------|----------|
| 2026-01-24 | Created Canon library structure with layered sessions |
| 2026-01-24 | Implemented step-loop.sh for incremental theory development |
| 2026-01-24 | Completed Prelude.thy with hardened proofs (explicit case splits, type annotations) |
| 2026-01-24 | Added session-based verification to step-loop for dependent theories |
| 2026-01-24 | Key insight: `(n::int)` type annotation required for mod/div simplification |
| 2026-01-24 | Completed ListVec.thy with iprod_transpose (key LWE correctness lemma) |
| 2026-01-24 | Key insight: avoid `...` chaining with `simp add: algebra_simps` on nested sums - causes infinite loops |
| 2026-01-25 | Completed Zq.thy with full encode/decode machinery and mat_vec_mult_mod |
| 2026-01-25 | Key insight: witness approach for division - from `q mod n = 0`, derive `n dvd q`, obtain `k` where `q = n*k`, eliminates division from goals |
| 2026-01-25 | Added isabella.ts TypeScript library via js_of_ocaml (28 passing tests) |
| 2026-01-25 | Created canon-analysis-norms prompt for Norms.thy (next theory) |
| 2026-01-25 | Completed Norms.thy with inner_prod_bound lemma |
| 2026-01-25 | Completed LWE_Def.thy (Phase 2 started) |
| 2026-01-25 | Created canon-crypto-regev-pke prompt - the "crown jewel" correctness proof |
| 2026-01-25 | Completed Regev_PKE.thy (Phase 3 started) |
| 2026-01-25 | Created canon-hardness-sis-def prompt for SIS problem definition |
| 2026-01-25 | Completed SIS_Def.thy (Phase 2 complete) |
| 2026-01-25 | Created canon-gadgets-decomp prompt for base-B decomposition |
| 2026-01-25 | Completed Decomp.thy (gadget infrastructure) |
| 2026-01-25 | Created canon-crypto-commit-sis prompt for SIS-based commitments |
| 2026-01-25 | Completed Commit_SIS.thy (binding_implies_sis theorem) |
| 2026-01-25 | Created canon-rings-polymod prompt for polynomial rings |
| 2026-01-25 | Completed PolyMod.thy (R_q = Z_q[X]/(X^n+1) infrastructure) |
| 2026-01-25 | Created canon-rings-modulelwe prompt for Module-LWE/SIS |
| 2026-01-25 | Completed ModuleLWE.thy (mlwe_context, msis_params, mod_inner_prod) |
| 2026-01-25 | Created canon-rings-ntt prompt for Number Theoretic Transform (Layer D begins) |
| 2026-01-25 | Completed NTT.thy (ntt_naive, ntt_fast, kyber/dilithium params) |
| 2026-01-25 | Created canon-crypto-kyber prompt for CRYSTALS-Kyber (ML-KEM) |
| 2026-01-25 | Completed Kyber.thy (kyber_keygen, kyber_encrypt, kyber_decrypt, kem_correctness) |
| 2026-01-25 | Created canon-crypto-dilithium prompt for CRYSTALS-Dilithium (ML-DSA) |

---

## Future Extensions (Post-MVP)

### Layer D — Modern Schemes (after ModuleLWE)
| Theory | Description | Dependencies |
|--------|-------------|--------------|
| `Rings/NTT.thy` | Number Theoretic Transform for O(n log n) poly mult | PolyMod |
| `Crypto/Kyber.thy` | CRYSTALS-Kyber KEM (ML-KEM) | ModuleLWE, NTT |
| `Crypto/Dilithium.thy` | CRYSTALS-Dilithium signatures (ML-DSA) | ModuleLWE, NTT |
| `Crypto/FO_Transform.thy` | Fujisaki-Okamoto CCA transform | Kyber |

### Layer E — LaZer-Grade ZK (after Sigma_Base)
| Theory | Description | Dependencies |
|--------|-------------|--------------|
| `ZK/FiatShamir.thy` | Fiat-Shamir transcript hashing | Sigma_Base |
| `ZK/RejectionSampling.thy` | Distribution closeness proofs | Sigma_Base, Norms |
| `ZK/LinearRelations.thy` | Σ-protocols for linear relations | Sigma_Base, ModuleLWE |
