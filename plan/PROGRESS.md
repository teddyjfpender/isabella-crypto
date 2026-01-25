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

---

## Phase 1: Foundation

| Theory | Status | Notes |
|--------|--------|-------|
| `Prelude.thy` | ✅ | Complete with hardened proofs |
| `Linear/ListVec.thy` | ✅ | Complete with iprod_transpose |
| `Algebra/Zq.thy` | ✅ | Complete with dist0, encode/decode_bit, mat_vec_mult_mod |
| `Analysis/Norms.thy` | ⬜ | Prompt ready: canon-analysis-norms |
| `Prob/DiscreteBasics.thy` | ⬜ | Prompt needed |

**Blockers**: None

---

## Phase 2: Hardness Assumptions

| Theory | Status | Notes |
|--------|--------|-------|
| `Hardness/LWE_Def.thy` | ⬜ | clean from LWE.thy |
| `Hardness/SIS_Def.thy` | ⬜ | from SIS work |
| `Hardness/NormalForms.thy` | ⬜ | migrate NFSIS |

**Blockers**: Phase 1 completion

---

## Phase 3: Core Constructions

| Theory | Status | Notes |
|--------|--------|-------|
| `Crypto/Regev_PKE.thy` | ⬜ | refactor to use new imports |
| `Gadgets/Decomp.thy` | ⬜ | new: base-B decomposition |
| `Crypto/Commit_SIS.thy` | ⬜ | new: SIS commitment |

**Blockers**: Phase 2 completion

---

## Phase 4: Ring Infrastructure

| Theory | Status | Notes |
|--------|--------|-------|
| `Rings/PolyMod.thy` | ⬜ | refactor Polynomial_Ring |
| `Rings/ModuleLWE.thy` | ⬜ | new: Module-LWE/SIS |

**Blockers**: Phase 3 completion

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
- [ ] `lwe_sample` definition
- [ ] `lwe_params` record
- [ ] Search-LWE definition
- [ ] Decision-LWE definition

### SIS_Def.thy
- [ ] `sis_instance` record
- [ ] `is_sis_solution` definition
- [ ] Inhomogeneous variant

### NormalForms.thy
- [ ] NFSIS definition
- [ ] NFSIS ↔ SIS reduction
- [ ] Solution preservation

### Regev_PKE.thy
- [ ] `lwe_dims` locale (or use generic)
- [ ] `lwe_encrypt` definition
- [ ] `lwe_decrypt` definition
- [ ] `decryption_error_term` lemma
- [ ] `correctness_condition` theorem

### Decomp.thy
- [ ] `decomp_base` definition
- [ ] `recompose` definition
- [ ] `recompose_decomp` theorem
- [ ] Digit bound lemma
- [ ] Gadget matrix definition

### Commit_SIS.thy
- [ ] Commitment definition
- [ ] Opening definition
- [ ] Open correctness theorem
- [ ] Binding definition
- [ ] Hiding definition

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
