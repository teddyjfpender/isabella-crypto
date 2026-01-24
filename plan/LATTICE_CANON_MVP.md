# Lattice Crypto Canon — MVP Roadmap

**Goal**: A verified Isabelle library that scales from LWE/SIS basics → Module-LWE → commitments → LaZer-grade ZK.

**Principle**: Build in layers so later schemes reuse earlier lemmas verbatim.

---

## Architecture Overview

```
LAYER E — LaZer-grade ZK
    │ Σ-protocols, Fiat-Shamir, rejection sampling, relation proofs
    ▼
LAYER D — Modern Schemes
    │ Module-LWE/SIS, Kyber, Dilithium, NTT
    ▼
LAYER C — Core Constructions
    │ Regev PKE, SIS commitments, trapdoors
    ▼
LAYER B — Hardness Assumptions
    │ LWE/SIS definitions, normal forms, decision/search
    ▼
LAYER A — Math Substrate
    │ Z_q, vectors/matrices, norms, polynomials, modules, distributions
    ▼
HOL (stdlib)
```

---

## Current State (What Exists)

| Layer | Status | Notes |
|-------|--------|-------|
| A - Math | Partial | Vectors, matrices, Z_q ops, polynomial rings done |
| B - Hardness | Partial | LWE/SIS defs, NFSIS reduction done |
| C - Constructions | Partial | Regev PKE with full correctness proof |
| D - Modern | Not started | No Module-LWE, no Kyber/Dilithium |
| E - ZK | Not started | No Σ-protocol framework |

---

## MVP Session Structure

```
Canon/
├── ROOT
├── Prelude.thy                    # Session 0
├── Linear/
│   └── ListVec.thy                # Session 1
├── Algebra/
│   └── Zq.thy                     # Session 2
├── Analysis/
│   └── Norms.thy                  # Session 3
├── Prob/
│   └── DiscreteBasics.thy         # Session 4
├── Hardness/
│   ├── LWE_Def.thy                # Session 5.1
│   ├── SIS_Def.thy                # Session 5.2
│   └── NormalForms.thy            # Session 5.3
├── Crypto/
│   ├── Regev_PKE.thy              # Session 6
│   └── Commit_SIS.thy             # Session 9
├── Rings/
│   ├── PolyMod.thy                # Session 7.1
│   └── ModuleLWE.thy              # Session 7.2
├── Gadgets/
│   └── Decomp.thy                 # Session 8
└── ZK/
    └── Sigma_Base.thy             # Session 10
```

---

## Session Details

### Session 0 — Prelude.thy (Foundations)

**Goal**: One place for simp sets, notations, lightweight lemmas.

**Contents**:
- Notation: `vec_add`, `vec_sub`, `vec_scale`, `mat_mul`, `mat_vec`
- `named_theorems`: `mod_simp`, `vec_simp`, `mat_simp`, `dist_simp`
- Lemmas: `mod_add`, `mod_sub`, `mod_mult`, `mod_sum`, `sum_swap` helpers

**Export**: Nothing (infrastructure only)

---

### Session 1 — Linear/ListVec.thy (Vectors & Matrices)

**Goal**: List-based vectors/matrices with dimension discipline via locales.

**Contents**:
- `valid_vec`, `valid_matrix` (rectangular)
- `locale vec_space n` and `locale mat_space m n`
- Length-preservation and nth lemmas (`map2`, `transpose`, etc.)
- Dot product as sum over indices (`inner_prod_nth`)
- `iprod_transpose` theorem: `⟨s, Aᵀr⟩ = ⟨As, r⟩`

**Key Theorems (MVP)**:
- Bilinearity of dot product
- Transpose identity
- "mod commutes with dot product" lemmas

**Export**: Optional pure functions (`dot`, `mat_vec`)

**Reuses**: Prelude

---

### Session 2 — Algebra/Zq.thy (Modular Arithmetic)

**Goal**: Clean Z_q story usable everywhere.

**Two Paths**:
- **MVP (fast)**: Stay in `int` with `mod q`, prove rewrite lemmas
- **Better (later)**: Introduce typedef/quotient for Z_q

**Contents**:
- `mod_sum`, `mod_map`, `mod_dot`, `mod_matvec` (proved once)
- Centered distance `dist0` + invariance under mod
- `decode_bit` utilities

**Export**: `dist0`, `decode_bit`

**Reuses**: Prelude, ListVec

---

### Session 3 — Analysis/Norms.thy (Smallness Lemmas)

**Goal**: Norms on int vectors and cheap inequalities.

**Contents** (MVP doesn't need fancy norms):
- Absolute value bounds for dot product:
  ```
  |⟨e,r⟩| ≤ Σ |eᵢ|·|rᵢ|
  ```
- Coefficient-wise bounds:
  ```
  (|eᵢ| ≤ B ∧ |rᵢ| ≤ B') ⟹ |⟨e,r⟩| ≤ n·B·B'
  ```
- L∞ norm (existing), L2 norm (needed later)

**Export**: None

**Reuses**: Prelude, ListVec

---

### Session 4 — Prob/DiscreteBasics.thy (Distributions)

**Goal**: Minimal probabilistic scaffolding for security proofs.

**Contents** (keep minimal now, CryptHOL later):
- Define discrete uniform over Z_q
- Define "small error distribution" abstractly (set predicate or pmf)
- Closure facts (sum of small is small)

**Export**: None

**Reuses**: Prelude, Zq

---

### Session 5.1 — Hardness/LWE_Def.thy

**Goal**: Define LWE so multiple papers' conventions map to it.

**Contents**:
- `LWE_sample(A,s,e) = (A, As+e mod q)` variants
- Search/decision forms (definitions, not reductions yet)
- "Secret distribution" and "error distribution" as parameters

**Export**: None

**Reuses**: ListVec, Zq, Norms

---

### Session 5.2 — Hardness/SIS_Def.thy

**Goal**: SIS with standard matrix formulation.

**Contents**:
- `SIS(A, β)` = find nonzero x with Ax = 0 mod q and ‖x‖ ≤ β
- Inhomogeneous variant: Ax = t mod q

**Export**: None

**Reuses**: ListVec, Zq, Norms

---

### Session 5.3 — Hardness/NormalForms.thy

**Goal**: Normal form LWE/SIS equivalences matching lecture notes.

**Contents**:
- NFSIS ↔ SIS (from existing work)
- NFLWE ↔ LWE
- Short-secret LWE variant

**MVP**: Prove equivalence of formulations, not hardness reductions.

**Export**: Reduction functions

**Reuses**: LWE_Def, SIS_Def

---

### Session 6 — Crypto/Regev_PKE.thy

**Goal**: Refactored Regev using Sessions 1–3.

**Contents**:
- Keygen: `b = A·s + e mod q`
- Encrypt/Decrypt with `dist0` decode
- Clean correctness theorem

**MVP Correctness Theorem**:
```
Assumes:
  - dimensions valid (locale)
  - q > 0, q mod 4 = 0
  - |⟨e,r⟩| < q/4
Shows:
  decrypt(encrypt(m)) = m
```

**Proof**: ~10 lines using `decryption_error_term`, `decode_bit_small`, `decode_bit_half_shift`

**Export**: Executable encryption/decryption (toy but consistent)

**Reuses**: ListVec, Zq, Norms, LWE_Def

---

### Session 7.1 — Rings/PolyMod.thy

**Goal**: Polynomials mod q and mod f(X).

**Contents**:
- Polynomials as coefficient lists + mod q
- Quotient by cyclotomic-like f (keep f as parameter; no NTT yet)
- Convolution / multiplication in R_q
- `ring_add`, `ring_mult`, `ring_sub`

**Export**: Ring operations

**Reuses**: Prelude, Zq

---

### Session 7.2 — Rings/ModuleLWE.thy

**Goal**: Lift LWE/SIS to Module setting.

**Contents**:
- Vectors of ring elements
- Module dot products / matrix mult over R_q
- "dist0-style" notions for coefficients / norms (MVP: coefficient-wise bounds)

**This is the on-ramp to Kyber/Dilithium.**

**Export**: Module operations

**Reuses**: PolyMod, LWE_Def, SIS_Def

---

### Session 8 — Gadgets/Decomp.thy

**Goal**: Base-B decomposition and recomposition.

**Contents**:
- `decomp_B : Z → digits`
- `recompose(decomp(x)) = x` (exact)
- Bounds on digit sizes
- Gadget matrix G and lemma `G · decomp(x) = x`
- Module version for R_q

**Central for commitments and ZK relations.**

**Export**: Decomposition functions

**Reuses**: Zq, PolyMod

---

### Session 9 — Crypto/Commit_SIS.thy

**Goal**: Basic lattice commitment with correctness + security definitions.

**Contents**:
- Commitment: `com = A·r + m·G + e mod q` (gadget-based)
- Open correctness proof
- Binding/hiding definitions (leave as assumptions for now)

**This gives the "language" of relations LaZer proves.**

**Export**: Commitment operations

**Reuses**: ListVec, Zq, Gadgets, SIS_Def

---

### Session 10 — ZK/Sigma_Base.thy

**Goal**: Reusable 3-move protocol framework.

**Contents**:
- Transcript types
- Completeness theorem template
- Soundness definition template
- HVZK definition template
- One toy instance over linear relations

**Can port into CryptHOL game-based proofs later.**

**Export**: None (framework)

**Reuses**: Commit_SIS, Norms

---

## MVP Deliverable Checklist

At completion, you should have:

- [ ] **Linear algebra layer** where transpose/dot/mat-vec identities are proved once
- [ ] **mod/q + dist0 + decoding lemma pack** (`dist0_small`, `decode_bit_half_shift`, etc.)
- [ ] **Formal LWE and SIS definitions** with "normal form" equivalences
- [ ] **Tight Regev correctness theorem** with `q mod 4 = 0` and `|⟨e,r⟩| < q/4`
- [ ] **Basic gadget/decomposition layer**
- [ ] **Basic lattice commitment correctness theory**
- [ ] **Minimal Σ-protocol framework** (completeness skeleton)

---

## Dependency Graph

```
Prelude
    │
    ├──────────────────────────────────────┐
    ▼                                      ▼
ListVec                                  Zq
    │                                      │
    ├──────────────────────────────────────┤
    ▼                                      ▼
Norms                               DiscreteBasics
    │                                      │
    ├──────────────────────────────────────┤
    ▼                                      │
LWE_Def ◄──────────────────────────────────┘
    │
    ├─────────────┐
    ▼             ▼
SIS_Def      NormalForms
    │             │
    ▼             │
Regev_PKE ◄───────┘
    │
    ├─────────────┬─────────────┐
    ▼             ▼             ▼
PolyMod       Decomp      Commit_SIS
    │             │             │
    ▼             │             │
ModuleLWE ◄───────┴─────────────┤
    │                           │
    └───────────────────────────┤
                                ▼
                          Sigma_Base
```

---

## Reusable Lemma Patterns

### Pattern 1: Dimension Tracking via Locale
```isabelle
locale mat_space =
  fixes A :: int_matrix and m n :: nat
  assumes A_ok: "valid_matrix A m n"
begin
  lemma len_A: "length A = m"
  lemma rows_A: "row ∈ set A ⟹ length row = n"
end
```

### Pattern 2: Named Theorem Collections
```isabelle
named_theorems mod_simp "modular arithmetic simplification rules"
named_theorems vec_simp "vector operation simplification rules"

declare mod_add [mod_simp]
declare vec_add_length [vec_simp]

(* Usage: *)
lemma foo: "..." by (simp add: mod_simp vec_simp)
```

### Pattern 3: Smallness-Implies-Correctness
```isabelle
lemma decode_correct_if_small:
  assumes "abs (inner_prod e r) < q div 4"
  shows "decode_bit q (encode_bit q m + inner_prod e r) = m"
```

### Pattern 4: Bilinearity Kit
```isabelle
lemma inner_prod_vec_add:
  "length x = length y ⟹ length x = length r ⟹
   inner_prod (vec_add x y) r = inner_prod x r + inner_prod y r"

lemma inner_prod_scalar:
  "inner_prod (scalar_mult c v) w = c * inner_prod v w"
```

---

## Code Generation Strategy

**Executable layer** (export_code friendly):
- Use `int` with explicit `mod` operations
- Keep algorithms out of `SOME`/non-constructive choices
- Provide code equations for all exported definitions

**Proof layer** (can stay abstract):
- Use locales for dimension constraints
- Use abstract properties (don't need to be executable)

**Target languages**: Haskell, OCaml, SML, Scala

---

## Future Extensions (Post-MVP)

### Layer D — Modern Schemes
- [ ] NTT (Number Theoretic Transform) for efficient polynomial multiplication
- [ ] ML-KEM (Kyber) using ModuleLWE infrastructure
- [ ] ML-DSA (Dilithium) signatures
- [ ] FO/CCA transforms for KEM security

### Layer E — Full LaZer-Grade ZK
- [ ] Fiat-Shamir transcript hashing
- [ ] Rejection sampling / distribution closeness
- [ ] Full Σ-protocol instances
- [ ] Relation language for LaZer proofs

### Infrastructure
- [ ] CryptHOL integration for game-based security proofs
- [ ] Word-sized types for efficient implementation
- [ ] Property-based testing of extracted code

---

## Priority Order for Implementation

| Priority | Theory | Rationale |
|----------|--------|-----------|
| 1 | Prelude.thy | Everything imports this |
| 2 | ListVec.thy | Consolidate existing vector/matrix work |
| 3 | Zq.thy | Extract mod lemmas into reusable form |
| 4 | Norms.thy | Needed for all correctness proofs |
| 5 | LWE_Def.thy + SIS_Def.thy | Clean problem definitions |
| 6 | NormalForms.thy | Incorporate existing NFSIS work |
| 7 | Regev_PKE.thy | Refactor existing proof |
| 8 | Decomp.thy | Foundation for commitments |
| 9 | Commit_SIS.thy | First non-encryption primitive |
| 10 | PolyMod.thy | Ring infrastructure |
| 11 | ModuleLWE.thy | Bridge to modern schemes |
| 12 | DiscreteBasics.thy | Can be done in parallel |
| 13 | Sigma_Base.thy | ZK framework |

---

## Notes

- All proofs must be complete — NO `sorry` or `oops`
- Use locales to package dimension assumptions
- Keep "infrastructure theories" dependency-light
- Consider CryptHOL for security proofs later
- AFP's CRYSTALS-Kyber entry is a good reference for structure
