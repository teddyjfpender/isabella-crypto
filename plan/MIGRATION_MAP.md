# Migration Map: Current → Canon Structure

Maps existing theories to their new homes in the Canon structure.

---

## Source → Destination Mapping

### From `isabelle/theories/`

| Current File | → Canon Location | Action |
|--------------|------------------|--------|
| `Lattice_Basics.thy` | `Canon/Linear/ListVec.thy` | Refactor + extend |
| `Polynomial_Ring.thy` | `Canon/Rings/PolyMod.thy` | Refactor |
| `LWE.thy` | `Canon/Hardness/LWE_Def.thy` + `Canon/Crypto/Regev_PKE.thy` | Split |

### From `eval/work/isabelle-lwe-regev-01/`

| Current Content | → Canon Location | Action |
|-----------------|------------------|--------|
| `lwe_dims` locale | `Canon/Linear/ListVec.thy` | Extract generalized version |
| `dist0`, `decode_bit` lemmas | `Canon/Algebra/Zq.thy` | Extract |
| `iprod_transpose` | `Canon/Linear/ListVec.thy` | Move |
| Correctness theorems | `Canon/Crypto/Regev_PKE.thy` | Refactor to use new imports |

### From `eval/work/isabelle-sis-normal-form-01/`

| Current Content | → Canon Location | Action |
|-----------------|------------------|--------|
| SIS definitions | `Canon/Hardness/SIS_Def.thy` | Extract |
| NFSIS definitions | `Canon/Hardness/NormalForms.thy` | Move |
| Reduction proofs | `Canon/Hardness/NormalForms.thy` | Move |
| `dot_append`, bilinearity | `Canon/Linear/ListVec.thy` | Generalize |

---

## Lemma Consolidation Plan

### Vector/Matrix Lemmas → ListVec.thy

Collect from all sources:
```
vec_add_length          (Lattice_Basics, Regev)
inner_product_comm      (Lattice_Basics, Regev)
inner_prod_nth_min      (Regev)
inner_prod_vec_add      (Regev)
mat_vec_mult_length     (Regev)
iprod_transpose         (Regev locale)
dot_append              (SIS)
mat_vec_mult_concat_cols (SIS)
```

### Modular Arithmetic → Zq.thy

Collect:
```
mod_int, mod_centered   (Lattice_Basics)
vec_mod, vec_mod_centered (Lattice_Basics)
dist0                   (Regev)
dist0_small             (Regev)
dist0_half_shift        (Regev)
decode_bit_small        (Regev)
decode_bit_half_shift   (Regev)
encode_decode_inverse   (Regev)
inner_prod_mod_cong     (Regev)
vec_mod_idemp           (SIS)
```

### Dimension Locales → ListVec.thy

Generalize `lwe_dims` into:
```isabelle
locale vec_space =
  fixes n :: nat
  assumes n_pos: "n > 0"

locale mat_space =
  fixes m n :: nat
  assumes m_pos: "m > 0" and n_pos: "n > 0"

locale mat_vec_space = mat_space +
  fixes A :: int_matrix and v :: int_vec
  assumes A_ok: "valid_matrix A m n"
  assumes v_ok: "valid_vec v n"
```

---

## Named Theorem Collections to Create

### In Prelude.thy
```isabelle
named_theorems mod_simp   "modular arithmetic simp rules"
named_theorems vec_simp   "vector operation simp rules"
named_theorems mat_simp   "matrix operation simp rules"
named_theorems dist_simp  "distance/decoding simp rules"
named_theorems dim_simp   "dimension preservation simp rules"
```

### Populate from existing lemmas
```isabelle
declare vec_add_length [dim_simp]
declare scalar_mult_length [dim_simp]
declare mat_vec_mult_length [dim_simp]
declare inner_product_comm [vec_simp]
declare dist0_small [dist_simp]
declare decode_bit_small [dist_simp]
```

---

## Code Export Consolidation

### Current Exports (scattered)

| Theory | Exports To |
|--------|-----------|
| Lattice_Basics | Haskell: Lattice_Basics |
| Polynomial_Ring | Haskell: Polynomial_Ring |
| LWE | Haskell: LWE |
| Regev (eval) | Haskell/SML/OCaml/Scala: Lattice.LWE_Regev |
| SIS (eval) | Haskell/SML/OCaml/Scala: Lattice.SIS_Normal_Form |

### Target Structure

```
Canon/
├── export/
│   ├── haskell/
│   │   └── Lattice/
│   │       ├── Vector.hs      (from ListVec)
│   │       ├── Zq.hs          (from Zq)
│   │       ├── LWE.hs         (from LWE_Def)
│   │       ├── SIS.hs         (from SIS_Def)
│   │       ├── Regev.hs       (from Regev_PKE)
│   │       ├── Ring.hs        (from PolyMod)
│   │       ├── Gadget.hs      (from Decomp)
│   │       └── Commit.hs      (from Commit_SIS)
│   ├── ocaml/
│   ├── sml/
│   └── scala/
```

---

## ROOT File Structure

### Current ROOT (isabelle/)
```
session LatticeCrypto = HOL +
  sessions "HOL-Library" "HOL-Number_Theory"
  theories Lattice_Basics Polynomial_Ring LWE
```

### Target ROOT (Canon/)
```
session Canon_Base = HOL +
  sessions "HOL-Library" "HOL-Number_Theory"
  theories
    Prelude
    "Linear/ListVec"
    "Algebra/Zq"
    "Analysis/Norms"

session Canon_Hardness = Canon_Base +
  theories
    "Hardness/LWE_Def"
    "Hardness/SIS_Def"
    "Hardness/NormalForms"

session Canon_Crypto = Canon_Hardness +
  theories
    "Crypto/Regev_PKE"
    "Gadgets/Decomp"
    "Crypto/Commit_SIS"

session Canon_Rings = Canon_Crypto +
  theories
    "Rings/PolyMod"
    "Rings/ModuleLWE"

session Canon_ZK = Canon_Rings +
  theories
    "ZK/Sigma_Base"

session Canon_Full = Canon_ZK +
  (* everything *)
```

---

## Migration Phases

### Phase 1: Foundation (Sessions 0-3)
1. Create `Canon/` directory structure
2. Write `Prelude.thy` with named_theorems
3. Extract and consolidate `ListVec.thy` from existing sources
4. Extract and consolidate `Zq.thy`
5. Write `Norms.thy` (new content)

### Phase 2: Problems (Session 5)
1. Clean up `LWE_Def.thy` from existing LWE.thy
2. Clean up `SIS_Def.thy` from existing SIS work
3. Migrate `NormalForms.thy` from eval session

### Phase 3: Constructions (Sessions 6, 8, 9)
1. Refactor `Regev_PKE.thy` to use new imports
2. Write `Decomp.thy` (new)
3. Write `Commit_SIS.thy` (new)

### Phase 4: Rings (Session 7)
1. Refactor `PolyMod.thy` from Polynomial_Ring
2. Write `ModuleLWE.thy` (new)

### Phase 5: ZK (Session 10)
1. Write `Sigma_Base.thy` (new)

---

## Validation Checklist

After each phase, verify:
- [ ] All theories compile without `sorry`
- [ ] Code exports work for all target languages
- [ ] No circular dependencies
- [ ] Named theorem collections populated
- [ ] Dimension lemmas accessible via locales
