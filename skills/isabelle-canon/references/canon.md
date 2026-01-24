# Canon Reference

## Session Structure

The Canon is organized into sessions that build on each other:

```
Canon_Base ← Canon_Hardness ← Canon_Crypto ← Canon_Rings ← Canon_ZK
```

### Canon_Base
- Prelude (infrastructure)
- Linear/ListVec (vectors, matrices)
- Algebra/Zq (modular arithmetic)
- Analysis/Norms (norm bounds)
- Prob/DiscreteBasics (distributions)

### Canon_Hardness
- Hardness/LWE_Def
- Hardness/SIS_Def
- Hardness/NormalForms

### Canon_Crypto
- Gadgets/Decomp
- Crypto/Regev_PKE
- Crypto/Commit_SIS

### Canon_Rings
- Rings/PolyMod
- Rings/ModuleLWE

### Canon_ZK
- ZK/Sigma_Base

## Key Definitions

### Validity Predicates

```isabelle
definition valid_vec :: "int_vec ⇒ nat ⇒ bool" where
  "valid_vec v n ≡ length v = n"

definition valid_matrix :: "int_matrix ⇒ nat ⇒ nat ⇒ bool" where
  "valid_matrix A m n ≡ length A = m ∧ (∀row ∈ set A. length row = n)"
```

### Distance from Zero

```isabelle
definition dist0 :: "int ⇒ int ⇒ int" where
  "dist0 q x = (let x' = x mod q in min x' (q - x'))"
```

### Bit Encoding

```isabelle
definition encode_bit :: "int ⇒ bool ⇒ int" where
  "encode_bit q b = (if b then q div 2 else 0)"

definition decode_bit :: "int ⇒ int ⇒ bool" where
  "decode_bit q x = (dist0 q x > q div 4)"
```

## Key Lemmas

### Transpose Identity (iprod_transpose)

In locale `lwe_dims`:
```isabelle
inner_prod s (mat_transpose_vec_mult A r) = inner_prod (mat_vec_mult A s) r
```

### Distance Lemmas

```isabelle
lemma dist0_small:
  "q > 0 ⟹ |x| < q div 4 ⟹ dist0 q x = |x|"

lemma dist0_half_shift:
  "q > 0 ⟹ q mod 4 = 0 ⟹ |x| < q div 4 ⟹
   dist0 q (x + q div 2) = q div 2 - |x|"
```

### Decoding Correctness

```isabelle
lemma decode_bit_small:
  "q > 0 ⟹ q mod 4 = 0 ⟹ |x| < q div 4 ⟹
   decode_bit q x = False"

lemma decode_bit_half_shift:
  "q > 0 ⟹ q mod 4 = 0 ⟹ |x| < q div 4 ⟹
   decode_bit q (x + q div 2) = True"
```

## Regev PKE Correctness

Main theorem (in `lwe_dims` locale):
```isabelle
theorem correctness_condition:
  assumes "q > 0" "q mod 4 = 0"
  assumes "|inner_prod e r| < q div 4"
  shows "lwe_decrypt sk q (lwe_encrypt pk q r m) = m"
```

Proof uses:
1. `decryption_error_term` - shows error equals `inner_prod e r`
2. `iprod_transpose` - key algebraic identity
3. `decode_bit_small` / `decode_bit_half_shift` - decoding works with bounded noise

## Named Theorem Categories

| Category | Purpose | Example |
|----------|---------|---------|
| `mod_simp` | Modular arithmetic | `mod_add`, `mod_mult` |
| `vec_simp` | Vector operations | `inner_prod_comm`, bilinearity |
| `mat_simp` | Matrix operations | `mat_vec_mult_nth` |
| `dim_simp` | Dimension preservation | `vec_add_length`, `mat_vec_mult_length` |
| `dist_simp` | Distance/decoding | `dist0_small`, `decode_bit_half_shift` |

## Locale Hierarchy

```
vec_space (n)
    ↓
mat_space (m, n)
    ↓
lwe_dims (A, s, r, e)
```

Each locale inherits from the previous and adds more structure.
