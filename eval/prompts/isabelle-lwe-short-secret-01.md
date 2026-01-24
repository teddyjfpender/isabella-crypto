# Prompt ID: isabelle-lwe-short-secret-01

## Task

Create an Isabelle/HOL theory implementing the polynomial-time reductions between Short-Secret LWE and standard LWE, with complete reduction algorithms, correctness proofs, and code export.

## Web References

For additional context on the algorithms, you may fetch these URLs:

| Topic | URL |
|-------|-----|
| LWE Survey | https://cims.nyu.edu/~regev/papers/lwesurvey.pdf |
| Simple LWE PKE Explanation | https://di-mgt.com.au/lattice-lwe-simple-pke.html |
| Isabelle Code Generation | https://isabelle.in.tum.de/doc/codegen.pdf |
| HOL-Library Reference | https://isabelle.in.tum.de/library/HOL/HOL-Library/index.html |

## Background: LWE and Short-Secret LWE

### The Learning With Errors (LWE) Problem

**LWE(n, m, q, χ)** (matrix form):
- Sample A ← ℤ_q^(n×m) uniformly
- Sample secret s ← ℤ_q^n uniformly
- Sample error e ← χ^m (each component from error distribution χ)
- Output (A, y^T) where y^T = s^T·A + e^T (mod q)

The **search** variant asks to find s given (A, y).
The **decision** variant asks to distinguish (A, y) from uniform.

### Short-Secret LWE (ssLWE)

**ssLWE(n, m, q, χ)**: Same as LWE, except:
- Secret s ← χ^n is also "short" (drawn from the error distribution)
- Error e ← χ^m as usual

This variant is important because:
1. It enables more efficient implementations (smaller keys)
2. It's used in practical schemes like NTRU-based constructions
3. Understanding its relationship to standard LWE is crucial for security analysis

### The Reduction Theorems

**Lemma (ssLWE ↔ LWE Reductions)**:

1. **ssLWE ≤_p LWE(n, m, q, χ)**: Short-secret LWE reduces to standard LWE with the same parameters.

2. **LWE(n, m, q, χ) ≤_p ssLWE(n, m+n, q, χ)**: Standard LWE reduces to short-secret LWE, but requires n additional samples.

## Requirements

### 1. Type Definitions

Define the following Isabelle types:

```
type_synonym int_vec = "int list"
type_synonym int_matrix = "int list list"
```

Define record types:
- `lwe_params`: n (dimension), m (samples), q (modulus)
- `lwe_instance`: matrix A, output vector y
- `lwe_secret`: secret vector s, error vector e
- `ss_lwe_instance`: same structure, but semantically the secret is short

### 2. Vector and Matrix Operations

Implement with definitions:

- `vec_add :: int_vec ⇒ int_vec ⇒ int_vec` — component-wise addition
- `vec_sub :: int_vec ⇒ int_vec ⇒ int_vec` — component-wise subtraction
- `vec_mod :: int_vec ⇒ int ⇒ int_vec` — component-wise modular reduction
- `inner_prod :: int_vec ⇒ int_vec ⇒ int` — inner product (dot product)
- `mat_vec_mult :: int_matrix ⇒ int_vec ⇒ int_vec` — matrix-vector multiplication (A·v)
- `vec_mat_mult :: int_vec ⇒ int_matrix ⇒ int_vec` — vector-matrix multiplication (s^T·A)
- `mat_mat_mult :: int_matrix ⇒ int_matrix ⇒ int_matrix` — matrix multiplication
- `split_cols :: int_matrix ⇒ nat ⇒ int_matrix × int_matrix` — split matrix columns at index
- `split_vec :: int_vec ⇒ nat ⇒ int_vec × int_vec` — split vector at index

### 3. LWE Instance Validity

Define predicates characterizing valid LWE instances:

```isabelle
(* Standard LWE: s uniform, e short *)
definition is_valid_lwe :: "lwe_params ⇒ lwe_instance ⇒ lwe_secret ⇒ bool" where
  "is_valid_lwe params inst sec = (
     length (s sec) = n params ∧
     length (e sec) = m params ∧
     y inst = vec_mod (vec_add (vec_mat_mult (s sec) (A inst)) (e sec)) (q params))"

(* Short-secret LWE: both s and e are short *)
definition is_valid_ss_lwe :: "lwe_params ⇒ lwe_instance ⇒ lwe_secret ⇒ bool" where
  "is_valid_ss_lwe params inst sec = (
     is_valid_lwe params inst sec ∧
     is_short (s sec))"  (* s drawn from error distribution *)
```

### 4. Reduction 1: ssLWE to LWE (Same Parameters)

This reduction "masks" the short secret with a uniform shift.

```isabelle
(* Transform ssLWE instance to standard LWE instance *)
definition sslwe_to_lwe :: "lwe_instance ⇒ int ⇒ int_vec ⇒ lwe_instance" where
  "sslwe_to_lwe ss_inst q r = ⦇
     A = A ss_inst,
     y = vec_mod (vec_add (y ss_inst) (vec_mat_mult r (A ss_inst))) q
   ⦈"

(* Transform ssLWE secret to LWE secret *)
definition sslwe_secret_to_lwe_secret :: "lwe_secret ⇒ int_vec ⇒ lwe_secret" where
  "sslwe_secret_to_lwe_secret ss_sec r = ⦇
     s = vec_add (s ss_sec) r,  (* s' = s + r is now uniform *)
     e = e ss_sec               (* error unchanged *)
   ⦈"

(* Inverse: recover ssLWE secret from LWE solution *)
definition lwe_secret_to_sslwe_secret :: "lwe_secret ⇒ int_vec ⇒ lwe_secret" where
  "lwe_secret_to_sslwe_secret lwe_sec r = ⦇
     s = vec_sub (s lwe_sec) r,  (* s = s' - r *)
     e = e lwe_sec
   ⦈"
```

### 5. Reduction 2: LWE to ssLWE (Needs m+n Samples)

This uses the "normal-form SIS trick" to eliminate the uniform secret.

```isabelle
(* Transform LWE instance (with m+n samples) to ssLWE instance (with m samples) *)
definition lwe_to_sslwe :: "lwe_instance ⇒ int ⇒ nat ⇒ lwe_instance" where
  "lwe_to_sslwe inst q n =
     (let (A0, B) = split_cols (A inst) (length (A inst ! 0) - n);
          (y0, y1) = split_vec (y inst) (length (y inst) - n);
          B_inv = mat_inverse_mod B q;
          s_tilde = vec_mat_mult y1 B_inv;         (* s̃ = y₁·B⁻¹ = s + e₁·B⁻¹ *)
          A_ss = mat_mat_mult_mod B_inv A0 q;     (* A_ss = B⁻¹·A₀ *)
          z0 = vec_mod (vec_sub y0 (vec_mat_mult s_tilde A0)) q
      in ⦇ A = A_ss, y = z0 ⦈)"

(* The new ssLWE secret structure *)
definition lwe_secret_to_sslwe_form :: "lwe_secret ⇒ nat ⇒ lwe_secret" where
  "lwe_secret_to_sslwe_form sec n =
     (let (e0, e1) = split_vec (e sec) (length (e sec) - n)
      in ⦇ s = vec_negate e1,   (* new short secret is -e₁ *)
           e = e0 ⦈)"            (* new error is e₀ *)
```

### 6. Correctness Lemmas

#### Lemma 1: Reduction 1 Correctness (ssLWE → LWE)

```isabelle
lemma reduction1_correctness:
  assumes "is_valid_ss_lwe params ss_inst ss_sec"
    and "length r = n params"
  shows "is_valid_lwe params (sslwe_to_lwe ss_inst (q params) r)
                            (sslwe_secret_to_lwe_secret ss_sec r)"
```

**Proof sketch**:
- Original: y = s^T·A + e (with short s)
- New: y' = y + r^T·A = (s+r)^T·A + e
- s' = s + r is uniform when r is uniform (masking)
- Error e is unchanged

#### Lemma 2: Reduction 1 Recovery

```isabelle
lemma reduction1_recovery:
  assumes "lwe_secret_to_sslwe_secret (sslwe_secret_to_lwe_secret ss_sec r) r = ss_sec"
  shows "s (lwe_secret_to_sslwe_secret lwe_sec r) = vec_sub (s lwe_sec) r"
```

#### Lemma 3: Reduction 2 Correctness (LWE → ssLWE)

```isabelle
lemma reduction2_correctness:
  assumes "is_valid_lwe params inst sec"
    and "A inst = concat_cols A0 B"
    and "is_invertible_mod B (q params)"
    and "m params = m_original + n params"  (* needs extra samples *)
  shows "is_valid_ss_lwe params' (lwe_to_sslwe inst (q params) (n params))
                                 (lwe_secret_to_sslwe_form sec (n params))"
```

**Proof sketch**:
- Let A = [A₀|B], y = [y₀|y₁], e = [e₀|e₁]
- y₀ = s^T·A₀ + e₀, y₁ = s^T·B + e₁
- Compute s̃ = y₁·B⁻¹ = s + e₁·B⁻¹ (noisy estimate of s)
- z₀ = y₀ - s̃·A₀ = s^T·A₀ + e₀ - (s + e₁·B⁻¹)·A₀
- z₀ = e₀ - e₁·(B⁻¹·A₀) = (-e₁)^T·A_ss + e₀
- This is ssLWE with short secret s_ss = -e₁ and error e_ss = e₀

#### Lemma 4: Parameter Relationship

```isabelle
lemma parameter_requirement:
  "reduction2 requires (m + n) samples to produce m-sample ssLWE"
```

### 7. Code Export

Export all core functions to multiple languages:

```isabelle
export_code
  vec_add vec_sub vec_mod inner_prod
  mat_vec_mult vec_mat_mult mat_mat_mult
  split_cols split_vec
  sslwe_to_lwe sslwe_secret_to_lwe_secret lwe_secret_to_sslwe_secret
  lwe_to_sslwe lwe_secret_to_sslwe_form
  in Haskell module_name "Lattice.LWE_Short_Secret"

export_code
  vec_add vec_sub vec_mod inner_prod
  mat_vec_mult vec_mat_mult mat_mat_mult
  split_cols split_vec
  sslwe_to_lwe sslwe_secret_to_lwe_secret lwe_secret_to_sslwe_secret
  lwe_to_sslwe lwe_secret_to_sslwe_form
  in SML module_name LWE_Short_Secret

export_code
  vec_add vec_sub vec_mod inner_prod
  mat_vec_mult vec_mat_mult mat_mat_mult
  split_cols split_vec
  sslwe_to_lwe sslwe_secret_to_lwe_secret lwe_secret_to_sslwe_secret
  lwe_to_sslwe lwe_secret_to_sslwe_form
  in OCaml module_name LWE_Short_Secret

export_code
  vec_add vec_sub vec_mod inner_prod
  mat_vec_mult vec_mat_mult mat_mat_mult
  split_cols split_vec
  sslwe_to_lwe sslwe_secret_to_lwe_secret lwe_secret_to_sslwe_secret
  lwe_to_sslwe lwe_secret_to_sslwe_form
  in Scala module_name LWE_Short_Secret
```

## Constraints

- **Theory name**: Must be `LatticeCrypto` (to match session configuration)
- **Imports**: `Main` and `HOL-Library.Code_Target_Numeral`
- **No sorry**: Aim for complete proofs on Reduction 1 (simpler). Reduction 2 may use `sorry` for complex matrix algebra.
- **Modular arithmetic**: Use `mod` consistently for all ℤ_q operations
- **Vector convention**: Use row vectors for secrets (s^T·A form) consistent with the mathematical description

## Proof Hints

1. For Reduction 1 (ssLWE → LWE):
   - Key insight: adding r^T·A to y is equivalent to shifting secret by r
   - Use distributivity: (s+r)^T·A = s^T·A + r^T·A
   - The error vector e is completely unchanged

2. For Reduction 2 (LWE → ssLWE):
   - Expand z₀ step by step using the LWE equation
   - Key identity: y₁·B⁻¹ = (s^T·B + e₁^T)·B⁻¹ = s^T + e₁^T·B⁻¹
   - Substitute and simplify to show z₀ = (-e₁)^T·(B⁻¹·A₀) + e₀^T

3. For helper lemmas:
   - `vec_add_assoc`: `vec_add (vec_add a b) c = vec_add a (vec_add b c)`
   - `vec_mat_mult_distrib`: `vec_mat_mult (vec_add s r) A = vec_add (vec_mat_mult s A) (vec_mat_mult r A)`

## Example Parameter Instantiation

For testing Reduction 1, use:
- n = 4 (dimension)
- m = 8 (samples)
- q = 97 (prime modulus)

For testing Reduction 2:
- Standard LWE: n = 4, m_input = 12 (i.e., m + n = 8 + 4)
- Resulting ssLWE: n = 4, m_output = 8

## Deliverable

A complete Isabelle theory file that:
1. Compiles with `isabelle build -d . LatticeCrypto`
2. Contains complete proofs for Reduction 1 correctness
3. Contains Reduction 2 with proof or justified `sorry`
4. Exports working Haskell code implementing both reductions
5. Demonstrates the relationship between LWE variants

## Mathematical Reference

### Reduction 1: ssLWE(n,m,q,χ) ≤_p LWE(n,m,q,χ)

```
Input: ssLWE instance (A, y) where y = s^T·A + e, s ← χ^n (short)
1. Sample r ← ℤ_q^n uniformly
2. Output LWE instance (A, y') where y' = y + r^T·A = (s+r)^T·A + e
   Now s' = s + r is uniform over ℤ_q^n

Recovery: Given LWE solution s', compute s = s' - r
```

### Reduction 2: LWE(n,m,q,χ) ≤_p ssLWE(n,m+n,q,χ)

```
Input: LWE instance with m+n samples
       A = [A₀|B] ∈ ℤ_q^(n×(m+n)), y = [y₀|y₁], y = s^T·A + e

1. Ensure B is invertible (permute columns if needed)
2. Compute s̃ = y₁·B⁻¹ = s + e₁·B⁻¹  (noisy secret estimate)
3. Compute A_ss = B⁻¹·A₀
4. Compute z₀ = y₀ - s̃·A₀

Output: ssLWE instance (A_ss, z₀)
Where: z₀ = (-e₁)^T·A_ss + e₀^T
       New secret: s_ss = -e₁ ∈ χ^n (short!)
       New error:  e_ss = e₀ ∈ χ^m (short!)
```

The key insight is that the n extra samples allow us to "consume" the uniform secret s and replace it with the short error vector e₁.
