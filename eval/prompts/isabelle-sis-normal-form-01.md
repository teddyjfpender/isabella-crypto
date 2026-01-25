# Prompt ID: isabelle-sis-normal-form-01

## Task

Create an Isabelle/HOL theory implementing the polynomial-time equivalence between Normal-form SIS (systematic matrices) and general SIS, with complete reduction algorithms and correctness proofs, plus code export.

## Web References

For additional context on the algorithms, you may fetch these URLs:

| Topic | URL |
|-------|-----|
| LWE Survey (SIS Section) | https://cims.nyu.edu/~regev/papers/lwesurvey.pdf |
| Lattice Crypto Overview | https://eprint.iacr.org/2015/939.pdf |
| Isabelle Code Generation | https://isabelle.in.tum.de/doc/codegen.pdf |
| HOL-Library Reference | https://isabelle.in.tum.de/library/HOL/HOL-Library/index.html |

## Background: SIS and Normal-Form SIS

### The Short Integer Solution (SIS) Problem

**SIS(n, m, q, β)**: Given a uniformly random matrix A ∈ ℤ_q^(n×m) and a target vector b ∈ ℤ_q^n, find a short integer vector e ∈ ℤ^m satisfying:
- A·e ≡ b (mod q)
- ‖e‖_∞ ≤ β (or another norm bound)

The **homogeneous** version has b = 0; the **inhomogeneous** version has arbitrary b.

### Normal-Form (Systematic) SIS

**nfSIS(n, m, q, β)**: A restricted variant where the matrix has systematic form:

A_nf = [A₀ | I_n]

where A₀ ∈ ℤ_q^(n×(m-n)) and I_n is the n×n identity matrix.

Given b₀ ∈ ℤ_q^n, find short e = (x, y) ∈ ℤ^(m-n) × ℤ^n such that:
- A₀·x + y ≡ b₀ (mod q)
- ‖e‖_∞ ≤ β

### The Equivalence Theorem

**Lemma (Normal-form SIS ≡ SIS)**: Normal-form SIS is polynomial-time equivalent to general SIS. Both directions have efficient reductions.

## Requirements

### 1. Type Definitions

Define the following Isabelle types:

```
type_synonym int_vec = "int list"
type_synonym int_matrix = "int list list"
```

Define record types:
- `sis_params`: n (rows), m (columns), q (modulus), beta (norm bound)
- `sis_instance`: matrix A, target vector b
- `nf_sis_instance`: matrix A₀, target vector b₀ (systematic form implied)

### 2. Matrix and Vector Operations

Implement with definitions:

- `vec_add :: int_vec ⇒ int_vec ⇒ int_vec` — component-wise addition
- `vec_mod :: int_vec ⇒ int ⇒ int_vec` — component-wise modular reduction
- `mat_vec_mult :: int_matrix ⇒ int_vec ⇒ int_vec` — matrix-vector multiplication
- `mat_mat_mult :: int_matrix ⇒ int_matrix ⇒ int_matrix` — matrix multiplication
- `identity_matrix :: nat ⇒ int_matrix` — n×n identity matrix
- `concat_cols :: int_matrix ⇒ int_matrix ⇒ int_matrix` — horizontal concatenation [A|B]
- `split_vec :: int_vec ⇒ nat ⇒ int_vec × int_vec` — split vector at index k

### 3. Invertible Matrix Operations

These are conceptual (may use `sorry` for non-trivial computations):

- `is_invertible_mod :: int_matrix ⇒ int ⇒ bool` — check if matrix is invertible mod q
- `mat_inverse_mod :: int_matrix ⇒ int ⇒ int_matrix` — compute inverse mod q (may be partial/underspecified)
- `random_invertible_matrix :: nat ⇒ int ⇒ int_matrix` — sample from GL_n(ℤ_q) (specification only)

### 4. Solution Predicates

Define predicates that characterize valid solutions:

```isabelle
(* General SIS solution *)
definition is_sis_solution :: "sis_params ⇒ sis_instance ⇒ int_vec ⇒ bool" where
  "is_sis_solution params inst e = (
     length e = m params ∧
     vec_mod (mat_vec_mult (A inst) e) (q params) = vec_mod (b inst) (q params) ∧
     (∀i < length e. |e ! i| ≤ beta params))"

(* Normal-form SIS solution *)
definition is_nf_sis_solution :: "sis_params ⇒ nf_sis_instance ⇒ int_vec ⇒ bool" where
  "is_nf_sis_solution params inst e = (
     length e = m params ∧
     let (x, y) = split_vec e (m params - n params) in
     vec_mod (vec_add (mat_vec_mult (A0 inst) x) y) (q params) = vec_mod (b0 inst) (q params) ∧
     (∀i < length e. |e ! i| ≤ beta params))"
```

### 5. Reduction Functions

Implement both directions of the reduction:

#### Direction A: Reduce nfSIS to SIS

```isabelle
(* Transform nfSIS instance to SIS instance *)
definition nfsis_to_sis :: "nf_sis_instance ⇒ int ⇒ int_matrix ⇒ sis_instance" where
  "nfsis_to_sis nf_inst q B = ⦇
     A = mat_mat_mult_mod B (concat_cols (A0 nf_inst) (identity_matrix (length (b0 nf_inst)))) q,
     b = mat_vec_mult_mod B (b0 nf_inst) q
   ⦈"

(* Given SIS solution, extract nfSIS solution (identity mapping) *)
definition sis_sol_to_nfsis_sol :: "int_vec ⇒ int_vec" where
  "sis_sol_to_nfsis_sol e = e"
```

#### Direction B: Reduce SIS to nfSIS

```isabelle
(* Transform SIS instance to nfSIS instance *)
definition sis_to_nfsis :: "sis_instance ⇒ int ⇒ nat ⇒ nf_sis_instance" where
  "sis_to_nfsis inst q n =
     (let (A0, B) = split_cols (A inst) (length (A inst ! 0) - n);
          B_inv = mat_inverse_mod B q
      in ⦇ A0 = mat_mat_mult_mod B_inv A0 q,
           b0 = mat_vec_mult_mod B_inv (b inst) q ⦈)"

(* Given nfSIS solution, it is also SIS solution (identity) *)
definition nfsis_sol_to_sis_sol :: "int_vec ⇒ int_vec" where
  "nfsis_sol_to_sis_sol e = e"
```

### 6. Correctness Lemmas

State and prove these lemmas:

#### Lemma 1: Direction A Correctness
```isabelle
lemma reduction_A_correctness:
  assumes "is_invertible_mod B q"
    and "is_sis_solution params (nfsis_to_sis nf_inst q B) e"
  shows "is_nf_sis_solution params nf_inst e"
```

**Proof sketch**:
- The SIS solution e satisfies B·[A₀|I]·e ≡ B·b₀ (mod q)
- Left-multiply by B⁻¹: [A₀|I]·e ≡ b₀ (mod q)
- This is exactly the nfSIS equation; shortness is preserved

#### Lemma 2: Direction B Correctness
```isabelle
lemma reduction_B_correctness:
  assumes "is_invertible_mod B q"
    and "A inst = concat_cols A0_raw B"
    and "is_nf_sis_solution params (sis_to_nfsis inst q n) e"
  shows "is_sis_solution params inst e"
```

**Proof sketch**:
- The nfSIS solution e = (x,y) satisfies B⁻¹·A₀·x + y ≡ B⁻¹·b (mod q)
- Multiply by B: A₀·x + B·y ≡ b (mod q)
- This is [A₀|B]·e ≡ b, the original SIS equation

#### Lemma 3: Shortness Preservation
```isabelle
lemma shortness_preserved:
  "∀i < length e. |e ! i| ≤ β ⟹ ∀i < length e. |e ! i| ≤ β"
```

This is trivial (the reductions don't modify the solution vector).

### 7. Code Export

Export all core functions to multiple languages:

```isabelle
export_code
  vec_add vec_mod mat_vec_mult mat_mat_mult
  identity_matrix concat_cols split_vec
  is_sis_solution is_nf_sis_solution
  nfsis_to_sis sis_sol_to_nfsis_sol
  sis_to_nfsis nfsis_sol_to_sis_sol
  in Haskell module_name "Lattice.SIS_Normal_Form"

export_code
  vec_add vec_mod mat_vec_mult mat_mat_mult
  identity_matrix concat_cols split_vec
  is_sis_solution is_nf_sis_solution
  nfsis_to_sis sis_sol_to_nfsis_sol
  sis_to_nfsis nfsis_sol_to_sis_sol
  in SML module_name SIS_Normal_Form

export_code
  vec_add vec_mod mat_vec_mult mat_mat_mult
  identity_matrix concat_cols split_vec
  is_sis_solution is_nf_sis_solution
  nfsis_to_sis sis_sol_to_nfsis_sol
  sis_to_nfsis nfsis_sol_to_sis_sol
  in OCaml module_name SIS_Normal_Form

export_code
  vec_add vec_mod mat_vec_mult mat_mat_mult
  identity_matrix concat_cols split_vec
  is_sis_solution is_nf_sis_solution
  nfsis_to_sis sis_sol_to_nfsis_sol
  sis_to_nfsis nfsis_sol_to_sis_sol
  in Scala module_name SIS_Normal_Form
```

## Constraints

- **Theory name**: Must be `LatticeCrypto` (to match session configuration)
- **Imports**: `Main` and `HOL-Library.Code_Target_Numeral`
- **No sorry**: Aim for complete proofs on the main correctness lemmas. Matrix inversion internals may use `sorry` if necessary.
- **Modular arithmetic**: Use `mod` consistently for all ℤ_q operations

## Proof Hints

1. For reduction A correctness:
   - Use `unfolding` to expand definitions
   - Key step: B⁻¹·(B·x) = x (mod q) for invertible B
   - The vector e is unchanged, so shortness is automatic

2. For reduction B correctness:
   - The key algebraic identity: (B⁻¹·A₀)·x + y ≡ B⁻¹·b implies A₀·x + B·y ≡ b after multiplying by B
   - Use associativity of matrix multiplication

3. For helper lemmas:
   - `vec_mod_idemp`: `vec_mod (vec_mod v q) q = vec_mod v q`
   - `mat_vec_mult_mod_compat`: operations commute with mod appropriately

## Example Parameter Instantiation

For testing, use small parameters:
- n = 3 (rows)
- m = 6 (columns, so m-n = 3 for A₀)
- q = 17 (small prime)
- β = 2 (norm bound)

Example systematic matrix:
```
A_nf = [A₀ | I₃] where A₀ = [[2, 5, 3], [7, 1, 9], [4, 8, 6]] ∈ ℤ₁₇^(3×3)
```

## Deliverable

A complete Isabelle theory file that:
1. Compiles with `isabelle build -d . LatticeCrypto`
2. Contains complete proofs for the core correctness lemmas
3. Exports working Haskell code implementing the reductions
4. Demonstrates the polynomial-time equivalence between SIS variants

## Mathematical Reference

The equivalence can be summarized as:

```
Direction A (nfSIS → SIS):
  Input: (A₀, b₀) for A_nf = [A₀|I]
  1. Sample B ← GL_n(ℤ_q)
  2. Set A = B·[A₀|I], b = B·b₀
  3. Solve SIS(A, b) → e
  4. Return e (same vector solves nfSIS)

Direction B (SIS → nfSIS):
  Input: (A, b) with A = [A₀|B], B invertible
  1. Compute A_nf = [B⁻¹·A₀|I], b_nf = B⁻¹·b
  2. Solve nfSIS(B⁻¹·A₀, b_nf) → e
  3. Return e (same vector solves SIS)
```

Both reductions preserve solution shortness because they only transform the problem instance, not the solution vector.
