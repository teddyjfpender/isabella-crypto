# Prompt ID: canon-linear-listvec

## Task

Create the Canon/Linear/ListVec.thy theory file - list-based vectors and matrices with dimension discipline.

This is the core linear algebra layer that all cryptographic constructions depend on.

## Note on Theory Structure

The step-loop provides the theory header automatically. Your steps output content for inside `begin...end`.

## Step-Loop Invocation

```bash
./ralph/step-loop.sh --prompt canon-linear-listvec \
    --output-dir Canon \
    --theory-name ListVec \
    --theory-path Linear \
    --session Canon_Base \
    --imports 'Canon_Base.Prelude' \
    --parent-session Canon_Base \
    --session-dir Canon
```

## Steps

### Step 1: Type Synonyms

```isabelle
type_synonym int_vec = "int list"
type_synonym int_matrix = "int list list"
```

### Step 2: Validity Predicates

Define predicates for well-formed vectors and matrices:

```isabelle
definition valid_vec :: "int_vec ⇒ nat ⇒ bool" where
  "valid_vec v n ≡ length v = n"

definition valid_matrix :: "int_matrix ⇒ nat ⇒ nat ⇒ bool" where
  "valid_matrix A m n ≡ length A = m ∧ (∀row ∈ set A. length row = n)"
```

Prove basic validity lemmas:
1. `valid_vec_length`: `valid_vec v n ⟹ length v = n`
2. `valid_matrix_length`: `valid_matrix A m n ⟹ length A = m`
3. `valid_matrix_row`: `valid_matrix A m n ⟹ row ∈ set A ⟹ length row = n`

### Step 3: Vector Operations with Length Preservation

Define operations and prove length preservation:

```isabelle
definition vec_add :: "int_vec ⇒ int_vec ⇒ int_vec" where
  "vec_add v w = map2 (+) v w"

definition vec_sub :: "int_vec ⇒ int_vec ⇒ int_vec" where
  "vec_sub v w = map2 (-) v w"

definition scalar_mult :: "int ⇒ int_vec ⇒ int_vec" where
  "scalar_mult c v = map ((*) c) v"

definition vec_neg :: "int_vec ⇒ int_vec" where
  "vec_neg v = map uminus v"
```

Prove and declare as [dim_simp]:
1. `vec_add_length`: `length (vec_add v w) = min (length v) (length w)`
2. `vec_sub_length`: `length (vec_sub v w) = min (length v) (length w)`
3. `scalar_mult_length`: `length (scalar_mult c v) = length v`
4. `vec_neg_length`: `length (vec_neg v) = length v`

### Step 4: Inner Product

Define inner product and prove properties:

```isabelle
definition inner_prod :: "int_vec ⇒ int_vec ⇒ int" where
  "inner_prod v w = sum_list (map2 (*) v w)"
```

Or equivalently using fold:
```isabelle
definition inner_prod :: "int_vec ⇒ int_vec ⇒ int" where
  "inner_prod v w = (∑i<min (length v) (length w). v!i * w!i)"
```

Prove:
1. `inner_prod_comm`: `length v = length w ⟹ inner_prod v w = inner_prod w v`
2. `inner_prod_vec_add_left`: Bilinearity - `inner_prod (vec_add u v) w = inner_prod u w + inner_prod v w` (when lengths match)
3. `inner_prod_vec_add_right`: `inner_prod u (vec_add v w) = inner_prod u v + inner_prod u w`
4. `inner_prod_scalar_left`: `inner_prod (scalar_mult c v) w = c * inner_prod v w`
5. `inner_prod_scalar_right`: `inner_prod v (scalar_mult c w) = c * inner_prod v w`

Declare bilinearity lemmas as [vec_simp].

### Step 5: Matrix-Vector Multiplication

Define matrix-vector multiplication:

```isabelle
definition mat_vec_mult :: "int_matrix ⇒ int_vec ⇒ int_vec" where
  "mat_vec_mult A v = map (λrow. inner_prod row v) A"
```

Prove:
1. `mat_vec_mult_length`: `length (mat_vec_mult A v) = length A`
2. `mat_vec_mult_nth`: `i < length A ⟹ (mat_vec_mult A v) ! i = inner_prod (A ! i) v`

Declare as [dim_simp] and [mat_simp].

### Step 6: Matrix Transpose

Define transpose:

```isabelle
definition transpose :: "int_matrix ⇒ int_matrix" where
  "transpose A = (if A = [] then []
                  else map (λi. map (λrow. row ! i) A) [0..<length (hd A)])"
```

Prove:
1. `transpose_length`: `A ≠ [] ⟹ (∀row ∈ set A. length row = n) ⟹ length (transpose A) = n`
2. `transpose_row_length`: `valid_matrix A m n ⟹ row ∈ set (transpose A) ⟹ length row = m`
3. `transpose_nth`: Characterization of (transpose A) ! i ! j

### Step 7: Transpose-Vector Multiplication

Define A^T * v:

```isabelle
definition mat_transpose_vec_mult :: "int_matrix ⇒ int_vec ⇒ int_vec" where
  "mat_transpose_vec_mult A v = mat_vec_mult (transpose A) v"
```

### Step 8: Dimension Tracking Locale

Create a locale for managing dimension constraints:

```isabelle
locale vec_space =
  fixes n :: nat
  assumes n_pos: "n > 0"

locale mat_space =
  fixes m n :: nat
  assumes m_pos: "m > 0" and n_pos: "n > 0"

locale lwe_dims = mat_space +
  fixes A :: int_matrix and s :: int_vec and r :: int_vec and e :: int_vec
  assumes A_valid: "valid_matrix A m n"
  assumes s_valid: "valid_vec s n"
  assumes r_valid: "valid_vec r m"
  assumes e_valid: "valid_vec e m"
begin
  lemma len_A: "length A = m"
  lemma len_s: "length s = n"
  lemma len_r: "length r = m"
  lemma len_e: "length e = m"
  lemma len_rows: "row ∈ set A ⟹ length row = n"
  lemma len_As: "length (mat_vec_mult A s) = m"
  lemma len_At: "length (mat_transpose_vec_mult A r) = n"
end
```

### Step 9: The Key Transpose Identity

**This is the most important lemma for LWE correctness.**

Within the `lwe_dims` locale, prove:

```isabelle
lemma iprod_transpose:
  "inner_prod s (mat_transpose_vec_mult A r) = inner_prod (mat_vec_mult A s) r"
```

This says: ⟨s, A^T r⟩ = ⟨As, r⟩

Proof sketch:
- Expand definitions
- Show both equal ∑∑ A_ij * s_j * r_i
- Use commutativity of addition/multiplication

### Step 10: Concatenation Helpers (for SIS)

Define vector/matrix concatenation:

```isabelle
definition vec_concat :: "int_vec ⇒ int_vec ⇒ int_vec" where
  "vec_concat v w = v @ w"

definition split_vec :: "int_vec ⇒ nat ⇒ int_vec × int_vec" where
  "split_vec v k = (take k v, drop k v)"
```

Prove:
1. `vec_concat_length`: `length (vec_concat v w) = length v + length w`
2. `split_vec_concat`: `split_vec (vec_concat v w) (length v) = (v, w)`
3. `inner_prod_concat`: `inner_prod (vec_concat u v) (vec_concat x y) = inner_prod u x + inner_prod v y` (when lengths match)

### Step 11: Code Export

```isabelle
export_code
  valid_vec valid_matrix
  vec_add vec_sub scalar_mult vec_neg
  inner_prod
  mat_vec_mult transpose mat_transpose_vec_mult
  vec_concat split_vec
  in Haskell module_name "Canon.Linear.ListVec"
```

## Constraints

- Theory name: `ListVec`
- Imports only `../Prelude`
- No sorry/oops
- All dimension lemmas must be declared [dim_simp]
- Bilinearity lemmas declared [vec_simp]
- The `iprod_transpose` lemma is critical - take time to get it right

## Proof Hints

1. For `inner_prod` properties, often need `by (simp add: inner_prod_def sum_list_def)`
2. Induction on lists is useful for sum properties
3. For transpose proofs, work with indices explicitly
4. `iprod_transpose` proof: expand to sums, then use sum reordering lemmas
5. Use `nth_map` and `length_map` from HOL-Library

## Mathematical Reference

The transpose identity is fundamental:
```
⟨s, A^T r⟩ = ∑_i s_i (A^T r)_i
           = ∑_i s_i (∑_j A_ji r_j)
           = ∑_i ∑_j A_ji s_i r_j
           = ∑_j (∑_i A_ji s_i) r_j
           = ∑_j (As)_j r_j
           = ⟨As, r⟩
```

## Deliverable

A working ListVec.thy that:
1. Compiles with Canon_Base session
2. Provides all vector/matrix operations
3. Has the `lwe_dims` locale with `iprod_transpose`
4. Exports to Haskell
