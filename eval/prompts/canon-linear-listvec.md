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

## Proof Robustness Guidelines

**CRITICAL**: Follow these rules for robust proofs that work across Isabelle versions.

1. **If exact code is provided, USE IT EXACTLY** - do not simplify or "improve"
2. **Type annotations** are sometimes required - e.g., `(n::nat)`
3. **Explicit case splits** for conditionals - use `proof (cases "condition")`
4. **Use `arith` for arithmetic** involving nat/int inequalities
5. **Name intermediate facts** for readability and debugging
6. **For sums over indices**, use `(\<Sum>i = 0 ..< n. ...)` syntax

## Steps

### Step 1: Type Synonyms

**USE THIS EXACT CODE**:
```isabelle
type_synonym int_vec = "int list"
type_synonym int_matrix = "int list list"
```

### Step 2: Validity Predicates

**USE THIS EXACT CODE**:
```isabelle
definition valid_vec :: "int_vec => nat => bool" where
  "valid_vec v n = (length v = n)"

definition valid_matrix :: "int_matrix => nat => nat => bool" where
  "valid_matrix A m n = (length A = m \<and> (\<forall>row \<in> set A. length row = n))"

lemma valid_vec_length: "valid_vec v n \<Longrightarrow> length v = n"
  by (simp add: valid_vec_def)

lemma valid_matrix_length: "valid_matrix A m n \<Longrightarrow> length A = m"
  by (simp add: valid_matrix_def)

lemma valid_matrix_row: "valid_matrix A m n \<Longrightarrow> row \<in> set A \<Longrightarrow> length row = n"
  by (simp add: valid_matrix_def)
```

### Step 3: Vector Operations

**USE THIS EXACT CODE**:
```isabelle
definition vec_add :: "int_vec => int_vec => int_vec" where
  "vec_add v w = map2 (+) v w"

definition vec_sub :: "int_vec => int_vec => int_vec" where
  "vec_sub v w = map2 (-) v w"

definition scalar_mult :: "int => int_vec => int_vec" where
  "scalar_mult c v = map ((*) c) v"

definition vec_neg :: "int_vec => int_vec" where
  "vec_neg v = map uminus v"

lemma vec_add_length [dim_simp]:
  "length (vec_add v w) = min (length v) (length w)"
  unfolding vec_add_def by simp

lemma vec_sub_length [dim_simp]:
  "length (vec_sub v w) = min (length v) (length w)"
  unfolding vec_sub_def by simp

lemma scalar_mult_length [dim_simp]:
  "length (scalar_mult c v) = length v"
  unfolding scalar_mult_def by simp

lemma vec_neg_length [dim_simp]:
  "length (vec_neg v) = length v"
  unfolding vec_neg_def by simp
```

### Step 4: Inner Product Definition

**USE THIS EXACT CODE**:
```isabelle
definition inner_prod :: "int_vec => int_vec => int" where
  "inner_prod v w = sum_list (map2 (*) v w)"
```

### Step 5: Inner Product Index Form

This is a critical helper for later proofs.

**USE THIS EXACT CODE**:
```isabelle
lemma inner_prod_nth_min:
  "inner_prod u v = (\<Sum>i = 0 ..< min (length u) (length v). u ! i * v ! i)"
proof -
  have "inner_prod u v = sum_list (map2 (*) u v)"
    by (simp add: inner_prod_def)
  also have "... = (\<Sum>i = 0 ..< length (map2 (*) u v). (map2 (*) u v) ! i)"
    by (simp add: sum_list_sum_nth)
  also have "... = (\<Sum>i = 0 ..< min (length u) (length v). u ! i * v ! i)"
  proof (intro sum.cong refl)
    fix i assume "i < min (length u) (length v)"
    then have iu: "i < length u" and iv: "i < length v" by auto
    show "(map2 (*) u v) ! i = u ! i * v ! i"
      using iu iv by simp
  qed simp
  finally show ?thesis .
qed
```

### Step 6: Inner Product Basic Properties

**USE THIS EXACT CODE**:
```isabelle
lemma inner_prod_comm:
  assumes "length v = length w"
  shows "inner_prod v w = inner_prod w v"
  unfolding inner_prod_def
  by (simp add: map2_map_map mult.commute)

lemma inner_prod_Nil [simp]: "inner_prod [] v = 0"
  by (simp add: inner_prod_def)

lemma inner_prod_Nil2 [simp]: "inner_prod v [] = 0"
  by (simp add: inner_prod_def)
```

### Step 7: Matrix-Vector Multiplication

**USE THIS EXACT CODE**:
```isabelle
definition mat_vec_mult :: "int_matrix => int_vec => int_vec" where
  "mat_vec_mult A v = map (\<lambda>row. inner_prod row v) A"

lemma mat_vec_mult_length [dim_simp]:
  "length (mat_vec_mult A v) = length A"
  unfolding mat_vec_mult_def by simp

lemma mat_vec_mult_nth:
  assumes "i < length A"
  shows "(mat_vec_mult A v) ! i = inner_prod (A ! i) v"
  using assms unfolding mat_vec_mult_def by simp
```

### Step 8: Matrix Transpose

**USE THIS EXACT CODE**:
```isabelle
definition transpose :: "int_matrix => int_matrix" where
  "transpose A = (
    let m = length A;
        n = (if m = 0 then 0 else length (hd A))
    in map (\<lambda>j. map (\<lambda>i. (A ! i) ! j) [0..<m]) [0..<n])"

definition mat_transpose_vec_mult :: "int_matrix => int_vec => int_vec" where
  "mat_transpose_vec_mult A v = mat_vec_mult (transpose A) v"

lemma length_transpose:
  "length (transpose A) = (if A = [] then 0 else length (hd A))"
  unfolding transpose_def Let_def by simp

lemma length_transpose_valid_matrix:
  assumes "valid_matrix A m n" and "m > 0"
  shows "length (transpose A) = n"
proof -
  from assms have "A \<noteq> []" by (simp add: valid_matrix_def)
  then obtain a as where A_cons: "A = a # as" by (cases A) auto
  have "a \<in> set A" using A_cons by simp
  hence "length a = n" using assms(1) by (simp add: valid_matrix_def)
  thus ?thesis using A_cons by (simp add: length_transpose)
qed
```

### Step 9: LWE Dimensions Locale

**USE THIS EXACT CODE**:
```isabelle
locale lwe_dims =
  fixes A :: int_matrix and s :: int_vec and r :: int_vec and e :: int_vec
    and m n :: nat
  assumes A_ok: "valid_matrix A m n"
    and s_ok: "valid_vec s n"
    and r_ok: "valid_vec r m"
    and e_ok: "valid_vec e m"
    and m_pos: "m > 0"
    and n_pos: "n > 0"
begin

lemma len_A: "length A = m"
  using A_ok by (simp add: valid_matrix_def)

lemma len_s: "length s = n"
  using s_ok by (simp add: valid_vec_def)

lemma len_r: "length r = m"
  using r_ok by (simp add: valid_vec_def)

lemma len_e: "length e = m"
  using e_ok by (simp add: valid_vec_def)

lemma len_rows: "row \<in> set A \<Longrightarrow> length row = n"
  using A_ok by (simp add: valid_matrix_def)

lemma len_As: "length (mat_vec_mult A s) = m"
  using len_A by (simp add: mat_vec_mult_length)

lemma len_At: "length (mat_transpose_vec_mult A r) = n"
  using length_transpose_valid_matrix[OF A_ok m_pos]
  by (simp add: mat_transpose_vec_mult_def mat_vec_mult_length)
```

### Step 10: Helper Lemmas for Transpose Identity

These are essential for proving `iprod_transpose`.

**USE THIS EXACT CODE**:
```isabelle
lemma transpose_nth:
  assumes j_lt: "j < n"
  shows "transpose A ! j = map (\<lambda>row. row ! j) A"
proof -
  have len_T: "length (transpose A) = n"
    using length_transpose_valid_matrix[OF A_ok m_pos] .
  have j_T: "j < length (transpose A)" using j_lt len_T by simp
  have all_rows: "\<forall>row \<in> set A. j < length row"
    using len_rows j_lt by auto
  have filt: "filter (\<lambda>ys. j < length ys) A = A"
    using all_rows by (simp add: filter_True)
  show ?thesis using nth_transpose[OF j_T]
    by (simp add: filt)
qed

lemma inner_prod_col:
  assumes j_lt: "j < n"
  shows "inner_prod (map (\<lambda>row. row ! j) A) r =
         (\<Sum>i = 0 ..< m. (A ! i) ! j * r ! i)"
proof -
  have len_map: "length (map (\<lambda>row. row ! j) A) = m"
    using len_A by simp
  have "inner_prod (map (\<lambda>row. row ! j) A) r =
        (\<Sum>i = 0 ..< min (length (map (\<lambda>row. row ! j) A)) (length r).
           (map (\<lambda>row. row ! j) A) ! i * r ! i)"
    by (simp add: inner_prod_nth_min)
  also have "... = (\<Sum>i = 0 ..< m. (map (\<lambda>row. row ! j) A) ! i * r ! i)"
    using len_map len_r by (intro sum.cong refl) simp
  also have "... = (\<Sum>i = 0 ..< m. (A ! i) ! j * r ! i)"
    using len_A by (intro sum.cong refl) simp
  finally show ?thesis .
qed

lemma inner_prod_row:
  assumes i_lt: "i < m"
  shows "inner_prod (A ! i) s =
         (\<Sum>j = 0 ..< n. (A ! i) ! j * s ! j)"
proof -
  have i_ltA: "i < length A" using i_lt len_A by simp
  have row_mem: "A ! i \<in> set A" using i_ltA by (simp add: nth_mem)
  have row_len: "length (A ! i) = n"
    using len_rows row_mem by simp
  have "inner_prod (A ! i) s =
        (\<Sum>j = 0 ..< min (length (A ! i)) (length s). (A ! i) ! j * s ! j)"
    by (simp add: inner_prod_nth_min)
  also have "... = (\<Sum>j = 0 ..< n. (A ! i) ! j * s ! j)"
    using row_len len_s by (simp add: min_def)
  finally show ?thesis .
qed
```

### Step 11: The Transpose Identity (Critical for LWE)

This is the most important lemma: `<s, A^T r> = <As, r>`.

**USE THIS EXACT CODE**:
```isabelle
lemma iprod_transpose:
  "inner_prod s (mat_transpose_vec_mult A r) =
   inner_prod (mat_vec_mult A s) r"
proof -
  have lhs:
    "inner_prod s (mat_transpose_vec_mult A r) =
     (\<Sum>j = 0 ..< n. s ! j * (\<Sum>i = 0 ..< m. (A ! i) ! j * r ! i))"
  proof -
    have "inner_prod s (mat_transpose_vec_mult A r) =
          (\<Sum>j = 0 ..< min (length s) (length (mat_transpose_vec_mult A r)).
             s ! j * (mat_transpose_vec_mult A r) ! j)"
      by (simp add: inner_prod_nth_min)
    also have "... = (\<Sum>j = 0 ..< n. s ! j * (mat_transpose_vec_mult A r) ! j)"
      using len_s len_At by simp
    also have "... = (\<Sum>j = 0 ..< n. s ! j * inner_prod (transpose A ! j) r)"
      using len_At by (intro sum.cong refl) (simp add: mat_transpose_vec_mult_def mat_vec_mult_def)
    also have "... = (\<Sum>j = 0 ..< n. s ! j * inner_prod (map (\<lambda>row. row ! j) A) r)"
      using transpose_nth by (intro sum.cong refl) simp
    also have "... = (\<Sum>j = 0 ..< n. s ! j * (\<Sum>i = 0 ..< m. (A ! i) ! j * r ! i))"
      using inner_prod_col by (intro sum.cong refl) simp
    finally show ?thesis .
  qed
  have rhs:
    "inner_prod (mat_vec_mult A s) r =
     (\<Sum>i = 0 ..< m. r ! i * (\<Sum>j = 0 ..< n. (A ! i) ! j * s ! j))"
  proof -
    have "inner_prod (mat_vec_mult A s) r =
          (\<Sum>i = 0 ..< min (length (mat_vec_mult A s)) (length r).
             (mat_vec_mult A s) ! i * r ! i)"
      by (simp add: inner_prod_nth_min)
    also have "... = (\<Sum>i = 0 ..< m. (mat_vec_mult A s) ! i * r ! i)"
      using len_As len_r by simp
    also have "... = (\<Sum>i = 0 ..< m. inner_prod (A ! i) s * r ! i)"
      using len_As by (intro sum.cong refl) (simp add: mat_vec_mult_def)
    also have "... = (\<Sum>i = 0 ..< m. r ! i * inner_prod (A ! i) s)"
      by (intro sum.cong refl) (simp add: algebra_simps)
    also have "... = (\<Sum>i = 0 ..< m. r ! i * (\<Sum>j = 0 ..< n. (A ! i) ! j * s ! j))"
      using inner_prod_row by (intro sum.cong refl) simp
    finally show ?thesis .
  qed
  have swap:
    "(\<Sum>j = 0 ..< n. s ! j * (\<Sum>i = 0 ..< m. (A ! i) ! j * r ! i)) =
     (\<Sum>i = 0 ..< m. r ! i * (\<Sum>j = 0 ..< n. (A ! i) ! j * s ! j))"
  proof -
    have step1:
      "(\<Sum>j = 0 ..< n. s ! j * (\<Sum>i = 0 ..< m. (A ! i) ! j * r ! i)) =
       (\<Sum>j = 0 ..< n. \<Sum>i = 0 ..< m. s ! j * ((A ! i) ! j * r ! i))"
      by (simp add: sum_distrib_left[symmetric])
    have step2:
      "... = (\<Sum>i = 0 ..< m. \<Sum>j = 0 ..< n. s ! j * ((A ! i) ! j * r ! i))"
      by (simp add: sum.swap)
    have step3:
      "... = (\<Sum>i = 0 ..< m. \<Sum>j = 0 ..< n. r ! i * ((A ! i) ! j * s ! j))"
      by (simp add: algebra_simps)
    have step4:
      "... = (\<Sum>i = 0 ..< m. r ! i * (\<Sum>j = 0 ..< n. (A ! i) ! j * s ! j))"
      by (simp add: sum_distrib_left)
    show ?thesis using step1 step2 step3 step4 by simp
  qed
  show ?thesis using lhs rhs swap by simp
qed

end
```

### Step 12: Concatenation Helpers and Code Export

**USE THIS EXACT CODE**:
```isabelle
definition vec_concat :: "int_vec => int_vec => int_vec" where
  "vec_concat v w = v @ w"

definition split_vec :: "int_vec => nat => int_vec \<times> int_vec" where
  "split_vec v k = (take k v, drop k v)"

lemma vec_concat_length [dim_simp]:
  "length (vec_concat v w) = length v + length w"
  unfolding vec_concat_def by simp

lemma split_vec_concat:
  "k \<le> length v \<Longrightarrow> vec_concat (fst (split_vec v k)) (snd (split_vec v k)) = v"
  unfolding split_vec_def vec_concat_def by simp

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
- Imports: `Canon_Base.Prelude`
- No sorry/oops - all proofs must be complete
- All dimension lemmas declared [dim_simp]
- The `iprod_transpose` lemma is critical - use the exact proof provided

## Proof Strategy Reference

| Goal Type | Recommended Tactic |
|-----------|-------------------|
| Definition unfolding | `unfolding foo_def by simp` |
| Sum equalities | `by (intro sum.cong refl) simp` |
| Index rewriting | `using nth_map by simp` |
| Sum reordering | `by (simp add: sum.swap)` |
| Algebraic manipulation | `by (simp add: algebra_simps)` |

## Deliverable

A working ListVec.thy that:
1. Compiles as part of Canon_Base session
2. Provides all vector/matrix operations with dimension lemmas
3. Has the `lwe_dims` locale with `iprod_transpose`
4. Exports to Haskell
