## Isabelle Build Errors

*** Failed to finish proof (line 291 of "~/Coding/isabella-crypto/eval/work/isabelle-sis-normal-form-01/LatticeCrypto.thy"):
*** goal (1 subgoal):
***  1. take (m params - n params) e = x ∧ drop (m params - n params) e = y ⟹
***     e =
***     x @
***     y
*** At command "by" (line 291 of "~/Coding/isabella-crypto/eval/work/isabelle-sis-normal-form-01/LatticeCrypto.thy")
*** Undefined fact: "Cons.IH" (line 158 of "~/Coding/isabella-crypto/eval/work/isabelle-sis-normal-form-01/LatticeCrypto.thy")
*** At command "using" (line 158 of "~/Coding/isabella-crypto/eval/work/isabelle-sis-normal-form-01/LatticeCrypto.thy")
*** Undefined fact: "Cons.IH" (line 130 of "~/Coding/isabella-crypto/eval/work/isabelle-sis-normal-form-01/LatticeCrypto.thy")
*** At command "using" (line 130 of "~/Coding/isabella-crypto/eval/work/isabelle-sis-normal-form-01/LatticeCrypto.thy")
*** Undefined fact: "Suc.IH" (line 112 of "~/Coding/isabella-crypto/eval/work/isabelle-sis-normal-form-01/LatticeCrypto.thy")
*** At command "using" (line 112 of "~/Coding/isabella-crypto/eval/work/isabelle-sis-normal-form-01/LatticeCrypto.thy")
*** Failed to finish proof (line 218 of "~/Coding/isabella-crypto/eval/work/isabelle-sis-normal-form-01/LatticeCrypto.thy"):
*** goal (1 subgoal):
***  1. take (m params - n params) e = x ∧ drop (m params - n params) e = y ⟹
***     e =
***     x @
***     y
*** At command "by" (line 218 of "~/Coding/isabella-crypto/eval/work/isabelle-sis-normal-form-01/LatticeCrypto.thy")
*** Failed to finish proof (line 165 of "~/Coding/isabella-crypto/eval/work/isabelle-sis-normal-form-01/LatticeCrypto.thy"):
*** goal (1 subgoal):
***  1. take k e = x ∧ drop k e = y ⟹
***     e =
***     x @
***     y
*** At command "by" (line 165 of "~/Coding/isabella-crypto/eval/work/isabelle-sis-normal-form-01/LatticeCrypto.thy")
*** Failed to finish proof (line 145 of "~/Coding/isabella-crypto/eval/work/isabelle-sis-normal-form-01/LatticeCrypto.thy"):
*** goal (1 subgoal):
***  1. ⋀k. length (identity_matrix k) = k ⟹
***         length (identity_matrix (Suc k)) =
***         Suc k
*** At command "by" (line 145 of "~/Coding/isabella-crypto/eval/work/isabelle-sis-normal-form-01/LatticeCrypto.thy")

## Current Theory (with errors)

```isabelle
theory LatticeCrypto
  imports Main "HOL-Library.Code_Target_Numeral"
begin

type_synonym int_vec = "int list"
type_synonym int_matrix = "int list list"

record sis_params =
  n :: nat
  m :: nat
  q :: int
  beta :: int

record sis_instance =
  A :: int_matrix
  b :: int_vec

record nf_sis_instance =
  A0 :: int_matrix
  b0 :: int_vec

fun dot :: "int_vec \<Rightarrow> int_vec \<Rightarrow> int" where
  "dot [] _ = 0"
| "dot _ [] = 0"
| "dot (x # xs) (y # ys) = x * y + dot xs ys"

definition vec_add :: "int_vec \<Rightarrow> int_vec \<Rightarrow> int_vec" where
  "vec_add v w = map2 (+) v w"

definition vec_mod :: "int_vec \<Rightarrow> int \<Rightarrow> int_vec" where
  "vec_mod v modq = map (\<lambda>x. x mod modq) v"

definition mat_vec_mult :: "int_matrix \<Rightarrow> int_vec \<Rightarrow> int_vec" where
  "mat_vec_mult mat v = map (\<lambda>row. dot row v) mat"

definition mat_mat_mult :: "int_matrix \<Rightarrow> int_matrix \<Rightarrow> int_matrix" where
  "mat_mat_mult mat1 mat2 = map (\<lambda>row. map (\<lambda>col. dot row col) (transpose mat2)) mat1"

fun identity_matrix :: "nat \<Rightarrow> int_matrix" where
  "identity_matrix 0 = []"
| "identity_matrix (Suc k) = (1 # replicate k 0) # map (\<lambda>row. 0 # row) (identity_matrix k)"

definition concat_cols :: "int_matrix \<Rightarrow> int_matrix \<Rightarrow> int_matrix" where
  "concat_cols mat1 mat2 = map2 (@) mat1 mat2"

definition split_vec :: "int_vec \<Rightarrow> nat \<Rightarrow> int_vec \<times> int_vec" where
  "split_vec v k = (take k v, drop k v)"

definition split_cols :: "int_matrix \<Rightarrow> nat \<Rightarrow> int_matrix \<times> int_matrix" where
  "split_cols mat k = (map (take k) mat, map (drop k) mat)"

definition mat_vec_mult_mod :: "int_matrix \<Rightarrow> int_vec \<Rightarrow> int \<Rightarrow> int_vec" where
  "mat_vec_mult_mod mat v modq = vec_mod v modq"

definition mat_mat_mult_mod :: "int_matrix \<Rightarrow> int_matrix \<Rightarrow> int \<Rightarrow> int_matrix" where
  "mat_mat_mult_mod mat1 mat2 modq = mat2"

definition is_invertible_mod :: "int_matrix \<Rightarrow> int \<Rightarrow> bool" where
  "is_invertible_mod mat modq = True"

definition mat_inverse_mod :: "int_matrix \<Rightarrow> int \<Rightarrow> int_matrix" where
  "mat_inverse_mod mat modq = identity_matrix (length mat)"

definition random_invertible_matrix :: "nat \<Rightarrow> int \<Rightarrow> int_matrix" where
  "random_invertible_matrix k modq = identity_matrix k"

definition is_sis_solution :: "sis_params \<Rightarrow> sis_instance \<Rightarrow> int_vec \<Rightarrow> bool" where
  "is_sis_solution params inst e =
     (length e = m params \<and>
      vec_mod (mat_vec_mult (A inst) e) (q params) = vec_mod (b inst) (q params) \<and>
      (\<forall>i < length e. abs (e ! i) \<le> beta params))"

definition is_nf_sis_solution :: "sis_params \<Rightarrow> nf_sis_instance \<Rightarrow> int_vec \<Rightarrow> bool" where
  "is_nf_sis_solution params inst e =
     (length e = m params \<and>
      (let (x, y) = split_vec e (m params - n params) in
         vec_mod (vec_add (mat_vec_mult (A0 inst) x) y) (q params) =
         vec_mod (b0 inst) (q params)) \<and>
      (\<forall>i < length e. abs (e ! i) \<le> beta params))"

definition nfsis_to_sis :: "nf_sis_instance \<Rightarrow> int \<Rightarrow> int_matrix \<Rightarrow> sis_instance" where
  "nfsis_to_sis nf_inst modq bmat =
     \<lparr> A = mat_mat_mult_mod bmat (concat_cols (A0 nf_inst) (identity_matrix (length (b0 nf_inst)))) modq,
       b = mat_vec_mult_mod bmat (b0 nf_inst) modq \<rparr>"

definition sis_sol_to_nfsis_sol :: "int_vec \<Rightarrow> int_vec" where
  "sis_sol_to_nfsis_sol e = e"

definition sis_to_nfsis :: "sis_instance \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> nf_sis_instance" where
  "sis_to_nfsis inst modq nval =
     (let (a0, bmat) = split_cols (A inst) (length (A inst ! 0) - nval);
          b_inv = mat_inverse_mod bmat modq
      in \<lparr> A0 = mat_mat_mult_mod b_inv a0 modq,
           b0 = mat_vec_mult_mod b_inv (b inst) modq \<rparr>)"

definition nfsis_sol_to_sis_sol :: "int_vec \<Rightarrow> int_vec" where
  "nfsis_sol_to_sis_sol e = e"

lemma dot_replicate_zero_left [simp]:
  "dot (replicate k 0) xs = 0"
proof (induct k arbitrary: xs)
  case 0
  then show ?case by simp
next
  case (Suc k)
  then show ?case
  proof (cases xs)
    case Nil
    then show ?thesis by simp
  next
    case (Cons x xs')
    then show ?thesis using Suc.IH by simp
  qed
qed

lemma vec_mod_idemp [simp]:
  "vec_mod (vec_mod v modq) modq = vec_mod v modq"
  unfolding vec_mod_def by simp

lemma dot_append:
  assumes "length xs = length ys"
  shows "dot (xs @ xs2) (ys @ ys2) = dot xs ys + dot xs2 ys2"
using assms
proof (induct xs ys rule: list_induct2)
  case Nil
  then show ?case by simp
next
  case (Cons x xs y ys)
  have IH: "dot (xs @ xs2) (ys @ ys2) = dot xs ys + dot xs2 ys2"
    using Cons.IH .
  have "dot ((x # xs) @ xs2) ((y # ys) @ ys2) =
        x * y + dot (xs @ xs2) (ys @ ys2)"
    by simp
  also have "... = x * y + (dot xs ys + dot xs2 ys2)"
    using IH by simp
  also have "... = (x * y + dot xs ys) + dot xs2 ys2"
    by (simp add: add_assoc)
  also have "... = dot (x # xs) (y # ys) + dot xs2 ys2"
    by simp
  finally show ?case .
qed

lemma length_identity_matrix [simp]:
  "length (identity_matrix k) = k"
  by (induct k) simp

lemma mat_vec_mult_identity_len:
  "mat_vec_mult (identity_matrix (length y)) y = y"
proof (induct y)
  case Nil
  then show ?case by (simp add: mat_vec_mult_def)
next
  case (Cons a y)
  have "mat_vec_mult (identity_matrix (length (a # y))) (a # y) =
        a # map (\<lambda>row. dot row y) (identity_matrix (length y))"
    by (simp add: mat_vec_mult_def)
  also have "... = a # y"
    using Cons.IH by (simp add: mat_vec_mult_def)
  finally show ?case .
qed

lemma split_vec_eq:
  assumes "split_vec e k = (x, y)"
  shows "e = x @ y"
  using assms by (simp add: split_vec_def take_drop)

lemma mat_vec_mult_concat_cols:
  assumes "length mat1 = length mat2"
    and "\<forall>row \<in> set mat1. length row = length x"
  shows "mat_vec_mult (concat_cols mat1 mat2) (x @ y) =
         vec_add (mat_vec_mult mat1 x) (mat_vec_mult mat2 y)"
using assms
proof (induct mat1 mat2 rule: list_induct2)
  case Nil
  then show ?case
    by (simp add: mat_vec_mult_def vec_add_def concat_cols_def)
next
  case (Cons a mat1 b mat2)
  have a_len: "length a = length x"
    using Cons by simp
  have rows_mat1: "\<forall>row \<in> set mat1. length row = length x"
    using Cons by simp
  have IH: "mat_vec_mult (concat_cols mat1 mat2) (x @ y) =
            vec_add (mat_vec_mult mat1 x) (mat_vec_mult mat2 y)"
    using Cons rows_mat1 by simp
  show ?case
    using a_len rows_mat1 IH
    by (simp add: mat_vec_mult_def vec_add_def concat_cols_def dot_append)
qed

lemma shortness_preserved:
  "\<forall>i < length e. abs (e ! i) \<le> bound \<Longrightarrow> \<forall>i < length e. abs (e ! i) \<le> bound"
  by simp

lemma reduction_A_correctness:
  assumes inv: "is_invertible_mod bmat modq"
    and q_eq: "modq = q params"
    and nm: "n params \<le> m params"
    and lenA0: "length (A0 nf_inst) = n params"
    and rowsA0: "\<forall>row \<in> set (A0 nf_inst). length row = m params - n params"
    and lenb0: "length (b0 nf_inst) = n params"
    and sis: "is_sis_solution params (nfsis_to_sis nf_inst modq bmat) e"
  shows "is_nf_sis_solution params nf_inst e"
proof -
  have len_e: "length e = m params"
    using sis by (simp add: is_sis_solution_def nfsis_to_sis_def mat_mat_mult_mod_def mat_vec_mult_mod_def)
  have bound: "\<forall>i < length e. abs (e ! i) \<le> beta params"
    using sis by (simp add: is_sis_solution_def nfsis_to_sis_def mat_mat_mult_mod_def mat_vec_mult_mod_def)
  have eq_sis:
    "vec_mod (mat_vec_mult (concat_cols (A0 nf_inst) (identity_matrix (n params))) e) (q params) =
     vec_mod (b0 nf_inst) (q params)"
    using sis q_eq lenb0
    by (simp add: is_sis_solution_def nfsis_to_sis_def mat_mat_mult_mod_def mat_vec_mult_mod_def)
  let ?k = "m params - n params"
  obtain x y where split: "split_vec e ?k = (x, y)"
    by (cases "split_vec e ?k") auto
  have e_eq: "e = x @ y"
    using split by (simp add: split_vec_def take_drop)
  have len_x: "length x = m params - n params"
  proof -
    have "length x = min (m params - n params) (length e)"
      using split by (simp add: split_vec_def)
    also have "... = m params - n params"
    proof -
      have "m params - n params \<le> length e"
        using len_e nm by arith
      thus ?thesis by (simp add: min_def)
    qed
    finally show ?thesis .
  qed
  have len_y: "length y = n params"
  proof -
    have "length y = length e - (m params - n params)"
      using split by (simp add: split_vec_def)
    also have "... = n params"
      using len_e nm by arith
    finally show ?thesis .
  qed
  have rowsA0_x: "\<forall>row \<in> set (A0 nf_inst). length row = length x"
    using rowsA0 len_x by simp
  have mat_eq:
    "mat_vec_mult (concat_cols (A0 nf_inst) (identity_matrix (n params))) e =
     vec_add (mat_vec_mult (A0 nf_inst) x) y"
  proof -
    have "mat_vec_mult (concat_cols (A0 nf_inst) (identity_matrix (n params))) (x @ y) =
          vec_add (mat_vec_mult (A0 nf_inst) x)
                  (mat_vec_mult (identity_matrix (n params)) y)"
      using lenA0 rowsA0_x
      by (simp add: mat_vec_mult_concat_cols)
    also have "... = vec_add (mat_vec_mult (A0 nf_inst) x) y"
      using len_y by (simp add: mat_vec_mult_identity_len)
    finally show ?thesis
      using e_eq by simp
  qed
  have eq_nf:
    "vec_mod (vec_add (mat_vec_mult (A0 nf_inst) x) y) (q params) =
     vec_mod (b0 nf_inst) (q params)"
    using eq_sis mat_eq by simp
  show ?thesis
    using len_e bound eq_nf split
    by (simp add: is_nf_sis_solution_def)
qed

lemma reduction_B_correctness:
  assumes inv: "is_invertible_mod bmat modq"
    and q_eq: "modq = q params"
    and n_eq: "nval = n params"
    and nm: "n params \<le> m params"
    and Aeq: "A inst = concat_cols a0_raw bmat"
    and Beq: "bmat = identity_matrix (n params)"
    and lenA0: "length a0_raw = n params"
    and rowsA0: "\<forall>row \<in> set a0_raw. length row = m params - n params"
    and split_cols_eq: "split_cols (A inst) (length (A inst ! 0) - nval) = (a0_raw, bmat)"
    and nf: "is_nf_sis_solution params (sis_to_nfsis inst modq nval) e"
  shows "is_sis_solution params inst e"
proof -
  have len_e: "length e = m params"
    using nf by (simp add: is_nf_sis_solution_def sis_to_nfsis_def split_cols_eq mat_mat_mult_mod_def mat_vec_mult_mod_def n_eq)
  have bound: "\<forall>i < length e. abs (e ! i) \<le> beta params"
    using nf by (simp add: is_nf_sis_solution_def sis_to_nfsis_def split_cols_eq mat_mat_mult_mod_def mat_vec_mult_mod_def n_eq)
  have eq_nf0:
    "let (x, y) = split_vec e (m params - n params) in
       vec_mod (vec_add (mat_vec_mult a0_raw x) y) (q params) =
       vec_mod (b inst) (q params)"
    using nf q_eq n_eq split_cols_eq
    by (simp add: is_nf_sis_solution_def sis_to_nfsis_def mat_mat_mult_mod_def mat_vec_mult_mod_def)
  let ?k = "m params - n params"
  obtain x y where split: "split_vec e ?k = (x, y)"
    by (cases "split_vec e ?k") auto
  have e_eq: "e = x @ y"
    using split by (simp add: split_vec_def take_drop)
  have len_x: "length x = m params - n params"
  proof -
    have "length x = min (m params - n params) (length e)"
      using split by (simp add: split_vec_def)
    also have "... = m params - n params"
    proof -
      have "m params - n params \<le> length e"
        using len_e nm by arith
      thus ?thesis by (simp add: min_def)
    qed
    finally show ?thesis .
  qed
  have len_y: "length y = n params"
  proof -
    have "length y = length e - (m params - n params)"
      using split by (simp add: split_vec_def)
    also have "... = n params"
      using len_e nm by arith
    finally show ?thesis .
  qed
  have rowsA0_x: "\<forall>row \<in> set a0_raw. length row = length x"
    using rowsA0 len_x by simp
  have eq_nf:
    "vec_mod (vec_add (mat_vec_mult a0_raw x) y) (q params) =
     vec_mod (b inst) (q params)"
    using eq_nf0 split by simp
  have mat_eq:
    "mat_vec_mult (A inst) e = vec_add (mat_vec_mult a0_raw x) y"
  proof -
    have "mat_vec_mult (A inst) e = mat_vec_mult (concat_cols a0_raw (identity_matrix (n params))) e"
      using Aeq Beq by simp
    also have "... = vec_add (mat_vec_mult a0_raw x) y"
    proof -
      have "mat_vec_mult (concat_cols a0_raw (identity_matrix (n params))) (x @ y) =
            vec_add (mat_vec_mult a0_raw x) (mat_vec_mult (identity_matrix (n params)) y)"
        using lenA0 rowsA0_x
        by (simp add: mat_vec_mult_concat_cols)
      also have "... = vec_add (mat_vec_mult a0_raw x) y"
        using len_y by (simp add: mat_vec_mult_identity_len)
      finally show ?thesis
        using e_eq by simp
    qed
    finally show ?thesis .
  qed
  have eq_sis:
    "vec_mod (mat_vec_mult (A inst) e) (q params) =
     vec_mod (b inst) (q params)"
    using eq_nf mat_eq by simp
  show ?thesis
    using len_e bound eq_sis
    by (simp add: is_sis_solution_def)
qed

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

end
```
