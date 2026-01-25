(*
  Theory: Lattice_Basics
  Author: Auto-generated

  Basic lattice definitions and operations for cryptographic applications.
  Provides vector operations, inner products, and fundamental lattice structures.
*)

theory Lattice_Basics
  imports
    Main
    "HOL-Library.Code_Target_Numeral"
    "HOL-Library.Code_Target_Int"
begin

section \<open>Vector Type and Basic Operations\<close>

text \<open>We represent vectors as lists of integers for simplicity and efficient code generation.\<close>

type_synonym vec = "int list"

text \<open>Vector dimension\<close>
definition vec_dim :: "vec \<Rightarrow> nat" where
  "vec_dim v = length v"

text \<open>Zero vector of given dimension\<close>
definition zero_vec :: "nat \<Rightarrow> vec" where
  "zero_vec n = replicate n 0"

text \<open>Vector addition\<close>
definition vec_add :: "vec \<Rightarrow> vec \<Rightarrow> vec" where
  "vec_add v1 v2 = map2 (+) v1 v2"

text \<open>Scalar multiplication\<close>
definition scalar_mult :: "int \<Rightarrow> vec \<Rightarrow> vec" where
  "scalar_mult s v = map (\<lambda>x. s * x) v"

text \<open>Vector subtraction\<close>
definition vec_sub :: "vec \<Rightarrow> vec \<Rightarrow> vec" where
  "vec_sub v1 v2 = map2 (-) v1 v2"

text \<open>Inner product of two vectors\<close>
definition inner_product :: "vec \<Rightarrow> vec \<Rightarrow> int" where
  "inner_product v1 v2 = sum_list (map2 (*) v1 v2)"

text \<open>Vector negation\<close>
definition vec_neg :: "vec \<Rightarrow> vec" where
  "vec_neg v = map uminus v"

section \<open>Modular Arithmetic for Vectors\<close>

text \<open>Reduce a single integer modulo q, centered around 0\<close>
definition mod_centered :: "int \<Rightarrow> int \<Rightarrow> int" where
  "mod_centered x q = (let r = x mod q in if r > q div 2 then r - q else r)"

text \<open>Reduce a single integer modulo q (standard)\<close>
definition mod_int :: "int \<Rightarrow> int \<Rightarrow> int" where
  "mod_int x q = x mod q"

text \<open>Component-wise modular reduction\<close>
definition vec_mod :: "vec \<Rightarrow> int \<Rightarrow> vec" where
  "vec_mod v q = map (\<lambda>x. mod_int x q) v"

text \<open>Centered modular reduction for vectors\<close>
definition vec_mod_centered :: "vec \<Rightarrow> int \<Rightarrow> vec" where
  "vec_mod_centered v q = map (\<lambda>x. mod_centered x q) v"

section \<open>Basic Lemmas\<close>

lemma vec_add_length:
  "length v1 = length v2 \<Longrightarrow> length (vec_add v1 v2) = length v1"
  unfolding vec_add_def by simp

lemma scalar_mult_length:
  "length (scalar_mult s v) = length v"
  unfolding scalar_mult_def by simp

lemma inner_product_comm:
  "length v1 = length v2 \<Longrightarrow> inner_product v1 v2 = inner_product v2 v1"
  unfolding inner_product_def
  by (simp add: map2_map_map mult.commute)

lemma vec_add_assoc:
  assumes "length v1 = length v2" "length v2 = length v3"
  shows "vec_add (vec_add v1 v2) v3 = vec_add v1 (vec_add v2 v3)"
  using assms unfolding vec_add_def
  by (induction v1 v2 v3 rule: list_induct3) auto

lemma vec_add_zero:
  "vec_add v (zero_vec (length v)) = v"
  unfolding vec_add_def zero_vec_def
  by (induction v) auto

section \<open>Matrix Operations\<close>

type_synonym matrix = "vec list"

text \<open>Matrix-vector multiplication\<close>
definition mat_vec_mult :: "matrix \<Rightarrow> vec \<Rightarrow> vec" where
  "mat_vec_mult A v = map (\<lambda>row. inner_product row v) A"

text \<open>Matrix-vector multiplication with modular reduction\<close>
definition mat_vec_mult_mod :: "matrix \<Rightarrow> vec \<Rightarrow> int \<Rightarrow> vec" where
  "mat_vec_mult_mod A v q = vec_mod (mat_vec_mult A v) q"

section \<open>Haskell Code Export\<close>

export_code
  vec_dim zero_vec vec_add scalar_mult vec_sub
  inner_product vec_neg mod_int mod_centered
  vec_mod vec_mod_centered mat_vec_mult mat_vec_mult_mod
  in Haskell
  module_name Lattice_Basics
  file_prefix Lattice_Basics

end
