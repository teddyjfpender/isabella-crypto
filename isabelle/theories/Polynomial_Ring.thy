(*
  Theory: Polynomial_Ring
  Author: Auto-generated

  Polynomial ring operations for Ring-LWE and related constructions.
  Implements polynomials over Z_q[X]/(X^n + 1).
*)

theory Polynomial_Ring
  imports
    Main
    "HOL-Library.Code_Target_Numeral"
    "HOL-Library.Code_Target_Int"
    Lattice_Basics
begin

section \<open>Polynomial Type\<close>

text \<open>Polynomials represented as coefficient lists, with index i being coefficient of X^i\<close>
type_synonym poly = "int list"

text \<open>Degree of polynomial (length - 1, or -1 for zero polynomial)\<close>
definition poly_degree :: "poly \<Rightarrow> int" where
  "poly_degree p = int (length p) - 1"

text \<open>Zero polynomial\<close>
definition zero_poly :: "nat \<Rightarrow> poly" where
  "zero_poly n = replicate n 0"

text \<open>Get coefficient at index i, defaulting to 0\<close>
definition coeff :: "poly \<Rightarrow> nat \<Rightarrow> int" where
  "coeff p i = (if i < length p then p ! i else 0)"

section \<open>Polynomial Arithmetic\<close>

text \<open>Polynomial addition\<close>
definition poly_add :: "poly \<Rightarrow> poly \<Rightarrow> poly" where
  "poly_add p1 p2 = (
    let len1 = length p1;
        len2 = length p2;
        maxlen = max len1 len2;
        pad1 = p1 @ replicate (maxlen - len1) 0;
        pad2 = p2 @ replicate (maxlen - len2) 0
    in map2 (+) pad1 pad2)"

text \<open>Polynomial subtraction\<close>
definition poly_sub :: "poly \<Rightarrow> poly \<Rightarrow> poly" where
  "poly_sub p1 p2 = poly_add p1 (map uminus p2)"

text \<open>Polynomial negation\<close>
definition poly_neg :: "poly \<Rightarrow> poly" where
  "poly_neg p = map uminus p"

text \<open>Scalar multiplication of polynomial\<close>
definition poly_scalar_mult :: "int \<Rightarrow> poly \<Rightarrow> poly" where
  "poly_scalar_mult s p = map (\<lambda>x. s * x) p"

text \<open>Single coefficient contribution to multiplication at index k\<close>
definition mult_coeff :: "poly \<Rightarrow> poly \<Rightarrow> nat \<Rightarrow> int" where
  "mult_coeff p1 p2 k = (\<Sum>i\<le>k. coeff p1 i * coeff p2 (k - i))"

text \<open>Naive polynomial multiplication (convolution)\<close>
definition poly_mult_naive :: "poly \<Rightarrow> poly \<Rightarrow> poly" where
  "poly_mult_naive p1 p2 = (
    let len1 = length p1;
        len2 = length p2;
        result_len = len1 + len2 - 1
    in if len1 = 0 \<or> len2 = 0 then []
       else map (\<lambda>k. mult_coeff p1 p2 k) [0..<result_len])"

section \<open>Ring Operations: Z_q[X]/(X^n + 1)\<close>

text \<open>Modular reduction of coefficients\<close>
definition poly_mod_coeffs :: "poly \<Rightarrow> int \<Rightarrow> poly" where
  "poly_mod_coeffs p q = map (\<lambda>x. x mod q) p"

text \<open>
  Reduce polynomial modulo (X^n + 1).
  For coefficient at position i >= n, it wraps around with negation.
  X^n = -1 in this ring, so X^(n+k) = -X^k
\<close>
definition poly_mod_cyclotomic :: "nat \<Rightarrow> poly \<Rightarrow> poly" where
  "poly_mod_cyclotomic n p = (
    let reduce_idx = (\<lambda>i.
      let base_coeff = coeff p i;
          wrap_coeff = coeff p (i + n)
      in base_coeff - wrap_coeff)
    in if n = 0 then [] else map reduce_idx [0..<n])"

text \<open>Full reduction: both cyclotomic and coefficient modular reduction\<close>
definition poly_reduce :: "nat \<Rightarrow> int \<Rightarrow> poly \<Rightarrow> poly" where
  "poly_reduce n q p = poly_mod_coeffs (poly_mod_cyclotomic n p) q"

text \<open>Ring multiplication: multiply and reduce\<close>
definition ring_mult :: "nat \<Rightarrow> int \<Rightarrow> poly \<Rightarrow> poly \<Rightarrow> poly" where
  "ring_mult n q p1 p2 = poly_reduce n q (poly_mult_naive p1 p2)"

text \<open>Ring addition: add and reduce coefficients\<close>
definition ring_add :: "int \<Rightarrow> poly \<Rightarrow> poly \<Rightarrow> poly" where
  "ring_add q p1 p2 = poly_mod_coeffs (poly_add p1 p2) q"

text \<open>Ring subtraction\<close>
definition ring_sub :: "int \<Rightarrow> poly \<Rightarrow> poly \<Rightarrow> poly" where
  "ring_sub q p1 p2 = poly_mod_coeffs (poly_sub p1 p2) q"

section \<open>Helper Functions\<close>

text \<open>Centered coefficient modular reduction\<close>
definition poly_mod_coeffs_centered :: "poly \<Rightarrow> int \<Rightarrow> poly" where
  "poly_mod_coeffs_centered p q = map (\<lambda>x. mod_centered x q) p"

text \<open>Check if polynomial has small coefficients (bounded by B)\<close>
definition is_small_poly :: "poly \<Rightarrow> int \<Rightarrow> bool" where
  "is_small_poly p B = list_all (\<lambda>x. \<bar>x\<bar> \<le> B) p"

text \<open>Compute infinity norm of polynomial\<close>
definition poly_inf_norm :: "poly \<Rightarrow> int" where
  "poly_inf_norm p = (if p = [] then 0 else Max (set (map abs p)))"

section \<open>Basic Lemmas\<close>

lemma poly_add_length:
  "length (poly_add p1 p2) = max (length p1) (length p2)"
  unfolding poly_add_def Let_def by simp

lemma poly_add_comm:
  "poly_add p1 p2 = poly_add p2 p1"
  unfolding poly_add_def Let_def
  by (simp add: max.commute add.commute map2_map_map)

lemma poly_mod_coeffs_length:
  "length (poly_mod_coeffs p q) = length p"
  unfolding poly_mod_coeffs_def by simp

section \<open>Haskell Code Export\<close>

export_code
  poly_degree zero_poly coeff
  poly_add poly_sub poly_neg poly_scalar_mult
  poly_mult_naive poly_mod_coeffs poly_mod_cyclotomic
  poly_reduce ring_mult ring_add ring_sub
  poly_mod_coeffs_centered is_small_poly poly_inf_norm
  in Haskell
  module_name Polynomial_Ring
  file_prefix Polynomial_Ring

end
