theory Prelude
  imports Main "HOL-Library.Code_Target_Numeral" "HOL-Number_Theory.Number_Theory"
begin

(* === Named Theorem Collections === *)
named_theorems mod_simp "modular arithmetic simplification rules"
named_theorems vec_simp "vector operation simplification rules"
named_theorems mat_simp "matrix operation simplification rules"
named_theorems dim_simp "dimension preservation rules"
named_theorems dist_simp "distance and decoding rules"

(* === Declare Existing Mod Lemmas === *)
declare mod_add_eq [mod_simp]
declare mod_diff_eq [mod_simp]
declare mod_mult_eq [mod_simp]
declare mod_mod_trivial [mod_simp]

(* === Centered Mod Definition === *)
definition mod_centered :: "int => int => int" where
  "mod_centered x q = (let r = x mod q in if r > q div 2 then r - q else r)"

lemma mod_centered_range:
  assumes "q > 0"
  shows "mod_centered x q > -(q div 2 + 1)" and "mod_centered x q <= q div 2"
proof -
  let ?r = "x mod q"
  have r0: "0 <= ?r" and rq: "?r < q" using assms by simp_all
  have q2_nonneg: "0 <= q div 2" using assms by simp

  show "mod_centered x q > -(q div 2 + 1)"
  proof (cases "?r > q div 2")
    case False
    have "-(q div 2 + 1) < 0" using q2_nonneg by arith
    also have "0 <= ?r" using r0 by simp
    finally have "-(q div 2 + 1) < ?r" by simp
    then show ?thesis
      unfolding mod_centered_def Let_def
      using False by simp
  next
    case True
    have "q div 2 < ?r" using True by simp
    hence "?r - q > q div 2 - q" by arith
    have "q div 2 - q >= -(q div 2 + 1)"
    proof -
      have "q div 2 + (q div 2 + 1) >= q" by (simp add: div_plus_div_distrib_dvd_left)
      thus ?thesis by arith
    qed
    hence "?r - q > -(q div 2 + 1)" using True rq by arith
    then show ?thesis
      unfolding mod_centered_def Let_def
      using True by simp
  qed

  show "mod_centered x q <= q div 2"
  proof (cases "?r > q div 2")
    case False
    then show ?thesis
      unfolding mod_centered_def Let_def
      by simp
  next
    case True
    have "?r - q < 0" using rq by arith
    hence "?r - q <= q div 2" using q2_nonneg by arith
    then show ?thesis
      unfolding mod_centered_def Let_def
      using True by simp
  qed
qed

(* === Absolute Value Bounds === *)
lemma abs_mod_less:
  assumes "(n::int) > 0"
  shows "abs (a mod n) < n"
proof -
  from assms have nonneg: "0 <= a mod n" by simp
  from assms have bound: "a mod n < n" by simp
  from nonneg have "abs (a mod n) = a mod n" by simp
  with bound show ?thesis by simp
qed

end
