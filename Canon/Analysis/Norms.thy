theory Norms
  imports Canon_Base.Prelude Canon_Base.ListVec
begin

(* === Step 1: L-infinity Norm Definition === *)
named_theorems norm_simp "norm simplification rules"

definition linf_norm :: "int list => int" where
  "linf_norm v = (if v = [] then 0 else Max (abs ` set v))"

lemma linf_norm_nonneg [norm_simp]:
  "linf_norm v >= 0"
proof (cases "v = []")
  case True
  then show ?thesis unfolding linf_norm_def by simp
next
  case False
  then have ne: "abs ` set v \<noteq> {}" by simp
  have fin: "finite (abs ` set v)" by simp
  from ne fin have "Max (abs ` set v) \<in> abs ` set v"
    by (intro Max_in)
  then obtain x where "x \<in> set v" and "Max (abs ` set v) = abs x" by auto
  hence "Max (abs ` set v) >= 0" by simp
  thus ?thesis using False unfolding linf_norm_def by simp
qed

lemma linf_norm_bound:
  assumes "x \<in> set v"
  shows "abs x <= linf_norm v"
proof -
  have vne: "v \<noteq> []" using assms by auto
  have fin: "finite (abs ` set v)" by simp
  have mem: "abs x \<in> abs ` set v" using assms by simp
  hence "abs x <= Max (abs ` set v)"
    using fin by simp
  thus ?thesis unfolding linf_norm_def using vne by simp
qed

lemma linf_norm_nth:
  assumes "i < length v"
  shows "abs (v ! i) <= linf_norm v"
proof -
  have "v ! i \<in> set v" using assms by simp
  thus ?thesis by (rule linf_norm_bound)
qed

(* === Step 2: All-Bounded Predicate === *)
definition all_bounded :: "int list => int => bool" where
  "all_bounded v B = (\<forall>x \<in> set v. abs x <= B)"

lemma all_bounded_alt:
  "all_bounded v B = (\<forall>i < length v. abs (v ! i) <= B)"
  unfolding all_bounded_def
  by (metis in_set_conv_nth)

lemma all_bounded_nth:
  assumes "all_bounded v B" and "i < length v"
  shows "abs (v ! i) <= B"
  using assms unfolding all_bounded_alt by simp

lemma all_bounded_linf:
  assumes "v \<noteq> []"
  shows "all_bounded v B \<longleftrightarrow> linf_norm v <= B"
proof
  assume ab: "all_bounded v B"
  have fin: "finite (abs ` set v)" by simp
  have ne: "abs ` set v \<noteq> {}" using assms by simp
  have "\<forall>x \<in> abs ` set v. x <= B"
  proof
    fix y assume "y \<in> abs ` set v"
    then obtain x where "x \<in> set v" and "y = abs x" by auto
    thus "y <= B" using ab unfolding all_bounded_def by simp
  qed
  hence "Max (abs ` set v) <= B"
    using fin ne by simp
  thus "linf_norm v <= B"
    unfolding linf_norm_def using assms by simp
next
  assume linf: "linf_norm v <= B"
  show "all_bounded v B"
    unfolding all_bounded_def
  proof
    fix x assume "x \<in> set v"
    hence "abs x <= linf_norm v" by (rule linf_norm_bound)
    thus "abs x <= B" using linf by simp
  qed
qed

lemma all_bounded_Nil [simp]:
  "all_bounded [] B"
  unfolding all_bounded_def by simp

(* === Step 3: Triangle Inequality for Inner Product === *)
lemma inner_prod_abs_bound:
  "abs (inner_prod u v) <= (\<Sum>i = 0 ..< min (length u) (length v). abs (u ! i) * abs (v ! i))"
proof -
  let ?n = "min (length u) (length v)"
  have "inner_prod u v = (\<Sum>i = 0 ..< ?n. u ! i * v ! i)"
    by (simp add: inner_prod_nth_min)
  hence "abs (inner_prod u v) = abs (\<Sum>i = 0 ..< ?n. u ! i * v ! i)"
    by simp
  also have "... <= (\<Sum>i = 0 ..< ?n. abs (u ! i * v ! i))"
    by (rule sum_abs)
  also have "... = (\<Sum>i = 0 ..< ?n. abs (u ! i) * abs (v ! i))"
    by (simp add: abs_mult)
  finally show ?thesis .
qed

(* === Step 4: Coefficient-wise Bound (Main Lemma) === *)
lemma inner_prod_bound:
  assumes len_eq: "length u = length v"
  assumes u_bound: "all_bounded u B1"
  assumes v_bound: "all_bounded v B2"
  assumes B1_pos: "(B1::int) >= 0"
  assumes B2_pos: "(B2::int) >= 0"
  shows "abs (inner_prod u v) <= int (length u) * B1 * B2"
proof -
  let ?n = "length u"
  have min_eq: "min (length u) (length v) = ?n"
    using len_eq by simp
  have step1: "abs (inner_prod u v) <= (\<Sum>i = 0 ..< min (length u) (length v). abs (u ! i) * abs (v ! i))"
    by (rule inner_prod_abs_bound)
  have step2: "(\<Sum>i = 0 ..< min (length u) (length v). abs (u ! i) * abs (v ! i)) =
               (\<Sum>i = 0 ..< ?n. abs (u ! i) * abs (v ! i))"
    using min_eq by simp
  have "abs (inner_prod u v) <= (\<Sum>i = 0 ..< ?n. abs (u ! i) * abs (v ! i))"
    using step1 step2 by simp
  also have "... <= (\<Sum>i = 0 ..< ?n. B1 * B2)"
  proof (rule sum_mono)
    fix i assume "i \<in> {0 ..< ?n}"
    hence i_lt: "i < ?n" by simp
    have "abs (u ! i) <= B1"
      using all_bounded_nth[OF u_bound i_lt] .
    moreover have "abs (v ! i) <= B2"
      using all_bounded_nth[OF v_bound] i_lt len_eq by simp
    moreover have "abs (u ! i) >= 0" and "abs (v ! i) >= 0" by simp_all
    ultimately show "abs (u ! i) * abs (v ! i) <= B1 * B2"
      using B1_pos B2_pos by (simp add: mult_mono)
  qed
  also have "... = int ?n * B1 * B2"
    by simp
  finally show ?thesis .
qed

(* === Step 5: Simplified Bound for Equal Bounds === *)
lemma inner_prod_bound_same:
  assumes "length u = length v"
  assumes "all_bounded u B"
  assumes "all_bounded v B"
  assumes "(B::int) >= 0"
  shows "abs (inner_prod u v) <= int (length u) * B * B"
  using inner_prod_bound[OF assms(1) assms(2) assms(3) assms(4) assms(4)]
  by simp

lemma inner_prod_bound_simpler:
  assumes "length u = length v"
  assumes "all_bounded u B"
  assumes "all_bounded v B"
  assumes "(B::int) >= 0"
  shows "abs (inner_prod u v) <= int (length u) * B^2"
  using inner_prod_bound_same[OF assms]
  by (simp add: power2_eq_square)

(* === Step 6: Bound with Explicit n Parameter === *)
lemma inner_prod_bound_n:
  assumes "length u = n" and "length v = n"
  assumes "all_bounded u B1" and "all_bounded v B2"
  assumes "(B1::int) >= 0" and "(B2::int) >= 0"
  shows "abs (inner_prod u v) <= int n * B1 * B2"
proof -
  have "length u = length v" using assms(1,2) by simp
  hence "abs (inner_prod u v) <= int (length u) * B1 * B2"
    using inner_prod_bound[OF _ assms(3,4,5,6)] by simp
  thus ?thesis using assms(1) by simp
qed

(* === Step 7: LWE Error Term Bound === *)
lemma lwe_error_bound:
  assumes len_e: "length e = (m::nat)"
  assumes len_r: "length r = m"
  assumes e_small: "all_bounded e B_e"
  assumes r_small: "all_bounded r B_r"
  assumes Be_pos: "(B_e::int) >= 0"
  assumes Br_pos: "(B_r::int) >= 0"
  shows "abs (inner_prod e r) <= int m * B_e * B_r"
proof -
  have "length e = length r" using len_e len_r by simp
  thus ?thesis
    using inner_prod_bound[OF _ e_small r_small Be_pos Br_pos] len_e
    by simp
qed

lemma lwe_noise_small:
  assumes "length e = (m::nat)" and "length r = m"
  assumes "all_bounded e B_e" and "all_bounded r B_r"
  assumes "(B_e::int) >= 0" and "(B_r::int) >= 0"
  assumes noise_cond: "int m * B_e * B_r < q div 4"
  shows "abs (inner_prod e r) < (q::int) div 4"
proof -
  have "abs (inner_prod e r) <= int m * B_e * B_r"
    using lwe_error_bound[OF assms(1-6)] .
  also have "... < q div 4" using noise_cond .
  finally show ?thesis .
qed

(* === Step 8: Code Export === *)
export_code
  linf_norm all_bounded
  in Haskell module_name "Canon.Analysis.Norms"

end
