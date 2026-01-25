theory LWE_Def
  imports Canon_Base.Prelude Canon_Base.ListVec Canon_Base.Zq Canon_Base.Norms
begin



(* === Step 1 === *)
text \<open>
  LWE Parameters:
  - n: dimension of secret vector s
  - m: number of LWE samples (rows of matrix A)
  - q: modulus (positive integer)
  - B_s: bound on secret coefficients (for short-secret variant)
  - B_e: bound on error coefficients
\<close>

record lwe_params =
  lwe_n :: nat
  lwe_m :: nat
  lwe_q :: int
  lwe_Bs :: int
  lwe_Be :: int

definition valid_lwe_params :: "lwe_params \<Rightarrow> bool" where
  "valid_lwe_params p = (
    lwe_n p > 0 \<and>
    lwe_m p > 0 \<and>
    lwe_q p > 1 \<and>
    lwe_Bs p >= 0 \<and>
    lwe_Be p >= 0)"

lemma valid_lwe_params_pos:
  assumes "valid_lwe_params p"
  shows "lwe_n p > 0" "lwe_m p > 0" "lwe_q p > 1"
  using assms unfolding valid_lwe_params_def by auto

(* === Step 2 === *)
text \<open>
  An LWE instance consists of:
  - A: public matrix (m x n) over Z_q
  - b: public vector (length m) where b = As + e mod q

  The secret s and error e are not part of the instance - they are witnesses.
\<close>

record lwe_instance =
  lwe_A :: int_matrix
  lwe_b :: int_vec

definition valid_lwe_instance :: "lwe_params \<Rightarrow> lwe_instance \<Rightarrow> bool" where
  "valid_lwe_instance p inst = (
    valid_matrix (lwe_A inst) (lwe_m p) (lwe_n p) \<and>
    valid_vec (lwe_b inst) (lwe_m p))"

(* === Step 3 === *)
text \<open>
  Generate an LWE sample: given matrix A, secret s, and error e,
  compute b = A * s + e mod q.
\<close>

definition lwe_sample :: "int_matrix \<Rightarrow> int_vec \<Rightarrow> int_vec \<Rightarrow> int \<Rightarrow> int_vec" where
  "lwe_sample A s e q = vec_mod (vec_add (mat_vec_mult A s) e) q"

lemma lwe_sample_length:
  "length (lwe_sample A s e q) = min (length A) (length e)"
  unfolding lwe_sample_def
  by (simp add: vec_mod_length vec_add_length mat_vec_mult_length)

lemma lwe_sample_nth:
  assumes "i < length A" "i < length e" "length A = length e"
  shows "(lwe_sample A s e q) ! i = (inner_prod (A ! i) s + e ! i) mod q"
proof -
  have "length (mat_vec_mult A s) = length A"
    by (simp add: mat_vec_mult_length)
  hence len_add: "length (vec_add (mat_vec_mult A s) e) = min (length A) (length e)"
    by (simp add: vec_add_length)
  have i_lt: "i < length (vec_add (mat_vec_mult A s) e)"
    using assms len_add by simp
  have "(lwe_sample A s e q) ! i = (vec_add (mat_vec_mult A s) e) ! i mod q"
    unfolding lwe_sample_def using i_lt by (simp add: vec_mod_nth)
  also have "(vec_add (mat_vec_mult A s) e) ! i = (mat_vec_mult A s) ! i + e ! i"
    using assms by (simp add: vec_add_def mat_vec_mult_length)
  also have "(mat_vec_mult A s) ! i = inner_prod (A ! i) s"
    using assms by (simp add: mat_vec_mult_nth)
  finally show ?thesis by simp
qed

(* === Step 4 === *)
text \<open>
  A valid secret vector has the right dimension and bounded coefficients.
  A valid error vector has the right dimension and bounded coefficients.
\<close>

definition valid_secret :: "lwe_params \<Rightarrow> int_vec \<Rightarrow> bool" where
  "valid_secret p s = (
    valid_vec s (lwe_n p) \<and>
    all_bounded s (lwe_Bs p))"

definition valid_error :: "lwe_params \<Rightarrow> int_vec \<Rightarrow> bool" where
  "valid_error p e = (
    valid_vec e (lwe_m p) \<and>
    all_bounded e (lwe_Be p))"

lemma valid_secret_length:
  "valid_secret p s \<Longrightarrow> length s = lwe_n p"
  unfolding valid_secret_def valid_vec_def by simp

lemma valid_secret_bounded:
  "valid_secret p s \<Longrightarrow> all_bounded s (lwe_Bs p)"
  unfolding valid_secret_def by simp

lemma valid_error_length:
  "valid_error p e \<Longrightarrow> length e = lwe_m p"
  unfolding valid_error_def valid_vec_def by simp

lemma valid_error_bounded:
  "valid_error p e \<Longrightarrow> all_bounded e (lwe_Be p)"
  unfolding valid_error_def by simp

(* === Step 5 === *)
definition make_lwe_instance :: "int_matrix \<Rightarrow> int_vec \<Rightarrow> int_vec \<Rightarrow> int \<Rightarrow> lwe_instance" where
  "make_lwe_instance A s e q = \<lparr> lwe_A = A, lwe_b = lwe_sample A s e q \<rparr>"

lemma make_lwe_instance_valid:
  assumes "valid_lwe_params p"
  assumes "valid_matrix A (lwe_m p) (lwe_n p)"
  assumes "valid_secret p s"
  assumes "valid_error p e"
  shows "valid_lwe_instance p (make_lwe_instance A s e (lwe_q p))"
proof -
  have A_len: "length A = lwe_m p"
    using assms(2) by (simp add: valid_matrix_def)
  have e_len: "length e = lwe_m p"
    using assms(4) by (simp add: valid_error_length)
  have "length (lwe_sample A s e (lwe_q p)) = min (length A) (length e)"
    by (simp add: lwe_sample_length)
  also have "min (length A) (length e) = lwe_m p"
    using A_len e_len by simp
  finally have b_len: "valid_vec (lwe_sample A s e (lwe_q p)) (lwe_m p)"
    by (simp add: valid_vec_def)
  show ?thesis
    unfolding valid_lwe_instance_def make_lwe_instance_def
    using assms(2) b_len by simp
qed

(* === Step 6 === *)
text \<open>
  Search-LWE: Given an LWE instance (A, b), find the secret s.

  A solution is correct if there exists a small error e such that
  b = As + e mod q.
\<close>

definition is_search_lwe_solution :: "lwe_params \<Rightarrow> lwe_instance \<Rightarrow> int_vec \<Rightarrow> bool" where
  "is_search_lwe_solution p inst s = (
    valid_vec s (lwe_n p) \<and>
    (\<exists>e. valid_error p e \<and>
         lwe_b inst = lwe_sample (lwe_A inst) s e (lwe_q p)))"

text \<open>
  Alternative formulation: the "residual" b - As mod q should be small.
\<close>

definition lwe_residual :: "lwe_instance \<Rightarrow> int_vec \<Rightarrow> int \<Rightarrow> int_vec" where
  "lwe_residual inst s q = vec_mod (vec_sub (lwe_b inst) (mat_vec_mult (lwe_A inst) s)) q"

definition is_search_lwe_solution_alt :: "lwe_params \<Rightarrow> lwe_instance \<Rightarrow> int_vec \<Rightarrow> bool" where
  "is_search_lwe_solution_alt p inst s = (
    valid_vec s (lwe_n p) \<and>
    all_bounded (vec_mod_centered (lwe_residual inst s (lwe_q p)) (lwe_q p)) (lwe_Be p))"

(* === Step 7 === *)
text \<open>
  Decision-LWE: Distinguish between:
  - Real: (A, b) where b = As + e for small s, e
  - Random: (A, b) where b is uniformly random

  We define predicates for "is a real LWE instance" and use these
  in security definitions.
\<close>

definition is_real_lwe_instance :: "lwe_params \<Rightarrow> lwe_instance \<Rightarrow> bool" where
  "is_real_lwe_instance p inst = (
    valid_lwe_instance p inst \<and>
    (\<exists>s e. valid_secret p s \<and> valid_error p e \<and>
           lwe_b inst = lwe_sample (lwe_A inst) s e (lwe_q p)))"

text \<open>
  A "witness" for a real LWE instance is the (s, e) pair.
\<close>

definition lwe_witness_valid :: "lwe_params \<Rightarrow> lwe_instance \<Rightarrow> int_vec \<Rightarrow> int_vec \<Rightarrow> bool" where
  "lwe_witness_valid p inst s e = (
    valid_secret p s \<and>
    valid_error p e \<and>
    lwe_b inst = lwe_sample (lwe_A inst) s e (lwe_q p))"

lemma real_lwe_has_witness:
  "is_real_lwe_instance p inst \<longleftrightarrow>
   valid_lwe_instance p inst \<and> (\<exists>s e. lwe_witness_valid p inst s e)"
  unfolding is_real_lwe_instance_def lwe_witness_valid_def by auto

(* === Step 8 === *)
locale lwe_context =
  fixes p :: lwe_params
    and A :: int_matrix
    and s :: int_vec
    and e :: int_vec
  assumes params_ok: "valid_lwe_params p"
    and A_ok: "valid_matrix A (lwe_m p) (lwe_n p)"
    and s_ok: "valid_secret p s"
    and e_ok: "valid_error p e"
begin

abbreviation "n \<equiv> lwe_n p"
abbreviation "m \<equiv> lwe_m p"
abbreviation "q \<equiv> lwe_q p"
abbreviation "B_s \<equiv> lwe_Bs p"
abbreviation "B_e \<equiv> lwe_Be p"

lemma n_pos: "n > 0"
  using params_ok unfolding valid_lwe_params_def by simp

lemma m_pos: "m > 0"
  using params_ok unfolding valid_lwe_params_def by simp

lemma q_pos: "q > 1"
  using params_ok unfolding valid_lwe_params_def by simp

lemma len_A: "length A = m"
  using A_ok unfolding valid_matrix_def by simp

lemma len_s: "length s = n"
  using s_ok valid_secret_length by simp

lemma len_e: "length e = m"
  using e_ok valid_error_length by simp

lemma s_bounded: "all_bounded s B_s"
  using s_ok valid_secret_bounded by simp

lemma e_bounded: "all_bounded e B_e"
  using e_ok valid_error_bounded by simp

definition "b \<equiv> lwe_sample A s e q"

definition "inst \<equiv> \<lparr> lwe_A = A, lwe_b = b \<rparr>"

lemma b_length: "length b = m"
proof -
  have "length b = length (lwe_sample A s e q)" unfolding b_def by simp
  also have "... = min (length A) (length e)" by (rule lwe_sample_length)
  also have "length A = m" by (rule len_A)
  also have "length e = m" by (rule len_e)
  finally show ?thesis by simp
qed

lemma inst_valid: "valid_lwe_instance p inst"
proof -
  have "valid_matrix A m n" using A_ok by simp
  moreover have "valid_vec b m" using b_length unfolding valid_vec_def by simp
  ultimately show ?thesis unfolding inst_def valid_lwe_instance_def by simp
qed

lemma inst_is_real: "is_real_lwe_instance p inst"
proof -
  have "lwe_witness_valid p inst s e"
  proof -
    have "valid_secret p s" by (rule s_ok)
    moreover have "valid_error p e" by (rule e_ok)
    moreover have "lwe_b inst = lwe_sample (lwe_A inst) s e q"
      unfolding inst_def b_def by simp
    ultimately show ?thesis unfolding lwe_witness_valid_def by simp
  qed
  from this inst_valid show ?thesis using real_lwe_has_witness by blast
qed

end

(* === Step 9 === *)
export_code
  lwe_params.make valid_lwe_params
  lwe_n lwe_m lwe_q lwe_Bs lwe_Be
  lwe_instance.make 
  lwe_A lwe_b
  lwe_sample make_lwe_instance
  valid_secret valid_error
  lwe_residual
  lwe_witness_valid
  in Haskell module_name "Canon.Hardness.LWE_Def"

end
