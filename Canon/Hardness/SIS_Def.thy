theory SIS_Def
  imports Canon_Base.Prelude Canon_Base.ListVec Canon_Base.Zq Canon_Base.Norms
begin

(* === Step 1: SIS Parameters Record === *)
text \<open>
  SIS Parameters:
  - n: number of columns in matrix A (dimension of solution vector)
  - m: number of rows in matrix A (number of equations)
  - q: modulus (positive integer)
  - beta: bound on solution coefficients (L-infinity norm bound)

  The SIS problem: given A, find short z such that Az = 0 mod q.
\<close>

record sis_params =
  sis_n :: nat
  sis_m :: nat
  sis_q :: int
  sis_beta :: int

definition valid_sis_params :: "sis_params \<Rightarrow> bool" where
  "valid_sis_params p = (
    sis_n p > 0 \<and>
    sis_m p > 0 \<and>
    sis_q p > 1 \<and>
    sis_beta p > 0)"

lemma valid_sis_params_pos:
  assumes "valid_sis_params p"
  shows "sis_n p > 0" "sis_m p > 0" "sis_q p > 1" "sis_beta p > 0"
  using assms unfolding valid_sis_params_def by auto

(* === Step 2: SIS Instance Type === *)
text \<open>
  An SIS instance is simply a matrix A over Z_q.
  The goal is to find a short non-zero vector z such that Az = 0 mod q.
\<close>

record sis_instance =
  sis_A :: int_matrix

definition valid_sis_instance :: "sis_params \<Rightarrow> sis_instance \<Rightarrow> bool" where
  "valid_sis_instance p inst = valid_matrix (sis_A inst) (sis_m p) (sis_n p)"

lemma valid_sis_instance_dims:
  assumes "valid_sis_instance p inst"
  shows "length (sis_A inst) = sis_m p"
    and "\<forall>row \<in> set (sis_A inst). length row = sis_n p"
  using assms unfolding valid_sis_instance_def valid_matrix_def by auto

(* === Step 3: SIS Solution Definition === *)
text \<open>
  A vector z is a valid SIS solution if:
  1. z has the right dimension (length n)
  2. z is non-zero
  3. z is short (all coefficients bounded by beta)
  4. Az = 0 mod q
\<close>

definition is_zero_vec :: "int_vec \<Rightarrow> bool" where
  "is_zero_vec v = (\<forall>x \<in> set v. x = 0)"

lemma is_zero_vec_alt:
  "is_zero_vec v = (\<forall>i < length v. v ! i = 0)"
proof
  assume asm: "is_zero_vec v"
  show "\<forall>i < length v. v ! i = 0"
  proof (intro allI impI)
    fix i assume "i < length v"
    hence "v ! i \<in> set v" by simp
    thus "v ! i = 0" using asm unfolding is_zero_vec_def by auto
  qed
next
  assume asm: "\<forall>i < length v. v ! i = 0"
  show "is_zero_vec v"
    unfolding is_zero_vec_def
  proof
    fix x assume "x \<in> set v"
    then obtain i where "i < length v" "v ! i = x"
      by (metis in_set_conv_nth)
    thus "x = 0" using asm by simp
  qed
qed

lemma is_zero_vec_Nil [simp]:
  "is_zero_vec []"
  unfolding is_zero_vec_def by simp

definition is_sis_solution :: "sis_params \<Rightarrow> sis_instance \<Rightarrow> int_vec \<Rightarrow> bool" where
  "is_sis_solution p inst z = (
    valid_vec z (sis_n p) \<and>
    \<not> is_zero_vec z \<and>
    all_bounded z (sis_beta p) \<and>
    is_zero_vec (vec_mod (mat_vec_mult (sis_A inst) z) (sis_q p)))"

lemma sis_solution_length:
  "is_sis_solution p inst z \<Longrightarrow> length z = sis_n p"
  unfolding is_sis_solution_def valid_vec_def by simp

lemma sis_solution_nonzero:
  "is_sis_solution p inst z \<Longrightarrow> \<not> is_zero_vec z"
  unfolding is_sis_solution_def by simp

lemma sis_solution_bounded:
  "is_sis_solution p inst z \<Longrightarrow> all_bounded z (sis_beta p)"
  unfolding is_sis_solution_def by simp

lemma sis_solution_kernel:
  "is_sis_solution p inst z \<Longrightarrow> is_zero_vec (vec_mod (mat_vec_mult (sis_A inst) z) (sis_q p))"
  unfolding is_sis_solution_def by simp

(* === Step 4: Alternative Kernel Characterization === *)
text \<open>
  Az = 0 mod q means each component (Az)_i is divisible by q.
\<close>

definition in_kernel_mod :: "int_matrix \<Rightarrow> int_vec \<Rightarrow> int \<Rightarrow> bool" where
  "in_kernel_mod A z q = (\<forall>i < length A. (mat_vec_mult A z) ! i mod q = 0)"

lemma is_zero_vec_mod_iff:
  assumes "q > 0"
  shows "is_zero_vec (vec_mod v q) \<longleftrightarrow> (\<forall>i < length v. v ! i mod q = 0)"
proof
  assume "is_zero_vec (vec_mod v q)"
  hence "\<forall>i < length (vec_mod v q). (vec_mod v q) ! i = 0"
    unfolding is_zero_vec_alt by simp
  hence "\<forall>i < length v. v ! i mod q = 0"
    by (simp add: vec_mod_length vec_mod_nth)
  thus "\<forall>i < length v. v ! i mod q = 0" .
next
  assume asm: "\<forall>i < length v. v ! i mod q = 0"
  show "is_zero_vec (vec_mod v q)"
    unfolding is_zero_vec_alt
  proof (intro allI impI)
    fix i assume "i < length (vec_mod v q)"
    hence "i < length v" by (simp add: vec_mod_length)
    hence "v ! i mod q = 0" using asm by simp
    thus "(vec_mod v q) ! i = 0"
      using `i < length v` by (simp add: vec_mod_nth)
  qed
qed

lemma in_kernel_mod_iff:
  assumes "q > 0"
  shows "in_kernel_mod A z q \<longleftrightarrow> is_zero_vec (vec_mod (mat_vec_mult A z) q)"
  unfolding in_kernel_mod_def
  using is_zero_vec_mod_iff[OF assms, of "mat_vec_mult A z"]
  by (simp add: mat_vec_mult_length)

(* === Step 5: Inhomogeneous SIS (ISIS) === *)
text \<open>
  Inhomogeneous SIS (ISIS):
  Given A and target vector t, find short z such that Az = t mod q.

  This is useful for:
  - Opening commitments
  - Signature schemes
  - Reduction proofs
\<close>

record isis_instance = sis_instance +
  isis_t :: int_vec

definition valid_isis_instance :: "sis_params \<Rightarrow> isis_instance \<Rightarrow> bool" where
  "valid_isis_instance p inst = (
    valid_sis_instance p (sis_instance.truncate inst) \<and>
    valid_vec (isis_t inst) (sis_m p))"

definition is_isis_solution :: "sis_params \<Rightarrow> isis_instance \<Rightarrow> int_vec \<Rightarrow> bool" where
  "is_isis_solution p inst z = (
    valid_vec z (sis_n p) \<and>
    all_bounded z (sis_beta p) \<and>
    vec_mod (mat_vec_mult (sis_A inst) z) (sis_q p) = vec_mod (isis_t inst) (sis_q p))"

lemma isis_solution_length:
  "is_isis_solution p inst z \<Longrightarrow> length z = sis_n p"
  unfolding is_isis_solution_def valid_vec_def by simp

lemma isis_solution_bounded:
  "is_isis_solution p inst z \<Longrightarrow> all_bounded z (sis_beta p)"
  unfolding is_isis_solution_def by simp

text \<open>
  Homogeneous SIS is ISIS with t = 0 (plus non-zero requirement).
\<close>

lemma sis_as_isis:
  assumes "is_sis_solution p \<lparr> sis_A = A \<rparr> z"
  assumes "sis_q p > 0"
  shows "is_isis_solution p \<lparr> sis_A = A, isis_t = replicate (length A) 0 \<rparr> z"
proof -
  define q :: int where "q = sis_q p"
  have len_z: "valid_vec z (sis_n p)"
    using assms(1) unfolding is_sis_solution_def by simp
  have bounded: "all_bounded z (sis_beta p)"
    using assms(1) unfolding is_sis_solution_def by simp
  have kernel: "is_zero_vec (vec_mod (mat_vec_mult A z) (sis_q p))"
    using assms(1) unfolding is_sis_solution_def by simp

  have Az_len: "length (mat_vec_mult A z) = length A"
    by (simp add: mat_vec_mult_length)

  have "vec_mod (mat_vec_mult A z) (sis_q p) = vec_mod (replicate (length A) 0) (sis_q p)"
  proof (intro nth_equalityI)
    show "length (vec_mod (mat_vec_mult A z) (sis_q p)) = length (vec_mod (replicate (length A) 0) (sis_q p))"
      by (simp add: vec_mod_length Az_len)
  next
    fix i assume "i < length (vec_mod (mat_vec_mult A z) (sis_q p))"
    hence i_lt: "i < length A" by (simp add: vec_mod_length Az_len)
    have lhs: "(vec_mod (mat_vec_mult A z) (sis_q p)) ! i = 0"
      using kernel i_lt unfolding is_zero_vec_alt
      by (simp add: vec_mod_length Az_len)
    have rhs: "(vec_mod (replicate (length A) 0) (sis_q p)) ! i = 0"
      using i_lt assms(2) by (simp add: vec_mod_nth)
    show "(vec_mod (mat_vec_mult A z) (sis_q p)) ! i = (vec_mod (replicate (length A) 0) (sis_q p)) ! i"
      using lhs rhs by simp
  qed

  thus ?thesis
    unfolding is_isis_solution_def using len_z bounded by simp
qed

(* === Step 6: SIS Hardness Predicate === *)
text \<open>
  SIS Hardness (informal):
  For appropriate parameters, no efficient algorithm can find an SIS solution
  with non-negligible probability.

  We define predicates for "has a solution" which can be used in security proofs.
\<close>

definition sis_has_solution :: "sis_params \<Rightarrow> sis_instance \<Rightarrow> bool" where
  "sis_has_solution p inst = (\<exists>z. is_sis_solution p inst z)"

definition isis_has_solution :: "sis_params \<Rightarrow> isis_instance \<Rightarrow> bool" where
  "isis_has_solution p inst = (\<exists>z. is_isis_solution p inst z)"

lemma sis_solution_witness:
  "sis_has_solution p inst \<Longrightarrow> \<exists>z. is_sis_solution p inst z"
  unfolding sis_has_solution_def by simp

lemma isis_solution_witness:
  "isis_has_solution p inst \<Longrightarrow> \<exists>z. is_isis_solution p inst z"
  unfolding isis_has_solution_def by simp

(* === Step 7: SIS Context Locale === *)
locale sis_context =
  fixes p :: sis_params
    and A :: int_matrix
  assumes params_ok: "valid_sis_params p"
    and A_ok: "valid_matrix A (sis_m p) (sis_n p)"
begin

abbreviation "n \<equiv> sis_n p"
abbreviation "m \<equiv> sis_m p"
abbreviation "q \<equiv> sis_q p"
abbreviation "beta \<equiv> sis_beta p"

lemma n_pos: "n > 0"
  using params_ok unfolding valid_sis_params_def by simp

lemma m_pos: "m > 0"
  using params_ok unfolding valid_sis_params_def by simp

lemma q_pos: "q > 1"
  using params_ok unfolding valid_sis_params_def by simp

lemma beta_pos: "beta > 0"
  using params_ok unfolding valid_sis_params_def by simp

lemma len_A: "length A = m"
  using A_ok unfolding valid_matrix_def by simp

lemma rows_A: "\<forall>row \<in> set A. length row = n"
  using A_ok unfolding valid_matrix_def by simp

definition "inst \<equiv> \<lparr> sis_A = A \<rparr>"

lemma inst_valid: "valid_sis_instance p inst"
  unfolding inst_def valid_sis_instance_def using A_ok by simp

end

(* === Step 8: Collision Implies SIS Solution === *)
text \<open>
  Collision to SIS Reduction:
  If Az1 = Az2 mod q with z1 ≠ z2 and both short, then z1 - z2 is an SIS solution.

  This is the core of proving binding for SIS-based commitments.
\<close>

text \<open>
  We need these helper lemmas about mat_vec_mult distributing over subtraction.
\<close>

lemma inner_prod_sub:
  assumes "length z1 = length z2"
  shows "inner_prod row (vec_sub z1 z2) = inner_prod row z1 - inner_prod row z2"
proof -
  define n where "n = min (length row) (length z1)"
  have len_sub: "length (vec_sub z1 z2) = length z1"
    using assms by (simp add: vec_sub_length)
  have "inner_prod row (vec_sub z1 z2) = (\<Sum>i = 0 ..< n. row ! i * (vec_sub z1 z2) ! i)"
    unfolding n_def using len_sub by (simp add: inner_prod_nth_min)
  also have "... = (\<Sum>i = 0 ..< n. row ! i * (z1 ! i - z2 ! i))"
  proof (rule sum.cong)
    fix i assume "i \<in> {0 ..< n}"
    hence "i < length z1" unfolding n_def by simp
    thus "row ! i * (vec_sub z1 z2) ! i = row ! i * (z1 ! i - z2 ! i)"
      using assms by (simp add: vec_sub_def)
  qed simp
  also have "... = (\<Sum>i = 0 ..< n. row ! i * z1 ! i - row ! i * z2 ! i)"
    by (simp add: algebra_simps)
  also have "... = (\<Sum>i = 0 ..< n. row ! i * z1 ! i) - (\<Sum>i = 0 ..< n. row ! i * z2 ! i)"
    by (simp add: sum_subtractf)
  also have "... = inner_prod row z1 - inner_prod row z2"
    unfolding n_def using assms by (simp add: inner_prod_nth_min)
  finally show ?thesis .
qed

lemma mat_vec_mult_sub:
  assumes "length z1 = length z2"
  shows "mat_vec_mult A (vec_sub z1 z2) = vec_sub (mat_vec_mult A z1) (mat_vec_mult A z2)"
proof (intro nth_equalityI)
  show "length (mat_vec_mult A (vec_sub z1 z2)) =
        length (vec_sub (mat_vec_mult A z1) (mat_vec_mult A z2))"
    by (simp add: mat_vec_mult_length vec_sub_length)
next
  fix i assume "i < length (mat_vec_mult A (vec_sub z1 z2))"
  hence i_lt: "i < length A" by (simp add: mat_vec_mult_length)

  have "(mat_vec_mult A (vec_sub z1 z2)) ! i = inner_prod (A ! i) (vec_sub z1 z2)"
    using i_lt by (simp add: mat_vec_mult_nth)
  also have "... = inner_prod (A ! i) z1 - inner_prod (A ! i) z2"
    using inner_prod_sub[OF assms] by simp
  also have "... = (mat_vec_mult A z1) ! i - (mat_vec_mult A z2) ! i"
    using i_lt by (simp add: mat_vec_mult_nth)
  also have "... = (vec_sub (mat_vec_mult A z1) (mat_vec_mult A z2)) ! i"
    using i_lt by (simp add: vec_sub_def mat_vec_mult_length)
  finally show "(mat_vec_mult A (vec_sub z1 z2)) ! i =
                (vec_sub (mat_vec_mult A z1) (mat_vec_mult A z2)) ! i" .
qed

lemma mat_vec_mult_sub_nth:
  assumes "i < length A"
  assumes "length z1 = length z2"
  shows "(mat_vec_mult A (vec_sub z1 z2)) ! i =
         (mat_vec_mult A z1) ! i - (mat_vec_mult A z2) ! i"
  using mat_vec_mult_sub[OF assms(2)] assms(1)
  by (simp add: vec_sub_def mat_vec_mult_length)

lemma collision_to_sis:
  assumes len_z1: "length z1 = n"
  assumes len_z2: "length z2 = n"
  assumes z1_bounded: "all_bounded z1 B"
  assumes z2_bounded: "all_bounded z2 B"
  assumes collision: "vec_mod (mat_vec_mult A z1) q = vec_mod (mat_vec_mult A z2) q"
  assumes diff_nonzero: "\<not> is_zero_vec (vec_sub z1 z2)"
  assumes q_pos: "(q::int) > 0"
  assumes B_pos: "(B::int) >= 0"
  shows "is_zero_vec (vec_mod (mat_vec_mult A (vec_sub z1 z2)) q)"
proof -
  let ?diff = "vec_sub z1 z2"
  have len_eq: "length z1 = length z2" using len_z1 len_z2 by simp
  have len_diff: "length ?diff = n"
    using len_z1 len_z2 by (simp add: vec_sub_length)

  have "mat_vec_mult A ?diff = vec_sub (mat_vec_mult A z1) (mat_vec_mult A z2)"
    using mat_vec_mult_sub[OF len_eq] by simp

  hence "vec_mod (mat_vec_mult A ?diff) q =
         vec_mod (vec_sub (mat_vec_mult A z1) (mat_vec_mult A z2)) q"
    by simp

  have len_Az1: "length (mat_vec_mult A z1) = length A"
    by (simp add: mat_vec_mult_length)
  have len_Az2: "length (mat_vec_mult A z2) = length A"
    by (simp add: mat_vec_mult_length)

  show ?thesis
    unfolding is_zero_vec_alt
  proof (intro allI impI)
    fix i assume i_lt: "i < length (vec_mod (mat_vec_mult A ?diff) q)"
    hence i_lt_A: "i < length A"
      by (simp add: vec_mod_length mat_vec_mult_length)

    have eq_mod: "(mat_vec_mult A z1) ! i mod q = (mat_vec_mult A z2) ! i mod q"
      using collision i_lt_A len_Az1 len_Az2
      by (metis nth_equalityI vec_mod_length vec_mod_nth)

    have "((mat_vec_mult A z1) ! i - (mat_vec_mult A z2) ! i) mod q =
          ((mat_vec_mult A z1) ! i mod q - (mat_vec_mult A z2) ! i mod q) mod q"
      by (simp add: mod_diff_eq)
    also have "... = 0" using eq_mod by simp
    finally have diff_mod: "((mat_vec_mult A z1) ! i - (mat_vec_mult A z2) ! i) mod q = 0" .

    have "(mat_vec_mult A ?diff) ! i = (mat_vec_mult A z1) ! i - (mat_vec_mult A z2) ! i"
      using mat_vec_mult_sub_nth[OF i_lt_A len_eq] by simp

    hence "(mat_vec_mult A ?diff) ! i mod q = 0"
      using diff_mod by simp

    thus "(vec_mod (mat_vec_mult A ?diff) q) ! i = 0"
      using i_lt by (simp add: vec_mod_nth vec_mod_length mat_vec_mult_length)
  qed
qed

(* === Step 9: Code Export === *)
(* Note: sis_has_solution and isis_has_solution use existentials and cannot be exported *)
export_code
  sis_params.make valid_sis_params
  sis_n sis_m sis_q sis_beta
  sis_instance.make valid_sis_instance
  sis_A
  is_zero_vec is_sis_solution
  in_kernel_mod
  isis_instance.make valid_isis_instance is_isis_solution
  isis_t
  in Haskell module_name "Canon.Hardness.SIS_Def"

end
