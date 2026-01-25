theory Commit_SIS
  imports Canon_Base.Prelude Canon_Base.ListVec Canon_Base.Zq Canon_Base.Norms Canon_Hardness.SIS_Def
begin

(* === Step 1: Commitment Parameters === *)
text \<open>
  SIS-based Commitment Parameters:

  The commitment scheme uses matrix A in Z_q^{m x (n1 + n2)} where:
  - n1: dimension of message space
  - n2: dimension of randomness space
  - m: number of rows (output dimension)
  - q: modulus
  - beta: bound on valid openings

  Commitment: c = A * [msg; rand] mod q
  Opening: (msg, rand) such that c = A * [msg; rand] mod q and ||(msg, rand)||_inf <= beta
\<close>

record commit_params =
  cp_n1 :: nat    \<comment> \<open>message dimension\<close>
  cp_n2 :: nat    \<comment> \<open>randomness dimension\<close>
  cp_m :: nat     \<comment> \<open>output dimension (rows of A)\<close>
  cp_q :: int     \<comment> \<open>modulus\<close>
  cp_beta :: int  \<comment> \<open>bound on opening coefficients\<close>

definition valid_commit_params :: "commit_params \<Rightarrow> bool" where
  "valid_commit_params p = (
    cp_n1 p > 0 \<and>
    cp_n2 p > 0 \<and>
    cp_m p > 0 \<and>
    cp_q p > 1 \<and>
    cp_beta p > 0)"

lemma valid_commit_params_pos:
  assumes "valid_commit_params p"
  shows "cp_n1 p > 0" "cp_n2 p > 0" "cp_m p > 0" "cp_q p > 1" "cp_beta p > 0"
  using assms unfolding valid_commit_params_def by auto

definition commit_total_dim :: "commit_params \<Rightarrow> nat" where
  "commit_total_dim p = cp_n1 p + cp_n2 p"

(* === Step 2: Commitment Key === *)
text \<open>
  Commitment Key: matrix A \<in> Z_q^{m \<times> (n1 + n2)}

  The matrix can be viewed as A = [A1 | A2] where:
  - A1 \<in> Z_q^{m \<times> n1} acts on the message
  - A2 \<in> Z_q^{m \<times> n2} acts on the randomness
\<close>

type_synonym commit_key = int_matrix

definition valid_commit_key :: "commit_params \<Rightarrow> commit_key \<Rightarrow> bool" where
  "valid_commit_key p ck = valid_matrix ck (cp_m p) (commit_total_dim p)"

lemma valid_commit_key_dims:
  assumes "valid_commit_key p ck"
  shows "length ck = cp_m p"
    and "\<forall>row \<in> set ck. length row = cp_n1 p + cp_n2 p"
  using assms unfolding valid_commit_key_def valid_matrix_def commit_total_dim_def
  by auto

(* === Step 3: Commitment and Opening Types === *)
text \<open>
  Commitment: a vector in Z_q^m
  Opening: a pair (message, randomness) where message \<in> Z^{n1}, randomness \<in> Z^{n2}
\<close>

type_synonym commitment = int_vec

record commit_opening =
  open_msg :: int_vec
  open_rand :: int_vec

definition valid_commitment :: "commit_params \<Rightarrow> commitment \<Rightarrow> bool" where
  "valid_commitment p c = valid_vec c (cp_m p)"

definition valid_opening :: "commit_params \<Rightarrow> commit_opening \<Rightarrow> bool" where
  "valid_opening p op = (
    valid_vec (open_msg op) (cp_n1 p) \<and>
    valid_vec (open_rand op) (cp_n2 p) \<and>
    all_bounded (open_msg op @ open_rand op) (cp_beta p))"

lemma valid_opening_msg_len:
  "valid_opening p op \<Longrightarrow> length (open_msg op) = cp_n1 p"
  unfolding valid_opening_def valid_vec_def by simp

lemma valid_opening_rand_len:
  "valid_opening p op \<Longrightarrow> length (open_rand op) = cp_n2 p"
  unfolding valid_opening_def valid_vec_def by simp

lemma valid_opening_bounded:
  "valid_opening p op \<Longrightarrow> all_bounded (open_msg op @ open_rand op) (cp_beta p)"
  unfolding valid_opening_def by simp

(* === Step 4: Commit Function === *)
text \<open>
  Commit(ck, msg, rand) = A \<cdot> [msg || rand] mod q

  The opening vector is the concatenation of message and randomness.
\<close>

definition opening_vec :: "commit_opening \<Rightarrow> int_vec" where
  "opening_vec op = open_msg op @ open_rand op"

lemma opening_vec_length:
  assumes "valid_opening p op"
  shows "length (opening_vec op) = cp_n1 p + cp_n2 p"
  unfolding opening_vec_def
  using valid_opening_msg_len[OF assms] valid_opening_rand_len[OF assms]
  by simp

definition commit :: "commit_key \<Rightarrow> commit_opening \<Rightarrow> int \<Rightarrow> commitment" where
  "commit ck op q = vec_mod (mat_vec_mult ck (opening_vec op)) q"

lemma commit_length:
  "length (commit ck op q) = length ck"
  unfolding commit_def by (simp add: vec_mod_length mat_vec_mult_length)

lemma commit_valid:
  assumes "valid_commit_params p"
  assumes "valid_commit_key p ck"
  assumes "valid_opening p op"
  shows "valid_commitment p (commit ck op (cp_q p))"
proof -
  have "length (commit ck op (cp_q p)) = length ck"
    by (simp add: commit_length)
  also have "... = cp_m p"
    using valid_commit_key_dims[OF assms(2)] by simp
  finally show ?thesis
    unfolding valid_commitment_def valid_vec_def by simp
qed

(* === Step 5: Opening Verification === *)
text \<open>
  Verify(ck, c, op) checks:
  1. The opening has correct dimensions
  2. The opening coefficients are bounded
  3. A \<cdot> [msg || rand] = c mod q
\<close>

definition verify_opening :: "commit_params \<Rightarrow> commit_key \<Rightarrow> commitment \<Rightarrow> commit_opening \<Rightarrow> bool" where
  "verify_opening p ck c op = (
    valid_opening p op \<and>
    commit ck op (cp_q p) = c)"

lemma verify_opening_valid:
  "verify_opening p ck c op \<Longrightarrow> valid_opening p op"
  unfolding verify_opening_def by simp

lemma verify_opening_eq:
  "verify_opening p ck c op \<Longrightarrow> commit ck op (cp_q p) = c"
  unfolding verify_opening_def by simp

text \<open>
  Correctness: if we commit with a valid opening, verification succeeds.
\<close>

lemma commit_verify_correct:
  assumes "valid_commit_params p"
  assumes "valid_commit_key p ck"
  assumes "valid_opening p op"
  shows "verify_opening p ck (commit ck op (cp_q p)) op"
  unfolding verify_opening_def using assms(3) by simp

(* === Step 6: Binding Definition === *)
text \<open>
  Binding: it is hard to find two different openings for the same commitment.

  A binding break is a tuple (c, op1, op2) where:
  - verify(ck, c, op1) = true
  - verify(ck, c, op2) = true
  - op1 \<noteq> op2
\<close>

definition is_binding_break :: "commit_params \<Rightarrow> commit_key \<Rightarrow> commitment \<Rightarrow> commit_opening \<Rightarrow> commit_opening \<Rightarrow> bool" where
  "is_binding_break p ck c op1 op2 = (
    verify_opening p ck c op1 \<and>
    verify_opening p ck c op2 \<and>
    opening_vec op1 \<noteq> opening_vec op2)"

lemma binding_break_verify1:
  "is_binding_break p ck c op1 op2 \<Longrightarrow> verify_opening p ck c op1"
  unfolding is_binding_break_def by simp

lemma binding_break_verify2:
  "is_binding_break p ck c op1 op2 \<Longrightarrow> verify_opening p ck c op2"
  unfolding is_binding_break_def by simp

lemma binding_break_different:
  "is_binding_break p ck c op1 op2 \<Longrightarrow> opening_vec op1 \<noteq> opening_vec op2"
  unfolding is_binding_break_def by simp

(* === Step 7: Binding Implies SIS Solution === *)
text \<open>
  Key Security Reduction:

  If (c, op1, op2) is a binding break, then z = opening_vec(op1) - opening_vec(op2)
  is a non-zero short vector in the kernel of A mod q, i.e., an SIS solution.

  This shows: breaking binding \<le> solving SIS.
\<close>

definition binding_to_sis_witness :: "commit_opening \<Rightarrow> commit_opening \<Rightarrow> int_vec" where
  "binding_to_sis_witness op1 op2 = vec_sub (opening_vec op1) (opening_vec op2)"

lemma vec_sub_self_zero:
  "vec_sub v v = replicate (length v) 0"
  unfolding vec_sub_def by (induct v) auto

lemma vec_sub_nth:
  assumes "i < min (length v1) (length v2)"
  shows "(vec_sub v1 v2) ! i = v1 ! i - v2 ! i"
  using assms unfolding vec_sub_def by simp

text \<open>Helper: if two equal-length vectors are different, their difference is not all zeros.\<close>

lemma vec_sub_eq_zero_imp_eq:
  assumes len_eq: "length v1 = length v2"
  assumes sub_zero: "vec_sub v1 v2 = replicate (length v1) (0::int)"
  shows "v1 = v2"
proof (rule nth_equalityI)
  show "length v1 = length v2" using len_eq .
next
  fix i assume "i < length v1"
  hence i_bound: "i < min (length v1) (length v2)" using len_eq by simp
  have "(vec_sub v1 v2) ! i = 0"
    using sub_zero \<open>i < length v1\<close> by simp
  hence "v1 ! i - v2 ! i = 0"
    using vec_sub_nth[OF i_bound] by simp
  thus "v1 ! i = v2 ! i" by simp
qed

lemma vec_neq_imp_sub_neq_zero:
  assumes len_eq: "length v1 = length v2"
  assumes neq: "v1 \<noteq> v2"
  shows "vec_sub v1 v2 \<noteq> replicate (length v1) (0::int)"
  using vec_sub_eq_zero_imp_eq[OF len_eq] neq by auto

lemma all_zero_replicate:
  "(\<forall>x \<in> set v. x = (0::int)) \<Longrightarrow> v = replicate (length v) 0"
  by (induct v) auto

lemma neq_replicate_not_zero_vec:
  assumes "v \<noteq> replicate (length v) (0::int)"
  shows "\<not> is_zero_vec v"
proof
  assume "is_zero_vec v"
  hence "v = replicate (length v) 0"
    unfolding is_zero_vec_def using all_zero_replicate by simp
  thus False using assms by simp
qed

lemma binding_to_sis_nonzero:
  assumes "is_binding_break p ck c op1 op2"
  shows "\<not> is_zero_vec (binding_to_sis_witness op1 op2)"
proof -
  have v1: "valid_opening p op1"
    using binding_break_verify1[OF assms] verify_opening_valid by simp
  have v2: "valid_opening p op2"
    using binding_break_verify2[OF assms] verify_opening_valid by simp

  have len1: "length (opening_vec op1) = cp_n1 p + cp_n2 p"
    using opening_vec_length[OF v1] .
  have len2: "length (opening_vec op2) = cp_n1 p + cp_n2 p"
    using opening_vec_length[OF v2] .
  have len_eq: "length (opening_vec op1) = length (opening_vec op2)"
    using len1 len2 by simp

  have neq: "opening_vec op1 \<noteq> opening_vec op2"
    using binding_break_different[OF assms] .

  let ?diff = "vec_sub (opening_vec op1) (opening_vec op2)"
  have diff_neq: "?diff \<noteq> replicate (length (opening_vec op1)) 0"
    using vec_neq_imp_sub_neq_zero[OF len_eq neq] .

  have len_diff: "length ?diff = length (opening_vec op1)"
    using len_eq by (simp add: vec_sub_length)

  have "?diff \<noteq> replicate (length ?diff) 0"
    using diff_neq len_diff by simp

  hence "\<not> is_zero_vec ?diff"
    using neq_replicate_not_zero_vec by simp

  thus ?thesis
    unfolding binding_to_sis_witness_def by simp
qed

lemma binding_to_sis_length:
  assumes "is_binding_break p ck c op1 op2"
  shows "length (binding_to_sis_witness op1 op2) = cp_n1 p + cp_n2 p"
proof -
  have v1: "valid_opening p op1"
    using binding_break_verify1[OF assms] verify_opening_valid by simp
  have v2: "valid_opening p op2"
    using binding_break_verify2[OF assms] verify_opening_valid by simp
  have "length (opening_vec op1) = cp_n1 p + cp_n2 p"
    using opening_vec_length[OF v1] .
  moreover have "length (opening_vec op2) = cp_n1 p + cp_n2 p"
    using opening_vec_length[OF v2] .
  ultimately show ?thesis
    unfolding binding_to_sis_witness_def by (simp add: vec_sub_length)
qed

text \<open>
  Helper: inner product distributes over vector subtraction (when lengths match).
\<close>

lemma inner_prod_vec_sub_eq_len:
  assumes "length v1 = length v2"
  shows "inner_prod u (vec_sub v1 v2) = inner_prod u v1 - inner_prod u v2"
proof -
  let ?n = "min (length u) (length v1)"
  have len_sub: "length (vec_sub v1 v2) = length v1"
    using assms by (simp add: vec_sub_length)
  have "inner_prod u (vec_sub v1 v2) =
        (\<Sum>i = 0 ..< min (length u) (length (vec_sub v1 v2)). u ! i * (vec_sub v1 v2) ! i)"
    by (simp add: inner_prod_nth_min)
  also have "... = (\<Sum>i = 0 ..< ?n. u ! i * (vec_sub v1 v2) ! i)"
    using len_sub by simp
  also have "... = (\<Sum>i = 0 ..< ?n. u ! i * (v1 ! i - v2 ! i))"
  proof (rule sum.cong, simp)
    fix i assume "i \<in> {0 ..< ?n}"
    hence "i < length v1" and "i < length v2" using assms by auto
    thus "u ! i * (vec_sub v1 v2) ! i = u ! i * (v1 ! i - v2 ! i)"
      by (simp add: vec_sub_nth)
  qed
  also have "... = (\<Sum>i = 0 ..< ?n. u ! i * v1 ! i - u ! i * v2 ! i)"
    by (simp add: algebra_simps)
  also have "... = (\<Sum>i = 0 ..< ?n. u ! i * v1 ! i) - (\<Sum>i = 0 ..< ?n. u ! i * v2 ! i)"
    by (simp add: sum_subtractf)
  also have "... = inner_prod u v1 - inner_prod u v2"
    using assms by (simp add: inner_prod_nth_min)
  finally show ?thesis .
qed

lemma mat_vec_mult_sub_nth:
  assumes "i < length A"
  assumes "length z1 = length z2"
  shows "(mat_vec_mult A (vec_sub z1 z2)) ! i =
         (mat_vec_mult A z1) ! i - (mat_vec_mult A z2) ! i"
proof -
  have "(mat_vec_mult A (vec_sub z1 z2)) ! i = inner_prod (A ! i) (vec_sub z1 z2)"
    using assms(1) by (simp add: mat_vec_mult_nth)
  also have "... = inner_prod (A ! i) z1 - inner_prod (A ! i) z2"
    using inner_prod_vec_sub_eq_len[OF assms(2)] by simp
  also have "... = (mat_vec_mult A z1) ! i - (mat_vec_mult A z2) ! i"
    using assms(1) by (simp add: mat_vec_mult_nth)
  finally show ?thesis .
qed

lemma collision_to_sis_kernel:
  assumes len1: "length z1 = n" and len2: "length z2 = n"
  assumes collision: "vec_mod (mat_vec_mult A z1) q = vec_mod (mat_vec_mult A z2) q"
  assumes diff_nonzero: "\<not> is_zero_vec (vec_sub z1 z2)"
  assumes q_pos: "q > 0"
  shows "is_zero_vec (vec_mod (mat_vec_mult A (vec_sub z1 z2)) q)"
proof -
  have len_eq: "length z1 = length z2"
    using len1 len2 by simp
  have len_Az1: "length (mat_vec_mult A z1) = length A"
    by (simp add: mat_vec_mult_length)
  have len_Az2: "length (mat_vec_mult A z2) = length A"
    by (simp add: mat_vec_mult_length)

  show ?thesis
    unfolding is_zero_vec_alt
  proof (intro allI impI)
    fix i assume i_lt: "i < length (vec_mod (mat_vec_mult A (vec_sub z1 z2)) q)"
    hence i_lt_A: "i < length A"
      by (simp add: vec_mod_length mat_vec_mult_length)

    have "(vec_mod (mat_vec_mult A z1) q) ! i = (vec_mod (mat_vec_mult A z2) q) ! i"
      using collision by simp
    hence mod_eq: "(mat_vec_mult A z1) ! i mod q = (mat_vec_mult A z2) ! i mod q"
      using i_lt_A len_Az1 len_Az2 by (simp add: vec_mod_nth)

    hence diff_mod: "((mat_vec_mult A z1) ! i - (mat_vec_mult A z2) ! i) mod q = 0"
    proof -
      let ?a = "(mat_vec_mult A z1) ! i"
      let ?b = "(mat_vec_mult A z2) ! i"
      have "(?a - ?b) mod q = (?a mod q - ?b mod q) mod q"
        by (simp add: mod_diff_eq)
      also have "... = (?a mod q - ?a mod q) mod q"
        using mod_eq by simp
      also have "... = 0" by simp
      finally show ?thesis .
    qed

    have "(mat_vec_mult A (vec_sub z1 z2)) ! i =
          (mat_vec_mult A z1) ! i - (mat_vec_mult A z2) ! i"
      using mat_vec_mult_sub_nth[OF i_lt_A len_eq] .

    hence "(mat_vec_mult A (vec_sub z1 z2)) ! i mod q = 0"
      using diff_mod by simp

    thus "(vec_mod (mat_vec_mult A (vec_sub z1 z2)) q) ! i = 0"
      using i_lt by (simp add: vec_mod_nth vec_mod_length mat_vec_mult_length)
  qed
qed

lemma binding_to_sis_kernel:
  assumes break: "is_binding_break p ck c op1 op2"
  assumes q_pos: "cp_q p > 0"
  shows "is_zero_vec (vec_mod (mat_vec_mult ck (binding_to_sis_witness op1 op2)) (cp_q p))"
proof -
  let ?z1 = "opening_vec op1"
  let ?z2 = "opening_vec op2"
  let ?q = "cp_q p"

  have v1: "verify_opening p ck c op1"
    using binding_break_verify1[OF break] .
  have v2: "verify_opening p ck c op2"
    using binding_break_verify2[OF break] .

  have eq1: "commit ck op1 ?q = c"
    using verify_opening_eq[OF v1] .
  have eq2: "commit ck op2 ?q = c"
    using verify_opening_eq[OF v2] .

  have collision: "vec_mod (mat_vec_mult ck ?z1) ?q = vec_mod (mat_vec_mult ck ?z2) ?q"
    using eq1 eq2 unfolding commit_def opening_vec_def by simp

  have vo1: "valid_opening p op1"
    using v1 verify_opening_valid by simp
  have vo2: "valid_opening p op2"
    using v2 verify_opening_valid by simp

  have len1: "length ?z1 = cp_n1 p + cp_n2 p"
    using opening_vec_length[OF vo1] .
  have len2: "length ?z2 = cp_n1 p + cp_n2 p"
    using opening_vec_length[OF vo2] .

  have diff_nonzero: "\<not> is_zero_vec (vec_sub ?z1 ?z2)"
    using binding_to_sis_nonzero[OF break]
    unfolding binding_to_sis_witness_def .

  show ?thesis
    unfolding binding_to_sis_witness_def
    using collision_to_sis_kernel[OF len1 len2 collision diff_nonzero q_pos]
    by simp
qed

(* === Step 8: Full Binding Reduction === *)
text \<open>
  Main Binding Theorem:

  A binding break for the commitment scheme yields an SIS solution.
  The SIS instance has:
  - Matrix: the commitment key ck
  - Dimension: n1 + n2
  - Modulus: q
  - Solution bound: 2 * beta (since we take difference of two bounded vectors)
\<close>

definition commit_to_sis_params :: "commit_params \<Rightarrow> sis_params" where
  "commit_to_sis_params p = \<lparr>
    sis_n = cp_n1 p + cp_n2 p,
    sis_m = cp_m p,
    sis_q = cp_q p,
    sis_beta = 2 * cp_beta p
  \<rparr>"

lemma commit_to_sis_params_valid:
  assumes "valid_commit_params p"
  shows "valid_sis_params (commit_to_sis_params p)"
  unfolding commit_to_sis_params_def valid_sis_params_def
  using valid_commit_params_pos[OF assms] by simp

text \<open>
  Helper: subtraction of bounded vectors is bounded by sum of bounds.
\<close>

lemma vec_sub_bounded:
  assumes "all_bounded v1 B1" and "all_bounded v2 B2"
  shows "all_bounded (vec_sub v1 v2) (B1 + B2)"
  unfolding all_bounded_def vec_sub_def
proof
  fix x assume "x \<in> set (map2 (-) v1 v2)"
  then obtain i where i_bound: "i < min (length v1) (length v2)" and x_eq: "x = v1 ! i - v2 ! i"
    by (auto simp: in_set_conv_nth)
  have "abs (v1 ! i) \<le> B1"
    using assms(1) i_bound
    unfolding all_bounded_def by (simp add: nth_mem)
  moreover have "abs (v2 ! i) \<le> B2"
    using assms(2) i_bound
    unfolding all_bounded_def by (simp add: nth_mem)
  ultimately have "abs (v1 ! i - v2 ! i) \<le> abs (v1 ! i) + abs (v2 ! i)"
    by (simp add: abs_triangle_ineq4)
  also have "... \<le> B1 + B2"
    using \<open>abs (v1 ! i) \<le> B1\<close> \<open>abs (v2 ! i) \<le> B2\<close> by simp
  finally show "abs x \<le> B1 + B2"
    using x_eq by simp
qed

theorem binding_implies_sis:
  assumes params_ok: "valid_commit_params p"
  assumes key_ok: "valid_commit_key p ck"
  assumes break: "is_binding_break p ck c op1 op2"
  shows "\<exists>z. valid_vec z (cp_n1 p + cp_n2 p) \<and>
             \<not> is_zero_vec z \<and>
             all_bounded z (2 * cp_beta p) \<and>
             is_zero_vec (vec_mod (mat_vec_mult ck z) (cp_q p))"
proof -
  let ?z = "binding_to_sis_witness op1 op2"
  let ?q = "cp_q p"

  have q_pos: "?q > 0"
    using valid_commit_params_pos[OF params_ok] by simp

  have len_z: "length ?z = cp_n1 p + cp_n2 p"
    using binding_to_sis_length[OF break] .

  have nonzero: "\<not> is_zero_vec ?z"
    using binding_to_sis_nonzero[OF break] .

  have kernel: "is_zero_vec (vec_mod (mat_vec_mult ck ?z) ?q)"
    using binding_to_sis_kernel[OF break q_pos] .

  have bounded: "all_bounded ?z (2 * cp_beta p)"
  proof -
    have v1: "valid_opening p op1"
      using binding_break_verify1[OF break] verify_opening_valid by simp
    have v2: "valid_opening p op2"
      using binding_break_verify2[OF break] verify_opening_valid by simp

    have b1: "all_bounded (opening_vec op1) (cp_beta p)"
      using valid_opening_bounded[OF v1] unfolding opening_vec_def .
    have b2: "all_bounded (opening_vec op2) (cp_beta p)"
      using valid_opening_bounded[OF v2] unfolding opening_vec_def .

    show ?thesis
      unfolding binding_to_sis_witness_def
      using vec_sub_bounded[OF b1 b2] by simp
  qed

  show ?thesis
    using len_z nonzero bounded kernel
    unfolding valid_vec_def by auto
qed

(* === Step 9: Commitment Context Locale === *)
locale commit_context =
  fixes p :: commit_params
    and ck :: commit_key
  assumes params_ok: "valid_commit_params p"
    and key_ok: "valid_commit_key p ck"
begin

abbreviation "n1 \<equiv> cp_n1 p"
abbreviation "n2 \<equiv> cp_n2 p"
abbreviation "m \<equiv> cp_m p"
abbreviation "q \<equiv> cp_q p"
abbreviation "beta \<equiv> cp_beta p"

lemma n1_pos: "n1 > 0"
  using params_ok unfolding valid_commit_params_def by simp

lemma n2_pos: "n2 > 0"
  using params_ok unfolding valid_commit_params_def by simp

lemma m_pos: "m > 0"
  using params_ok unfolding valid_commit_params_def by simp

lemma q_pos: "q > 1"
  using params_ok unfolding valid_commit_params_def by simp

lemma beta_pos: "beta > 0"
  using params_ok unfolding valid_commit_params_def by simp

lemma key_rows: "length ck = m"
  using key_ok unfolding valid_commit_key_def valid_matrix_def by simp

lemma key_cols: "\<forall>row \<in> set ck. length row = n1 + n2"
  using key_ok unfolding valid_commit_key_def valid_matrix_def commit_total_dim_def by simp

lemma commit_correct:
  assumes "valid_opening p op"
  shows "verify_opening p ck (commit ck op q) op"
  using commit_verify_correct[OF params_ok key_ok assms] .

lemma binding_security:
  assumes "is_binding_break p ck c op1 op2"
  shows "\<exists>z. valid_vec z (n1 + n2) \<and>
             \<not> is_zero_vec z \<and>
             all_bounded z (2 * beta) \<and>
             is_zero_vec (vec_mod (mat_vec_mult ck z) q)"
  using binding_implies_sis[OF params_ok key_ok assms] .

end

(* === Step 10: Code Export === *)
export_code
  commit_params.make valid_commit_params commit_total_dim
  cp_n1 cp_n2 cp_m cp_q cp_beta
  valid_commit_key
  commit_opening.make valid_opening opening_vec
  open_msg open_rand
  commit verify_opening
  is_binding_break binding_to_sis_witness
  in Haskell module_name "Canon.Crypto.Commit_SIS"

end
