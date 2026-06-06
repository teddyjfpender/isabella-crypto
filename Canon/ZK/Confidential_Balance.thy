theory Confidential_Balance
  imports Canon_Crypto.Commit_SIS Repeated_FS
begin

text \<open>
  Confidential balance proofs over SIS commitments.

  This theory focuses on the smallest contract-verifiable slice needed for
  confidential transfers: proving that an aggregated input-output commitment
  opens to zero message while keeping the blinding witness hidden.

  We specialize to scalar amounts (\<open>cp_n1 = 1\<close>) and reuse the randomness
  columns of the commitment key as the public statement matrix.
\<close>

definition valid_scalar_commit_params :: "commit_params \<Rightarrow> bool" where
  "valid_scalar_commit_params p \<longleftrightarrow>
    valid_commit_params p \<and> cp_n1 p = 1"

lemma valid_scalar_commit_params_props:
  assumes "valid_scalar_commit_params p"
  shows "valid_commit_params p"
    and "cp_n1 p = 1"
    and "cp_n2 p > 0"
    and "cp_m p > 0"
    and "cp_q p > 1"
    and "cp_beta p > 0"
  using assms valid_commit_params_pos
  unfolding valid_scalar_commit_params_def
  by auto

definition valid_confidential_commit_key :: "commit_params \<Rightarrow> commit_key \<Rightarrow> bool" where
  "valid_confidential_commit_key p ck \<longleftrightarrow> separating_commit_key p ck"

lemma valid_confidential_commit_key_valid:
  assumes "valid_confidential_commit_key p ck"
  shows "valid_commit_key p ck"
  using assms
  unfolding valid_confidential_commit_key_def
  by (rule separating_commit_key_valid)

definition rand_commit_key :: "commit_params \<Rightarrow> commit_key \<Rightarrow> int_matrix" where
  "rand_commit_key p ck = map (drop (cp_n1 p)) ck"

lemma rand_commit_key_dims:
  assumes "valid_commit_key p ck"
  shows "length (rand_commit_key p ck) = cp_m p"
    and "\<forall>row \<in> set (rand_commit_key p ck). length row = cp_n2 p"
proof -
  show "length (rand_commit_key p ck) = cp_m p"
    using assms
    unfolding rand_commit_key_def
    by (simp add: valid_commit_key_dims)
next
  have row_len:
    "\<forall>row \<in> set ck. length row = cp_n1 p + cp_n2 p"
    using valid_commit_key_dims[OF assms] by simp
  show "\<forall>row \<in> set (rand_commit_key p ck). length row = cp_n2 p"
    unfolding rand_commit_key_def
  proof
    fix row
    assume "row \<in> set (map (drop (cp_n1 p)) ck)"
    then obtain row0 where row0_in: "row0 \<in> set ck" and row_def: "row = drop (cp_n1 p) row0"
      by auto
    have "length row0 = cp_n1 p + cp_n2 p"
      using row_len row0_in by auto
    then show "length row = cp_n2 p"
      using row_def by simp
  qed
qed

definition rand_commit :: "commit_params \<Rightarrow> commit_key \<Rightarrow> int_vec \<Rightarrow> commitment" where
  "rand_commit p ck r = vec_mod (mat_vec_mult (rand_commit_key p ck) r) (cp_q p)"

definition amount_of_opening :: "commit_opening \<Rightarrow> int" where
  "amount_of_opening op = open_msg op ! 0"

definition valid_scalar_opening :: "commit_params \<Rightarrow> commit_opening \<Rightarrow> bool" where
  "valid_scalar_opening p op \<longleftrightarrow>
    valid_scalar_commit_params p \<and> valid_opening p op"

definition zero_opening :: "int_vec \<Rightarrow> commit_opening" where
  "zero_opening r = \<lparr> open_msg = [0], open_rand = r \<rparr>"

definition opening_add :: "commit_opening \<Rightarrow> commit_opening \<Rightarrow> commit_opening" where
  "opening_add op1 op2 =
    \<lparr> open_msg = vec_add (open_msg op1) (open_msg op2),
      open_rand = vec_add (open_rand op1) (open_rand op2) \<rparr>"

definition opening_sub :: "commit_opening \<Rightarrow> commit_opening \<Rightarrow> commit_opening" where
  "opening_sub op1 op2 =
    \<lparr> open_msg = vec_sub (open_msg op1) (open_msg op2),
      open_rand = vec_sub (open_rand op1) (open_rand op2) \<rparr>"

definition aggregate_opening ::
  "commit_opening \<Rightarrow> commit_opening \<Rightarrow> commit_opening \<Rightarrow> commit_opening \<Rightarrow> commit_opening" where
  "aggregate_opening op_in1 op_in2 op_out1 op_out2 =
    opening_sub (opening_add op_in1 op_in2) (opening_add op_out1 op_out2)"

definition aggregate_randomness ::
  "commit_opening \<Rightarrow> commit_opening \<Rightarrow> commit_opening \<Rightarrow> commit_opening \<Rightarrow> int_vec" where
  "aggregate_randomness op_in1 op_in2 op_out1 op_out2 =
    open_rand (aggregate_opening op_in1 op_in2 op_out1 op_out2)"

definition balance_commitment ::
  "commitment \<Rightarrow> commitment \<Rightarrow> commitment \<Rightarrow> commitment \<Rightarrow> int \<Rightarrow> commitment" where
  "balance_commitment c_in1 c_in2 c_out1 c_out2 q =
    vec_mod (vec_sub (vec_add c_in1 c_in2) (vec_add c_out1 c_out2)) q"

definition public_amount_opening :: "commit_params \<Rightarrow> int \<Rightarrow> commit_opening" where
  "public_amount_opening p fee =
    \<lparr> open_msg = [fee], open_rand = replicate (cp_n2 p) 0 \<rparr>"

definition public_amount_commitment ::
  "commit_params \<Rightarrow> commit_key \<Rightarrow> int \<Rightarrow> commitment" where
  "public_amount_commitment p ck fee =
    commit ck (public_amount_opening p fee) (cp_q p)"

definition fee_balance_commitment ::
  "commit_params \<Rightarrow> commit_key \<Rightarrow> commitment \<Rightarrow> commitment \<Rightarrow>
   commitment \<Rightarrow> commitment \<Rightarrow> int \<Rightarrow> commitment" where
  "fee_balance_commitment p ck c_in1 c_in2 c_out1 c_out2 fee =
    vec_mod
      (vec_sub
        (balance_commitment c_in1 c_in2 c_out1 c_out2 (cp_q p))
        (public_amount_commitment p ck fee))
      (cp_q p)"

definition valid_balance_witness :: "commit_params \<Rightarrow> int_vec \<Rightarrow> bool" where
  "valid_balance_witness p r \<longleftrightarrow>
    valid_vec r (cp_n2 p) \<and> all_bounded r (4 * cp_beta p)"

definition valid_balance_mask :: "commit_params \<Rightarrow> int \<Rightarrow> int_vec \<Rightarrow> bool" where
  "valid_balance_mask p gamma y \<longleftrightarrow>
    valid_vec y (cp_n2 p) \<and> all_bounded y gamma"

definition balance_response_bound :: "commit_params \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int" where
  "balance_response_bound p gamma e = gamma + abs e * (4 * cp_beta p)"

definition valid_balance_challenge :: "commit_params \<Rightarrow> int \<Rightarrow> bool" where
  "valid_balance_challenge p e \<longleftrightarrow>
    valid_scalar_commit_params p \<and> (e = 0 \<or> e = 1)"

lemma valid_balance_challenge_binary:
  assumes "valid_balance_challenge p e"
  shows "e = 0 \<or> e = 1"
  using assms unfolding valid_balance_challenge_def by simp

lemma balance_response_bound_binary:
  assumes "valid_balance_challenge p e"
  shows "balance_response_bound p gamma e =
    (if e = 0 then gamma else gamma + 4 * cp_beta p)"
  using valid_balance_challenge_binary[OF assms]
  unfolding balance_response_bound_def
  by auto

definition valid_balance_response :: "commit_params \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int_vec \<Rightarrow> bool" where
  "valid_balance_response p gamma e z \<longleftrightarrow>
    valid_vec z (cp_n2 p) \<and> all_bounded z (balance_response_bound p gamma e)"

definition balance_relation ::
  "commit_params \<Rightarrow> commit_key \<Rightarrow> commitment \<Rightarrow> int_vec \<Rightarrow> bool" where
  "balance_relation p ck c r \<longleftrightarrow>
    valid_scalar_commit_params p \<and>
    valid_confidential_commit_key p ck \<and>
    valid_balance_witness p r \<and>
    rand_commit p ck r = c"

definition balance_relation_wellformed ::
  "commit_params \<Rightarrow> commit_key \<Rightarrow> commitment \<Rightarrow> int_vec \<Rightarrow> bool" where
  "balance_relation_wellformed p ck c r \<longleftrightarrow>
    valid_scalar_commit_params p \<and>
    valid_commit_key p ck \<and>
    valid_balance_witness p r \<and>
    rand_commit p ck r = c"

lemma balance_relation_imp_wellformed:
  assumes "balance_relation p ck c r"
  shows "balance_relation_wellformed p ck c r"
  using assms valid_confidential_commit_key_valid
  unfolding balance_relation_def balance_relation_wellformed_def
  by blast

definition balance_fs_rounds :: nat where
  "balance_fs_rounds = fixed_fs_rounds"

definition balance_fs_domain :: transcript_domain where
  "balance_fs_domain = 1001"

definition balance_fs_fields ::
  "commit_key \<Rightarrow> commitment \<Rightarrow> commitment list \<Rightarrow> int list" where
  "balance_fs_fields ck c as =
    [sum_list (concat ck), sum_list c, sum_list (concat as)]"

record balance_proof =
  balance_as :: "commitment list"
  balance_zs :: "int_vec list"

definition balance_sigma_commit ::
  "commit_params \<Rightarrow> commit_key \<Rightarrow> int_vec \<Rightarrow> commitment" where
  "balance_sigma_commit p ck y = rand_commit p ck y"

definition balance_sigma_respond ::
  "int_vec \<Rightarrow> int_vec \<Rightarrow> int \<Rightarrow> int_vec" where
  "balance_sigma_respond r y e = vec_add y (scalar_mult e r)"

definition canonical_balance_challenge ::
  "commit_params \<Rightarrow> commit_key \<Rightarrow> commitment \<Rightarrow> commitment \<Rightarrow> int" where
  "canonical_balance_challenge p ck c a =
    binary_fs_challenge balance_fs_domain (balance_fs_fields ck c [a]) 0"

definition balance_sigma_verify ::
  "commit_params \<Rightarrow> int \<Rightarrow> commit_key \<Rightarrow> commitment \<Rightarrow> commitment \<Rightarrow> int \<Rightarrow> int_vec \<Rightarrow> bool" where
  "balance_sigma_verify p gamma ck c a e z \<longleftrightarrow>
    valid_scalar_commit_params p \<and>
    valid_commit_key p ck \<and>
    valid_commitment p a \<and>
    valid_balance_challenge p e \<and>
    valid_balance_response p gamma e z \<and>
    rand_commit p ck z =
      vec_mod (vec_add a (scalar_mult e c)) (cp_q p)"

definition balance_sigma_verify_core ::
  "commit_params \<Rightarrow> int \<Rightarrow> commit_key \<Rightarrow> commitment \<Rightarrow> commitment \<Rightarrow> int \<Rightarrow> int_vec \<Rightarrow> bool" where
  "balance_sigma_verify_core p gamma ck c a e z \<longleftrightarrow>
    valid_commitment p a \<and>
    valid_balance_challenge p e \<and>
    valid_balance_response p gamma e z \<and>
    rand_commit p ck z =
      vec_mod (vec_add a (scalar_mult e c)) (cp_q p)"

definition balance_fs_challenges ::
  "commit_params \<Rightarrow> commit_key \<Rightarrow> commitment \<Rightarrow> commitment list \<Rightarrow> int list" where
  "balance_fs_challenges p ck c as =
    binary_fs_challenges balance_fs_domain (balance_fs_fields ck c as) balance_fs_rounds"

definition balance_sigma_responds ::
  "int_vec \<Rightarrow> int_vec list \<Rightarrow> int list \<Rightarrow> int_vec list" where
  "balance_sigma_responds r ys es =
    sigma_response_rounds balance_sigma_respond r ys es"

definition balance_fs_prove ::
  "commit_params \<Rightarrow> int \<Rightarrow> commit_key \<Rightarrow> commitment \<Rightarrow> int_vec \<Rightarrow> int_vec list \<Rightarrow> balance_proof option" where
  "balance_fs_prove p gamma ck c r ys = (
    let as = map (balance_sigma_commit p ck) ys in
    let es = balance_fs_challenges p ck c as in
    let zs = balance_sigma_responds r ys es in
    if balance_relation_wellformed p ck c r \<and>
       length ys = balance_fs_rounds \<and>
       (\<forall>i < balance_fs_rounds. valid_balance_mask p gamma (ys ! i)) \<and>
       (\<forall>i < balance_fs_rounds. valid_balance_response p gamma (es ! i) (zs ! i))
    then Some \<lparr> balance_as = as, balance_zs = zs \<rparr>
    else None)"

definition balance_fs_verify ::
  "commit_params \<Rightarrow> int \<Rightarrow> commit_key \<Rightarrow> commitment \<Rightarrow> balance_proof \<Rightarrow> bool" where
  "balance_fs_verify p gamma ck c proof \<longleftrightarrow>
    (let as = balance_as proof in
     let es = balance_fs_challenges p ck c as in
     let zs = balance_zs proof in
     valid_scalar_commit_params p \<and>
     valid_commit_key p ck \<and>
     length as = balance_fs_rounds \<and>
     length zs = balance_fs_rounds \<and>
     (\<forall>i < balance_fs_rounds. balance_sigma_verify_core p gamma ck c (as ! i) (es ! i) (zs ! i)))"

definition balance_scheduled_verify ::
  "commit_params \<Rightarrow> int \<Rightarrow> commit_key \<Rightarrow> commitment \<Rightarrow>
   commitment list \<Rightarrow> int list \<Rightarrow> int_vec list \<Rightarrow> bool" where
  "balance_scheduled_verify p gamma ck c as es zs \<longleftrightarrow>
    length as = balance_fs_rounds \<and>
    length es = balance_fs_rounds \<and>
    length zs = balance_fs_rounds \<and>
    (\<forall>i < balance_fs_rounds.
      balance_sigma_verify p gamma ck c (as ! i) (es ! i) (zs ! i))"

lemma balance_sigma_verify_imp_core:
  assumes "balance_sigma_verify p gamma ck c a e z"
  shows "balance_sigma_verify_core p gamma ck c a e z"
  using assms
  unfolding balance_sigma_verify_def balance_sigma_verify_core_def
  by auto

lemma all_bounded_mono:
  assumes "all_bounded v B" and "B \<le> C"
  shows "all_bounded v C"
  using assms unfolding all_bounded_def by auto

lemma vec_add_bounded:
  assumes "all_bounded v1 B1"
      and "all_bounded v2 B2"
      and "length v1 = length v2"
  shows "all_bounded (vec_add v1 v2) (B1 + B2)"
proof -
  show ?thesis
    unfolding all_bounded_alt
  proof (intro allI impI)
    fix i
    assume i_lt: "i < length (vec_add v1 v2)"
    have len_eq: "length (vec_add v1 v2) = length v1"
      using assms(3) by (simp add: vec_add_length)
    then have i_v1: "i < length v1"
      using i_lt by simp
    have i_v2: "i < length v2"
      using assms(3) i_v1 by simp
    have abs_v1: "abs (v1 ! i) \<le> B1"
      using all_bounded_nth[OF assms(1) i_v1] .
    have abs_v2: "abs (v2 ! i) \<le> B2"
      using all_bounded_nth[OF assms(2) i_v2] .
    have "abs ((vec_add v1 v2) ! i) = abs (v1 ! i + v2 ! i)"
      using i_v1 i_v2 by (simp add: vec_add_def)
    also have "... \<le> abs (v1 ! i) + abs (v2 ! i)"
      by (rule abs_triangle_ineq)
    also have "... \<le> B1 + B2"
      using abs_v1 abs_v2 by simp
    finally show "abs ((vec_add v1 v2) ! i) \<le> B1 + B2" .
  qed
qed

lemma inner_prod_vec_add_eq_len:
  assumes "length v1 = length v2"
  shows "inner_prod u (vec_add v1 v2) = inner_prod u v1 + inner_prod u v2"
proof -
  let ?n = "min (length u) (length v1)"
  have len_add: "length (vec_add v1 v2) = length v1"
    using assms by (simp add: vec_add_length)
  have "inner_prod u (vec_add v1 v2) =
        (\<Sum>i = 0 ..< min (length u) (length (vec_add v1 v2)). u ! i * (vec_add v1 v2) ! i)"
    by (simp add: inner_prod_nth_min)
  also have "... = (\<Sum>i = 0 ..< ?n. u ! i * (vec_add v1 v2) ! i)"
    using len_add by simp
  also have "... = (\<Sum>i = 0 ..< ?n. u ! i * (v1 ! i + v2 ! i))"
  proof (rule sum.cong, simp)
    fix i
    assume "i \<in> {0 ..< ?n}"
    then have i_v1: "i < length v1" and i_v2: "i < length v2"
      using assms by auto
    then show "u ! i * (vec_add v1 v2 ! i) = u ! i * (v1 ! i + v2 ! i)"
      by (simp add: vec_add_def)
  qed
  also have "... = (\<Sum>i = 0 ..< ?n. u ! i * v1 ! i + u ! i * v2 ! i)"
    by (simp add: algebra_simps)
  also have "... = (\<Sum>i = 0 ..< ?n. u ! i * v1 ! i) + (\<Sum>i = 0 ..< ?n. u ! i * v2 ! i)"
    by (simp add: sum.distrib)
  also have "... = inner_prod u v1 + inner_prod u v2"
    using assms by (simp add: inner_prod_nth_min)
  finally show ?thesis .
qed

lemma mat_vec_mult_add_nth:
  assumes "i < length A"
      and "length z1 = length z2"
  shows "(mat_vec_mult A (vec_add z1 z2)) ! i =
         (mat_vec_mult A z1) ! i + (mat_vec_mult A z2) ! i"
proof -
  have "(mat_vec_mult A (vec_add z1 z2)) ! i = inner_prod (A ! i) (vec_add z1 z2)"
    using assms(1) by (simp add: mat_vec_mult_nth)
  also have "... = inner_prod (A ! i) z1 + inner_prod (A ! i) z2"
    using inner_prod_vec_add_eq_len[OF assms(2)] by simp
  also have "... = (mat_vec_mult A z1) ! i + (mat_vec_mult A z2) ! i"
    using assms(1) by (simp add: mat_vec_mult_nth)
  finally show ?thesis .
qed

lemma mat_vec_mult_add_eq:
  assumes "length z1 = length z2"
  shows "mat_vec_mult A (vec_add z1 z2) = vec_add (mat_vec_mult A z1) (mat_vec_mult A z2)"
proof (intro nth_equalityI)
  show "length (mat_vec_mult A (vec_add z1 z2)) =
        length (vec_add (mat_vec_mult A z1) (mat_vec_mult A z2))"
    by (simp add: vec_add_length mat_vec_mult_length)
next
  fix i
  assume i_lt: "i < length (mat_vec_mult A (vec_add z1 z2))"
  then have i_A: "i < length A"
    by (simp add: mat_vec_mult_length)
  show "mat_vec_mult A (vec_add z1 z2) ! i =
        vec_add (mat_vec_mult A z1) (mat_vec_mult A z2) ! i"
    using mat_vec_mult_add_nth[OF i_A assms] i_A
    by (simp add: vec_add_def mat_vec_mult_length)
qed

lemma mat_vec_mult_sub_eq:
  assumes "length z1 = length z2"
  shows "mat_vec_mult A (vec_sub z1 z2) = vec_sub (mat_vec_mult A z1) (mat_vec_mult A z2)"
proof (intro nth_equalityI)
  show "length (mat_vec_mult A (vec_sub z1 z2)) =
        length (vec_sub (mat_vec_mult A z1) (mat_vec_mult A z2))"
    by (simp add: vec_sub_length mat_vec_mult_length)
next
  fix i
  assume i_lt: "i < length (mat_vec_mult A (vec_sub z1 z2))"
  then have i_A: "i < length A"
    by (simp add: mat_vec_mult_length)
  show "mat_vec_mult A (vec_sub z1 z2) ! i =
        vec_sub (mat_vec_mult A z1) (mat_vec_mult A z2) ! i"
    using mat_vec_mult_sub_nth[OF i_A assms] i_A
    by (simp add: vec_sub_def mat_vec_mult_length)
qed

lemma vec_mod_add_eq:
  assumes "length v = length w" and "q > 0"
  shows "vec_mod (vec_add v w) q = vec_mod (vec_add (vec_mod v q) (vec_mod w q)) q"
proof (intro nth_equalityI)
  show "length (vec_mod (vec_add v w) q) =
        length (vec_mod (vec_add (vec_mod v q) (vec_mod w q)) q)"
    using assms by (simp add: vec_add_length vec_mod_length)
next
  fix i
  assume i_lt: "i < length (vec_mod (vec_add v w) q)"
  have len_add: "length (vec_add v w) = length v"
    using assms(1) by (simp add: vec_add_length)
  then have i_v: "i < length v"
    using i_lt by (simp add: vec_mod_length)
  have i_w: "i < length w"
    using assms(1) i_v by simp
  have i_rhs:
    "i < length (vec_add (vec_mod v q) (vec_mod w q))"
    using i_v i_w by (simp add: vec_add_length vec_mod_length)
  show "vec_mod (vec_add v w) q ! i =
        vec_mod (vec_add (vec_mod v q) (vec_mod w q)) q ! i"
  proof -
    have lhs: "vec_mod (vec_add v w) q ! i = (v ! i + w ! i) mod q"
      using i_lt i_v i_w by (simp add: vec_add_def vec_mod_nth)
    have rhs:
      "vec_mod (vec_add (vec_mod v q) (vec_mod w q)) q ! i =
        ((v ! i mod q) + (w ! i mod q)) mod q"
      using i_rhs i_v i_w by (simp add: vec_add_def vec_mod_nth)
    from lhs rhs show ?thesis
      using assms(2) by (simp add: mod_add_eq)
  qed
qed

lemma vec_mod_sub_eq:
  assumes "length v = length w" and "q > 0"
  shows "vec_mod (vec_sub v w) q = vec_mod (vec_sub (vec_mod v q) (vec_mod w q)) q"
proof (intro nth_equalityI)
  show "length (vec_mod (vec_sub v w) q) =
        length (vec_mod (vec_sub (vec_mod v q) (vec_mod w q)) q)"
    using assms by (simp add: vec_sub_length vec_mod_length)
next
  fix i
  assume i_lt: "i < length (vec_mod (vec_sub v w) q)"
  have len_sub: "length (vec_sub v w) = length v"
    using assms(1) by (simp add: vec_sub_length)
  then have i_v: "i < length v"
    using i_lt by (simp add: vec_mod_length)
  have i_w: "i < length w"
    using assms(1) i_v by simp
  have i_rhs:
    "i < length (vec_sub (vec_mod v q) (vec_mod w q))"
    using i_v i_w by (simp add: vec_sub_length vec_mod_length)
  show "vec_mod (vec_sub v w) q ! i =
        vec_mod (vec_sub (vec_mod v q) (vec_mod w q)) q ! i"
  proof -
    have lhs: "vec_mod (vec_sub v w) q ! i = (v ! i - w ! i) mod q"
      using i_lt i_v i_w by (simp add: vec_sub_def vec_mod_nth)
    have rhs:
      "vec_mod (vec_sub (vec_mod v q) (vec_mod w q)) q ! i =
        ((v ! i mod q) - (w ! i mod q)) mod q"
      using i_rhs i_v i_w by (simp add: vec_sub_def vec_mod_nth)
    from lhs rhs show ?thesis
      using assms(2) by (simp add: mod_diff_eq)
  qed
qed

lemma vec_mod_sub_add_cancel_left:
  assumes len_eq: "length a = length c"
      and q_pos: "q > 0"
      and c_canonical: "vec_mod c q = c"
  shows "vec_mod (vec_sub (vec_mod (vec_add a c) q) (vec_mod a q)) q = c"
proof (intro nth_equalityI)
  show "length (vec_mod (vec_sub (vec_mod (vec_add a c) q) (vec_mod a q)) q) =
        length c"
    using len_eq by (simp add: vec_add_length vec_sub_length vec_mod_length)
next
  fix i
  assume i_lt: "i < length (vec_mod (vec_sub (vec_mod (vec_add a c) q) (vec_mod a q)) q)"
  have i_a: "i < length a"
    using i_lt len_eq by (simp add: vec_add_length vec_sub_length vec_mod_length)
  have i_c: "i < length c"
    using i_a len_eq by simp
  have c_i_mod: "c ! i mod q = c ! i"
  proof -
    have "(vec_mod c q) ! i = c ! i"
      using c_canonical by simp
    then show ?thesis
      using i_c by (simp add: vec_mod_nth)
  qed
  have mod_cancel:
    "((a ! i + c ! i) mod q - a ! i mod q) mod q = c ! i"
  proof -
    have "((a ! i + c ! i) mod q - a ! i mod q) mod q =
          ((a ! i + c ! i) - a ! i) mod q"
      by (rule mod_diff_eq)
    also have "... = c ! i"
      using c_i_mod by simp
    finally show ?thesis .
  qed
  have nth_eq:
    "vec_mod (vec_sub (vec_mod (vec_add a c) q) (vec_mod a q)) q ! i =
      ((a ! i + c ! i) mod q - a ! i mod q) mod q"
    using i_a i_c
    by (simp add: vec_add_def vec_sub_def vec_mod_def)
  show "vec_mod (vec_sub (vec_mod (vec_add a c) q) (vec_mod a q)) q ! i = c ! i"
    using nth_eq mod_cancel by simp
qed

lemma vec_mod_sub_add_cancel_right:
  assumes len_eq: "length v = length w"
      and q_pos: "q > 0"
      and v_canonical: "vec_mod v q = v"
  shows "vec_mod (vec_add (vec_mod (vec_sub v w) q) w) q = v"
proof (intro nth_equalityI)
  show "length (vec_mod (vec_add (vec_mod (vec_sub v w) q) w) q) = length v"
    using len_eq by (simp add: vec_sub_length vec_add_length vec_mod_length)
next
  fix i
  assume i_lt: "i < length (vec_mod (vec_add (vec_mod (vec_sub v w) q) w) q)"
  have i_v: "i < length v"
    using i_lt len_eq by (simp add: vec_sub_length vec_add_length vec_mod_length)
  have i_w: "i < length w"
    using i_v len_eq by simp
  have v_i_mod: "v ! i mod q = v ! i"
  proof -
    have "(vec_mod v q) ! i = v ! i"
      using v_canonical by simp
    then show ?thesis
      using i_v by (simp add: vec_mod_nth)
  qed
  have mod_cancel:
    "((v ! i - w ! i) mod q + w ! i) mod q = v ! i"
  proof -
    have "((v ! i - w ! i) mod q + w ! i) mod q =
          ((v ! i - w ! i) + w ! i) mod q"
      by (simp add: mod_add_left_eq)
    also have "... = v ! i"
      using v_i_mod by simp
    finally show ?thesis .
  qed
  have nth_eq:
    "vec_mod (vec_add (vec_mod (vec_sub v w) q) w) q ! i =
      ((v ! i - w ! i) mod q + w ! i) mod q"
    using i_v i_w
    by (simp add: vec_add_def vec_sub_def vec_mod_def)
  show "vec_mod (vec_add (vec_mod (vec_sub v w) q) w) q ! i = v ! i"
    using nth_eq mod_cancel by simp
qed

lemma scalar_mult_bounded:
  assumes "all_bounded v B"
  shows "all_bounded (scalar_mult c v) (abs c * B)"
  unfolding all_bounded_alt
proof (intro allI impI)
  fix i
  assume i_lt: "i < length (scalar_mult c v)"
  then have i_v: "i < length v"
    by (simp add: scalar_mult_length)
  have "abs ((scalar_mult c v) ! i) = abs (c * (v ! i))"
    using i_v by (simp add: scalar_mult_def)
  also have "... = abs c * abs (v ! i)"
    by (simp add: abs_mult)
  also have "... \<le> abs c * B"
    using all_bounded_nth[OF assms i_v]
    by (simp add: mult_left_mono)
  finally show "abs (scalar_mult c v ! i) \<le> abs c * B" .
qed

lemma inner_prod_scalar_right:
  "inner_prod u (scalar_mult c v) = c * inner_prod u v"
proof -
  let ?n = "min (length u) (length v)"
  have "inner_prod u (scalar_mult c v) =
        (\<Sum>i = 0 ..< ?n. u ! i * (scalar_mult c v) ! i)"
    by (simp add: inner_prod_nth_min scalar_mult_length)
  also have "... = (\<Sum>i = 0 ..< ?n. u ! i * (c * (v ! i)))"
    by (intro sum.cong refl) (simp add: scalar_mult_def)
  also have "... = (\<Sum>i = 0 ..< ?n. c * (u ! i * v ! i))"
    by (simp add: algebra_simps)
  also have "... = c * inner_prod u v"
    by (simp add: inner_prod_nth_min sum_distrib_left algebra_simps)
  finally show ?thesis .
qed

lemma mat_vec_mult_scalar_eq:
  "mat_vec_mult A (scalar_mult c v) = scalar_mult c (mat_vec_mult A v)"
proof (intro nth_equalityI)
  show "length (mat_vec_mult A (scalar_mult c v)) =
        length (scalar_mult c (mat_vec_mult A v))"
    by (simp add: mat_vec_mult_length scalar_mult_length)
next
  fix i
  assume i_lt: "i < length (mat_vec_mult A (scalar_mult c v))"
  then have i_A: "i < length A"
    by (simp add: mat_vec_mult_length)
  show "mat_vec_mult A (scalar_mult c v) ! i =
        scalar_mult c (mat_vec_mult A v) ! i"
  proof -
    have "mat_vec_mult A (scalar_mult c v) ! i =
          inner_prod (A ! i) (scalar_mult c v)"
      using i_A by (simp add: mat_vec_mult_nth)
    also have "... = c * inner_prod (A ! i) v"
      by (rule inner_prod_scalar_right)
    also have "... = c * (mat_vec_mult A v ! i)"
      using i_A by (simp add: mat_vec_mult_nth)
    also have "... = scalar_mult c (mat_vec_mult A v) ! i"
      using i_A by (simp add: scalar_mult_def mat_vec_mult_length)
    finally show ?thesis .
  qed
qed

lemma vec_mod_scalar_eq:
  assumes "q > 0"
  shows "vec_mod (scalar_mult c v) q = vec_mod (scalar_mult c (vec_mod v q)) q"
proof (intro nth_equalityI)
  show "length (vec_mod (scalar_mult c v) q) =
        length (vec_mod (scalar_mult c (vec_mod v q)) q)"
    by (simp add: vec_mod_length scalar_mult_length)
next
  fix i
  assume i_lt: "i < length (vec_mod (scalar_mult c v) q)"
  then have i_v: "i < length v"
    by (simp add: vec_mod_length scalar_mult_length)
  show "vec_mod (scalar_mult c v) q ! i =
        vec_mod (scalar_mult c (vec_mod v q)) q ! i"
  proof -
    have lhs: "vec_mod (scalar_mult c v) q ! i = (c * v ! i) mod q"
      using i_v by (simp add: vec_mod_nth scalar_mult_def)
    have rhs:
      "vec_mod (scalar_mult c (vec_mod v q)) q ! i =
        (c * (v ! i mod q)) mod q"
    proof -
      have i_mod_v: "i < length (vec_mod v q)"
        using i_v by (simp add: vec_mod_length)
      show ?thesis
        using i_v i_mod_v by (simp add: vec_mod_nth scalar_mult_def)
    qed
    show ?thesis
      using lhs rhs assms by (simp add: mod_mult_right_eq)
  qed
qed

lemma scalar_mult_one:
  "scalar_mult 1 v = v"
  unfolding scalar_mult_def
  by (induction v) simp_all

lemma vec_add_scalar_zero_right:
  assumes len_eq: "length a = length c"
  shows "vec_add a (scalar_mult 0 c) = a"
  using len_eq
  unfolding vec_add_def scalar_mult_def
  by (induction a c rule: list_induct2) simp_all

lemma canonical_balance_challenge_valid:
  assumes "valid_scalar_commit_params p"
  shows "valid_balance_challenge p (canonical_balance_challenge p ck c a)"
proof -
  have bit:
    "canonical_balance_challenge p ck c a = 0 \<or>
     canonical_balance_challenge p ck c a = 1"
    unfolding canonical_balance_challenge_def
    by (rule binary_fs_challenge_bit)
  show ?thesis
    using assms bit
    unfolding valid_balance_challenge_def canonical_balance_challenge_def
    by auto
qed

lemma balance_fs_challenges_length:
  "length (balance_fs_challenges p ck c as) = balance_fs_rounds"
  unfolding balance_fs_challenges_def
  by simp

lemma balance_fs_challenge_valid:
  assumes "valid_scalar_commit_params p"
      and "i < balance_fs_rounds"
  shows "valid_balance_challenge p ((balance_fs_challenges p ck c as) ! i)"
proof -
  have bit:
    "(balance_fs_challenges p ck c as) ! i = 0 \<or>
     (balance_fs_challenges p ck c as) ! i = 1"
    using assms(2)
    unfolding balance_fs_challenges_def
    by (rule binary_fs_challenges_bit)
  show ?thesis
    using assms(1) bit
    unfolding valid_balance_challenge_def
    by auto
qed

lemma balance_sigma_responds_length:
  assumes "length ys = length es"
  shows "length (balance_sigma_responds r ys es) = length ys"
  using assms
  unfolding balance_sigma_responds_def
  by (rule sigma_response_rounds_length)

lemma balance_sigma_responds_nth:
  assumes "length ys = length es"
      and "i < length ys"
  shows "(balance_sigma_responds r ys es) ! i = balance_sigma_respond r (ys ! i) (es ! i)"
  using assms
  unfolding balance_sigma_responds_def
  by (rule sigma_response_rounds_nth)

lemma vec_add_append_eq:
  assumes "length xs = length xs'"
  shows "vec_add (xs @ ys) (xs' @ ys') = vec_add xs xs' @ vec_add ys ys'"
  using assms unfolding vec_add_def by simp

lemma vec_sub_append_eq:
  assumes "length xs = length xs'"
  shows "vec_sub (xs @ ys) (xs' @ ys') = vec_sub xs xs' @ vec_sub ys ys'"
  using assms unfolding vec_sub_def by simp

lemma rand_commit_valid:
  assumes params_ok: "valid_commit_params p"
      and key_ok: "valid_commit_key p ck"
      and r_ok: "valid_vec r (cp_n2 p)"
  shows "valid_commitment p (rand_commit p ck r)"
proof -
  have q_pos: "cp_q p > 0"
    using valid_commit_params_pos[OF params_ok] by simp
  have len_rows: "length (rand_commit p ck r) = cp_m p"
    unfolding rand_commit_def
    using rand_commit_key_dims[OF key_ok]
          valid_vec_length[OF r_ok]
    by (simp add: vec_mod_length mat_vec_mult_length)
  show ?thesis
    unfolding valid_commitment_def valid_vec_def
    using len_rows by simp
qed

lemma rand_commit_add_hom:
  assumes key_ok: "valid_commit_key p ck"
      and len_r1: "length r1 = cp_n2 p"
      and len_r2: "length r2 = cp_n2 p"
      and q_pos: "cp_q p > 0"
  shows "rand_commit p ck (vec_add r1 r2) =
    vec_mod (vec_add (rand_commit p ck r1) (rand_commit p ck r2)) (cp_q p)"
proof -
  have raw:
    "mat_vec_mult (rand_commit_key p ck) (vec_add r1 r2) =
      vec_add (mat_vec_mult (rand_commit_key p ck) r1)
              (mat_vec_mult (rand_commit_key p ck) r2)"
    using len_r1 len_r2
    by (simp add: mat_vec_mult_add_eq)
  have len_eq:
    "length (mat_vec_mult (rand_commit_key p ck) r1) =
     length (mat_vec_mult (rand_commit_key p ck) r2)"
    by (simp add: mat_vec_mult_length)
  show ?thesis
    unfolding rand_commit_def
    using raw len_eq q_pos
    by (simp add: vec_mod_add_eq)
qed

lemma rand_commit_sub_hom:
  assumes key_ok: "valid_commit_key p ck"
      and len_r1: "length r1 = cp_n2 p"
      and len_r2: "length r2 = cp_n2 p"
      and q_pos: "cp_q p > 0"
  shows "rand_commit p ck (vec_sub r1 r2) =
    vec_mod (vec_sub (rand_commit p ck r1) (rand_commit p ck r2)) (cp_q p)"
proof -
  have raw:
    "mat_vec_mult (rand_commit_key p ck) (vec_sub r1 r2) =
      vec_sub (mat_vec_mult (rand_commit_key p ck) r1)
              (mat_vec_mult (rand_commit_key p ck) r2)"
    using len_r1 len_r2
    by (simp add: mat_vec_mult_sub_eq)
  have len_eq:
    "length (mat_vec_mult (rand_commit_key p ck) r1) =
     length (mat_vec_mult (rand_commit_key p ck) r2)"
    by (simp add: mat_vec_mult_length)
  show ?thesis
    unfolding rand_commit_def
    using raw len_eq q_pos
    by (simp add: vec_mod_sub_eq)
qed

lemma rand_commit_scalar_hom:
  assumes key_ok: "valid_commit_key p ck"
      and len_r: "length r = cp_n2 p"
      and q_pos: "cp_q p > 0"
  shows "rand_commit p ck (scalar_mult e r) =
    vec_mod (scalar_mult e (rand_commit p ck r)) (cp_q p)"
proof -
  have raw:
    "mat_vec_mult (rand_commit_key p ck) (scalar_mult e r) =
      scalar_mult e (mat_vec_mult (rand_commit_key p ck) r)"
    by (simp add: mat_vec_mult_scalar_eq)
  have "rand_commit p ck (scalar_mult e r) =
        vec_mod (scalar_mult e (mat_vec_mult (rand_commit_key p ck) r)) (cp_q p)"
    unfolding rand_commit_def using raw by simp
  also have "... = vec_mod (scalar_mult e (rand_commit p ck r)) (cp_q p)"
    using vec_mod_scalar_eq[OF q_pos, of e "mat_vec_mult (rand_commit_key p ck) r"]
    unfolding rand_commit_def by simp
  finally show ?thesis .
qed

definition balance_sigma_extract ::
  "int \<Rightarrow> int_vec \<Rightarrow> int \<Rightarrow> int_vec \<Rightarrow> int_vec option" where
  "balance_sigma_extract e1 z1 e2 z2 =
    (if e1 = 1 \<and> e2 = 0 then Some (vec_sub z1 z2)
     else if e1 = 0 \<and> e2 = 1 then Some (vec_sub z2 z1)
     else None)"

definition balance_scheduled_fork_extract ::
  "int list \<Rightarrow> int_vec list \<Rightarrow> int list \<Rightarrow> int_vec list \<Rightarrow> nat \<Rightarrow>
   int_vec option" where
  "balance_scheduled_fork_extract es1 zs1 es2 zs2 i =
    balance_sigma_extract (es1 ! i) (zs1 ! i) (es2 ! i) (zs2 ! i)"

definition balance_sigma_sim_commit ::
  "commit_params \<Rightarrow> commit_key \<Rightarrow> commitment \<Rightarrow> int \<Rightarrow> int_vec \<Rightarrow> commitment" where
  "balance_sigma_sim_commit p ck c e z =
    vec_mod (vec_sub (rand_commit p ck z) (scalar_mult e c)) (cp_q p)"

lemma balance_sigma_sim_commit_valid:
  assumes params_ok: "valid_scalar_commit_params p"
      and key_ok: "valid_commit_key p ck"
      and c_valid: "valid_commitment p c"
      and z_vec: "valid_vec z (cp_n2 p)"
  shows "valid_commitment p (balance_sigma_sim_commit p ck c e z)"
proof -
  have rc_valid: "valid_commitment p (rand_commit p ck z)"
    using rand_commit_valid[OF valid_scalar_commit_params_props(1)[OF params_ok] key_ok z_vec] .
  have len_rc: "length (rand_commit p ck z) = cp_m p"
    using rc_valid unfolding valid_commitment_def valid_vec_def by simp
  have len_c: "length c = cp_m p"
    using c_valid unfolding valid_commitment_def valid_vec_def by simp
  show ?thesis
    unfolding balance_sigma_sim_commit_def valid_commitment_def valid_vec_def
    using len_rc len_c by (simp add: vec_sub_length scalar_mult_length vec_mod_length)
qed

lemma balance_sigma_sim_commit_equation:
  assumes params_ok: "valid_scalar_commit_params p"
      and key_ok: "valid_commit_key p ck"
      and c_valid: "valid_commitment p c"
      and z_vec: "valid_vec z (cp_n2 p)"
  shows "rand_commit p ck z =
    vec_mod (vec_add (balance_sigma_sim_commit p ck c e z)
             (scalar_mult e c)) (cp_q p)"
proof -
  have rc_valid: "valid_commitment p (rand_commit p ck z)"
    using rand_commit_valid[OF valid_scalar_commit_params_props(1)[OF params_ok] key_ok z_vec] .
  have len_rc: "length (rand_commit p ck z) = cp_m p"
    using rc_valid unfolding valid_commitment_def valid_vec_def by simp
  have len_c: "length c = cp_m p"
    using c_valid unfolding valid_commitment_def valid_vec_def by simp
  have len_eq: "length (rand_commit p ck z) = length (scalar_mult e c)"
    using len_rc len_c by (simp add: scalar_mult_length)
  have q_pos: "cp_q p > 0"
    using valid_scalar_commit_params_props(5)[OF params_ok] by linarith
  have rc_canonical: "vec_mod (rand_commit p ck z) (cp_q p) = rand_commit p ck z"
    unfolding rand_commit_def
    using q_pos by (simp add: vec_mod_idemp)
  show ?thesis
    unfolding balance_sigma_sim_commit_def
    using vec_mod_sub_add_cancel_right[OF len_eq q_pos rc_canonical] by simp
qed

lemma balance_sigma_simulate_verify:
  assumes params_ok: "valid_scalar_commit_params p"
      and key_ok: "valid_commit_key p ck"
      and c_valid: "valid_commitment p c"
      and challenge_ok: "valid_balance_challenge p e"
      and z_ok: "valid_balance_response p gamma e z"
      and a_def: "a = balance_sigma_sim_commit p ck c e z"
  shows "balance_sigma_verify p gamma ck c a e z"
proof -
  have z_vec: "valid_vec z (cp_n2 p)"
    using z_ok unfolding valid_balance_response_def by simp
  have a_valid: "valid_commitment p a"
    using balance_sigma_sim_commit_valid[OF params_ok key_ok c_valid z_vec] a_def by simp
  have sim_eq:
    "rand_commit p ck z = vec_mod (vec_add a (scalar_mult e c)) (cp_q p)"
    using balance_sigma_sim_commit_equation[OF params_ok key_ok c_valid z_vec] a_def by simp
  show ?thesis
    unfolding balance_sigma_verify_def
    using params_ok key_ok a_valid challenge_ok z_ok sim_eq
    by simp
qed

lemma balance_sigma_extract_some_if_distinct_binary:
  assumes e1_ok: "valid_balance_challenge p e1"
      and e2_ok: "valid_balance_challenge p e2"
      and distinct: "e1 \<noteq> e2"
  shows "\<exists>r. balance_sigma_extract e1 z1 e2 z2 = Some r"
  using valid_balance_challenge_binary[OF e1_ok]
        valid_balance_challenge_binary[OF e2_ok]
        distinct
  unfolding balance_sigma_extract_def
  by auto

lemma balance_sigma_extract_response_bound:
  assumes z1_ok: "valid_balance_response p gamma e1 z1"
      and z2_ok: "valid_balance_response p gamma e2 z2"
      and ext: "balance_sigma_extract e1 z1 e2 z2 = Some r"
  shows "valid_vec r (cp_n2 p) \<and>
         all_bounded r (balance_response_bound p gamma e1 +
                        balance_response_bound p gamma e2)"
proof -
  have len1: "length z1 = cp_n2 p"
    using z1_ok unfolding valid_balance_response_def valid_vec_def by simp
  have len2: "length z2 = cp_n2 p"
    using z2_ok unfolding valid_balance_response_def valid_vec_def by simp
  have b1: "all_bounded z1 (balance_response_bound p gamma e1)"
    using z1_ok unfolding valid_balance_response_def by simp
  have b2: "all_bounded z2 (balance_response_bound p gamma e2)"
    using z2_ok unfolding valid_balance_response_def by simp
  show ?thesis
  proof (cases "e1 = 1 \<and> e2 = 0")
    case True
    then have r_eq: "r = vec_sub z1 z2"
      using ext unfolding balance_sigma_extract_def by simp
    have len_r: "length r = cp_n2 p"
      using r_eq len1 len2 by (simp add: vec_sub_length)
    have bound_r:
      "all_bounded r (balance_response_bound p gamma e1 +
                      balance_response_bound p gamma e2)"
      using vec_sub_bounded[OF b1 b2] r_eq by simp
    show ?thesis
      using len_r bound_r unfolding valid_vec_def by simp
  next
    case False
    then have alt: "e1 = 0 \<and> e2 = 1"
      using ext unfolding balance_sigma_extract_def by (auto split: if_splits)
    then have r_eq: "r = vec_sub z2 z1"
      using ext False unfolding balance_sigma_extract_def by simp
    have len_r: "length r = cp_n2 p"
      using r_eq len1 len2 by (simp add: vec_sub_length)
    have bound_r:
      "all_bounded r (balance_response_bound p gamma e1 +
                      balance_response_bound p gamma e2)"
    proof -
      have raw_bound:
        "all_bounded r (balance_response_bound p gamma e2 +
                        balance_response_bound p gamma e1)"
        using vec_sub_bounded[OF b2 b1] r_eq by simp
      have sum_comm:
        "balance_response_bound p gamma e2 + balance_response_bound p gamma e1 =
         balance_response_bound p gamma e1 + balance_response_bound p gamma e2"
        by simp
      show ?thesis
        using raw_bound sum_comm by simp
    qed
    show ?thesis
      using len_r bound_r unfolding valid_vec_def by simp
  qed
qed

lemma balance_sigma_extract_distinct_binary_bound:
  assumes e1_ok: "valid_balance_challenge p e1"
      and e2_ok: "valid_balance_challenge p e2"
      and distinct: "e1 \<noteq> e2"
      and z1_ok: "valid_balance_response p gamma e1 z1"
      and z2_ok: "valid_balance_response p gamma e2 z2"
      and ext: "balance_sigma_extract e1 z1 e2 z2 = Some r"
  shows "valid_vec r (cp_n2 p) \<and> all_bounded r (2 * gamma + 4 * cp_beta p)"
proof -
  have extracted:
    "valid_vec r (cp_n2 p) \<and>
     all_bounded r (balance_response_bound p gamma e1 +
                    balance_response_bound p gamma e2)"
    using balance_sigma_extract_response_bound[OF z1_ok z2_ok ext] .
  have "balance_response_bound p gamma e1 +
        balance_response_bound p gamma e2 = 2 * gamma + 4 * cp_beta p"
    using valid_balance_challenge_binary[OF e1_ok]
          valid_balance_challenge_binary[OF e2_ok]
          distinct
    unfolding balance_response_bound_def
    by auto
  then show ?thesis
    using extracted by simp
qed

lemma balance_sigma_extract_sub_opening:
  assumes key_ok: "valid_commit_key p ck"
      and q_pos: "cp_q p > 0"
      and len_z_hi: "length z_hi = cp_n2 p"
      and len_z_lo: "length z_lo = cp_n2 p"
      and hi_eq: "rand_commit p ck z_hi = vec_mod (vec_add a c) (cp_q p)"
      and lo_eq: "rand_commit p ck z_lo = vec_mod a (cp_q p)"
      and len_a: "length a = length c"
      and c_canonical: "vec_mod c (cp_q p) = c"
  shows "rand_commit p ck (vec_sub z_hi z_lo) = c"
proof -
  have "rand_commit p ck (vec_sub z_hi z_lo) =
        vec_mod (vec_sub (rand_commit p ck z_hi) (rand_commit p ck z_lo)) (cp_q p)"
    using rand_commit_sub_hom[OF key_ok len_z_hi len_z_lo q_pos] .
  also have "... =
        vec_mod (vec_sub (vec_mod (vec_add a c) (cp_q p)) (vec_mod a (cp_q p))) (cp_q p)"
    using hi_eq lo_eq by simp
  also have "... = c"
    using vec_mod_sub_add_cancel_left[OF len_a q_pos c_canonical] .
  finally show ?thesis .
qed

lemma balance_sigma_extract_algebraic_opening:
  assumes t1: "balance_sigma_verify p gamma ck c a e1 z1"
      and t2: "balance_sigma_verify p gamma ck c a e2 z2"
      and c_valid: "valid_commitment p c"
      and c_canonical: "vec_mod c (cp_q p) = c"
      and ext: "balance_sigma_extract e1 z1 e2 z2 = Some r"
  shows "rand_commit p ck r = c"
proof -
  have params_ok: "valid_scalar_commit_params p"
    using t1 unfolding balance_sigma_verify_def by simp
  have key_ok: "valid_commit_key p ck"
    using t1 unfolding balance_sigma_verify_def by simp
  have a_valid: "valid_commitment p a"
    using t1 unfolding balance_sigma_verify_def by simp
  have e1_ok: "valid_balance_challenge p e1"
    using t1 unfolding balance_sigma_verify_def by simp
  have z1_ok: "valid_balance_response p gamma e1 z1"
    using t1 unfolding balance_sigma_verify_def by simp
  have eq1:
    "rand_commit p ck z1 =
      vec_mod (vec_add a (scalar_mult e1 c)) (cp_q p)"
    using t1 unfolding balance_sigma_verify_def by simp
  have e2_ok: "valid_balance_challenge p e2"
    using t2 unfolding balance_sigma_verify_def by simp
  have z2_ok: "valid_balance_response p gamma e2 z2"
    using t2 unfolding balance_sigma_verify_def by simp
  have eq2:
    "rand_commit p ck z2 =
      vec_mod (vec_add a (scalar_mult e2 c)) (cp_q p)"
    using t2 unfolding balance_sigma_verify_def by simp
  have q_pos: "cp_q p > 0"
    using valid_scalar_commit_params_props(5)[OF params_ok] by linarith
  have len_z1: "length z1 = cp_n2 p"
    using z1_ok unfolding valid_balance_response_def valid_vec_def by simp
  have len_z2: "length z2 = cp_n2 p"
    using z2_ok unfolding valid_balance_response_def valid_vec_def by simp
  have len_a: "length a = cp_m p"
    using a_valid unfolding valid_commitment_def valid_vec_def by simp
  have len_c: "length c = cp_m p"
    using c_valid unfolding valid_commitment_def valid_vec_def by simp
  have len_a_c: "length a = length c"
    using len_a len_c by simp
  show ?thesis
    using ext
  proof (cases "e1 = 1 \<and> e2 = 0")
    case True
    then have e_vals: "e1 = 1" "e2 = 0"
      by auto
    have r_eq: "r = vec_sub z1 z2"
      using ext True unfolding balance_sigma_extract_def by simp
    have hi_eq: "rand_commit p ck z1 = vec_mod (vec_add a c) (cp_q p)"
      using eq1 e_vals len_a_c by (simp add: scalar_mult_one)
    have lo_eq: "rand_commit p ck z2 = vec_mod a (cp_q p)"
      using eq2 e_vals len_a_c by (simp add: vec_add_scalar_zero_right)
    show ?thesis
      using balance_sigma_extract_sub_opening[
        OF key_ok q_pos len_z1 len_z2 hi_eq lo_eq len_a_c c_canonical]
      by (simp add: r_eq)
  next
    case False
    have alt: "e1 = 0 \<and> e2 = 1"
      using ext False unfolding balance_sigma_extract_def by (auto split: if_splits)
    then have e_vals: "e1 = 0" "e2 = 1"
      by auto
    have r_eq: "r = vec_sub z2 z1"
      using ext False alt unfolding balance_sigma_extract_def by simp
    have hi_eq: "rand_commit p ck z2 = vec_mod (vec_add a c) (cp_q p)"
      using eq2 e_vals len_a_c by (simp add: scalar_mult_one)
    have lo_eq: "rand_commit p ck z1 = vec_mod a (cp_q p)"
      using eq1 e_vals len_a_c by (simp add: vec_add_scalar_zero_right)
    show ?thesis
      using balance_sigma_extract_sub_opening[
        OF key_ok q_pos len_z2 len_z1 hi_eq lo_eq len_a_c c_canonical]
      by (simp add: r_eq)
  qed
qed

lemma balance_scheduled_fork_extract_algebraic_opening:
  assumes left: "balance_scheduled_verify p gamma ck c as es1 zs1"
      and right: "balance_scheduled_verify p gamma ck c as es2 zs2"
      and fork: "forked_binary_challenge_schedules balance_fs_rounds es1 es2 i"
      and c_valid: "valid_commitment p c"
      and c_canonical: "vec_mod c (cp_q p) = c"
  obtains r where
    "balance_scheduled_fork_extract es1 zs1 es2 zs2 i = Some r"
    "rand_commit p ck r = c"
    "valid_vec r (cp_n2 p)"
    "all_bounded r (2 * gamma + 4 * cp_beta p)"
proof -
  have i_lt: "i < balance_fs_rounds"
    using fork by (rule forked_binary_challenge_schedules_index(1))
  have distinct: "es1 ! i \<noteq> es2 ! i"
    using fork by (rule forked_binary_challenge_schedules_index(2))
  have t1:
    "balance_sigma_verify p gamma ck c (as ! i) (es1 ! i) (zs1 ! i)"
    using left i_lt unfolding balance_scheduled_verify_def by simp
  have t2:
    "balance_sigma_verify p gamma ck c (as ! i) (es2 ! i) (zs2 ! i)"
    using right i_lt unfolding balance_scheduled_verify_def by simp
  have e1_ok: "valid_balance_challenge p (es1 ! i)"
    using t1 unfolding balance_sigma_verify_def by simp
  have e2_ok: "valid_balance_challenge p (es2 ! i)"
    using t2 unfolding balance_sigma_verify_def by simp
  have z1_ok: "valid_balance_response p gamma (es1 ! i) (zs1 ! i)"
    using t1 unfolding balance_sigma_verify_def by simp
  have z2_ok: "valid_balance_response p gamma (es2 ! i) (zs2 ! i)"
    using t2 unfolding balance_sigma_verify_def by simp
  obtain r where ext:
    "balance_sigma_extract (es1 ! i) (zs1 ! i) (es2 ! i) (zs2 ! i) = Some r"
    using balance_sigma_extract_some_if_distinct_binary[OF e1_ok e2_ok distinct]
    by blast
  have fork_ext: "balance_scheduled_fork_extract es1 zs1 es2 zs2 i = Some r"
    using ext unfolding balance_scheduled_fork_extract_def by simp
  have open_eq: "rand_commit p ck r = c"
    using balance_sigma_extract_algebraic_opening[
      OF t1 t2 c_valid c_canonical ext] .
  have bounded:
    "valid_vec r (cp_n2 p) \<and> all_bounded r (2 * gamma + 4 * cp_beta p)"
    using balance_sigma_extract_distinct_binary_bound[
      OF e1_ok e2_ok distinct z1_ok z2_ok ext] .
  show ?thesis
    using that fork_ext open_eq bounded by blast
qed

lemma amount_of_opening_eq_hd:
  assumes "valid_scalar_opening p op"
  shows "open_msg op = [amount_of_opening op]"
proof -
  have "length (open_msg op) = cp_n1 p"
    using assms unfolding valid_scalar_opening_def
    by (auto dest: valid_opening_msg_len)
  with valid_scalar_commit_params_props(2)[OF assms[unfolded valid_scalar_opening_def, THEN conjunct1]]
  show ?thesis
    unfolding amount_of_opening_def by (cases "open_msg op") auto
qed

lemma valid_scalar_opening_rand_len:
  assumes "valid_scalar_opening p op"
  shows "length (open_rand op) = cp_n2 p"
  using assms unfolding valid_scalar_opening_def
  by (auto dest: valid_opening_rand_len)

lemma aggregate_randomness_length:
  assumes "valid_scalar_opening p op_in1"
      and "valid_scalar_opening p op_in2"
      and "valid_scalar_opening p op_out1"
      and "valid_scalar_opening p op_out2"
  shows "length (aggregate_randomness op_in1 op_in2 op_out1 op_out2) = cp_n2 p"
proof -
  have len_in: "length (vec_add (open_rand op_in1) (open_rand op_in2)) = cp_n2 p"
    using valid_scalar_opening_rand_len[OF assms(1)]
          valid_scalar_opening_rand_len[OF assms(2)]
    by (simp add: vec_add_length)
  have len_out: "length (vec_add (open_rand op_out1) (open_rand op_out2)) = cp_n2 p"
    using valid_scalar_opening_rand_len[OF assms(3)]
          valid_scalar_opening_rand_len[OF assms(4)]
    by (simp add: vec_add_length)
  show ?thesis
    unfolding aggregate_randomness_def aggregate_opening_def opening_sub_def opening_add_def
    using len_in len_out
    by (simp add: vec_sub_length)
qed

lemma aggregate_randomness_bounded:
  assumes "valid_scalar_opening p op_in1"
      and "valid_scalar_opening p op_in2"
      and "valid_scalar_opening p op_out1"
      and "valid_scalar_opening p op_out2"
  shows "all_bounded (aggregate_randomness op_in1 op_in2 op_out1 op_out2) (4 * cp_beta p)"
proof -
  have b_in1: "all_bounded (open_rand op_in1) (cp_beta p)"
    using assms(1) unfolding valid_scalar_opening_def valid_opening_def all_bounded_def by auto
  have b_in2: "all_bounded (open_rand op_in2) (cp_beta p)"
    using assms(2) unfolding valid_scalar_opening_def valid_opening_def all_bounded_def by auto
  have b_out1: "all_bounded (open_rand op_out1) (cp_beta p)"
    using assms(3) unfolding valid_scalar_opening_def valid_opening_def all_bounded_def by auto
  have b_out2: "all_bounded (open_rand op_out2) (cp_beta p)"
    using assms(4) unfolding valid_scalar_opening_def valid_opening_def all_bounded_def by auto
  have len_in: "length (open_rand op_in1) = length (open_rand op_in2)"
    using valid_scalar_opening_rand_len[OF assms(1)]
          valid_scalar_opening_rand_len[OF assms(2)] by simp
  have len_out: "length (open_rand op_out1) = length (open_rand op_out2)"
    using valid_scalar_opening_rand_len[OF assms(3)]
          valid_scalar_opening_rand_len[OF assms(4)] by simp
  have in_bounded:
    "all_bounded (vec_add (open_rand op_in1) (open_rand op_in2)) (2 * cp_beta p)"
    using vec_add_bounded[OF b_in1 b_in2 len_in] by simp
  have out_bounded:
    "all_bounded (vec_add (open_rand op_out1) (open_rand op_out2)) (2 * cp_beta p)"
    using vec_add_bounded[OF b_out1 b_out2 len_out] by simp
  have len_sum:
    "length (vec_add (open_rand op_in1) (open_rand op_in2)) =
     length (vec_add (open_rand op_out1) (open_rand op_out2))"
    using valid_scalar_opening_rand_len[OF assms(1)]
          valid_scalar_opening_rand_len[OF assms(2)]
          valid_scalar_opening_rand_len[OF assms(3)]
          valid_scalar_opening_rand_len[OF assms(4)]
    by (simp add: vec_add_length)
  show ?thesis
  proof -
    have "aggregate_randomness op_in1 op_in2 op_out1 op_out2 =
          vec_sub (vec_add (open_rand op_in1) (open_rand op_in2))
                  (vec_add (open_rand op_out1) (open_rand op_out2))"
      unfolding aggregate_randomness_def aggregate_opening_def opening_sub_def opening_add_def
      by simp
    then show ?thesis
      using vec_sub_bounded[OF in_bounded out_bounded] by simp
  qed
qed

lemma commit_zero_opening_eq_rand_commit:
  assumes params_ok: "valid_scalar_commit_params p"
      and key_ok: "valid_commit_key p ck"
      and r_ok: "valid_vec r (cp_n2 p)"
  shows "commit ck (zero_opening r) (cp_q p) = rand_commit p ck r"
proof -
  have n1_one: "cp_n1 p = 1"
    using valid_scalar_commit_params_props(2)[OF params_ok] .
  have row_split:
    "\<And>row. row \<in> set ck \<Longrightarrow> inner_prod row ([0] @ r) = inner_prod (drop (cp_n1 p) row) r"
  proof -
    fix row
    assume row_in: "row \<in> set ck"
    have row_len: "length row = cp_n1 p + cp_n2 p"
      using valid_commit_key_dims[OF key_ok] row_in by auto
    then obtain x xs where row_def: "row = x # xs"
      using n1_one by (cases row) auto
    have "drop (cp_n1 p) row = xs"
      using row_def n1_one by simp
    moreover have "inner_prod row ([0] @ r) = inner_prod xs r"
      using row_def by (simp add: inner_prod_def)
    ultimately show "inner_prod row ([0] @ r) = inner_prod (drop (cp_n1 p) row) r"
      by simp
  qed
  have raw:
    "mat_vec_mult ck ([0] @ r) = mat_vec_mult (rand_commit_key p ck) r"
  proof (intro nth_equalityI)
    show "length (mat_vec_mult ck ([0] @ r)) = length (mat_vec_mult (rand_commit_key p ck) r)"
      using valid_commit_key_dims(1)[OF key_ok] rand_commit_key_dims(1)[OF key_ok]
      by (simp add: mat_vec_mult_length)
  next
    fix i
    assume i_lt: "i < length (mat_vec_mult ck ([0] @ r))"
    then have i_ck: "i < length ck"
      by (simp add: mat_vec_mult_length)
    have row_in: "ck ! i \<in> set ck"
      using i_ck by (simp add: nth_mem)
    have "(mat_vec_mult ck ([0] @ r)) ! i = inner_prod (ck ! i) ([0] @ r)"
      using i_ck by (simp add: mat_vec_mult_nth)
    also have "... = inner_prod (drop (cp_n1 p) (ck ! i)) r"
      using row_split[OF row_in] by simp
    also have "... = (mat_vec_mult (rand_commit_key p ck) r) ! i"
      using i_ck rand_commit_key_dims(1)[OF key_ok]
      by (simp add: rand_commit_key_def mat_vec_mult_nth)
    finally show "mat_vec_mult ck ([0] @ r) ! i = mat_vec_mult (rand_commit_key p ck) r ! i" .
  qed
  show ?thesis
    unfolding zero_opening_def commit_def rand_commit_def opening_vec_def
    using raw by simp
qed

lemma commit_add_hom:
  assumes msg_len: "length (open_msg op1) = length (open_msg op2)"
      and rand_len: "length (open_rand op1) = length (open_rand op2)"
      and q_pos: "q > 0"
  shows "commit ck (opening_add op1 op2) q =
    vec_mod (vec_add (commit ck op1 q) (commit ck op2 q)) q"
proof -
  have ov_eq:
    "opening_vec (opening_add op1 op2) = vec_add (opening_vec op1) (opening_vec op2)"
    unfolding opening_add_def opening_vec_def
    using msg_len by (simp add: vec_add_append_eq)
  have len_eq: "length (opening_vec op1) = length (opening_vec op2)"
    using msg_len rand_len unfolding opening_vec_def by simp
  have raw:
    "mat_vec_mult ck (opening_vec (opening_add op1 op2)) =
      vec_add (mat_vec_mult ck (opening_vec op1)) (mat_vec_mult ck (opening_vec op2))"
    using ov_eq len_eq by (simp add: mat_vec_mult_add_eq)
  have len_mat:
    "length (mat_vec_mult ck (opening_vec op1)) =
     length (mat_vec_mult ck (opening_vec op2))"
    by (simp add: mat_vec_mult_length)
  show ?thesis
  proof -
    have "commit ck (opening_add op1 op2) q =
          vec_mod (vec_add (mat_vec_mult ck (opening_vec op1)) (mat_vec_mult ck (opening_vec op2))) q"
      unfolding commit_def using raw by simp
    also have "... =
          vec_mod (vec_add (vec_mod (mat_vec_mult ck (opening_vec op1)) q)
                           (vec_mod (mat_vec_mult ck (opening_vec op2)) q)) q"
      using vec_mod_add_eq[OF len_mat q_pos] by simp
    finally show ?thesis
      unfolding commit_def by simp
  qed
qed

lemma commit_sub_hom:
  assumes msg_len: "length (open_msg op1) = length (open_msg op2)"
      and rand_len: "length (open_rand op1) = length (open_rand op2)"
      and q_pos: "q > 0"
  shows "commit ck (opening_sub op1 op2) q =
    vec_mod (vec_sub (commit ck op1 q) (commit ck op2 q)) q"
proof -
  have ov_eq:
    "opening_vec (opening_sub op1 op2) = vec_sub (opening_vec op1) (opening_vec op2)"
    unfolding opening_sub_def opening_vec_def
    using msg_len by (simp add: vec_sub_append_eq)
  have len_eq: "length (opening_vec op1) = length (opening_vec op2)"
    using msg_len rand_len unfolding opening_vec_def by simp
  have raw:
    "mat_vec_mult ck (opening_vec (opening_sub op1 op2)) =
      vec_sub (mat_vec_mult ck (opening_vec op1)) (mat_vec_mult ck (opening_vec op2))"
    using ov_eq len_eq by (simp add: mat_vec_mult_sub_eq)
  have len_mat:
    "length (mat_vec_mult ck (opening_vec op1)) =
     length (mat_vec_mult ck (opening_vec op2))"
    by (simp add: mat_vec_mult_length)
  show ?thesis
  proof -
    have "commit ck (opening_sub op1 op2) q =
          vec_mod (vec_sub (mat_vec_mult ck (opening_vec op1)) (mat_vec_mult ck (opening_vec op2))) q"
      unfolding commit_def using raw by simp
    also have "... =
          vec_mod (vec_sub (vec_mod (mat_vec_mult ck (opening_vec op1)) q)
                           (vec_mod (mat_vec_mult ck (opening_vec op2)) q)) q"
      using vec_mod_sub_eq[OF len_mat q_pos] by simp
    finally show ?thesis
      unfolding commit_def by simp
  qed
qed

lemma aggregate_opening_zero_message:
  assumes v1: "valid_scalar_opening p op_in1"
      and v2: "valid_scalar_opening p op_in2"
      and v3: "valid_scalar_opening p op_out1"
      and v4: "valid_scalar_opening p op_out2"
      and balance:
        "amount_of_opening op_in1 + amount_of_opening op_in2 =
         amount_of_opening op_out1 + amount_of_opening op_out2"
  shows "open_msg (aggregate_opening op_in1 op_in2 op_out1 op_out2) = [0]"
proof -
  have msg1: "open_msg op_in1 = [amount_of_opening op_in1]"
    using amount_of_opening_eq_hd[OF v1] .
  have msg2: "open_msg op_in2 = [amount_of_opening op_in2]"
    using amount_of_opening_eq_hd[OF v2] .
  have msg3: "open_msg op_out1 = [amount_of_opening op_out1]"
    using amount_of_opening_eq_hd[OF v3] .
  have msg4: "open_msg op_out2 = [amount_of_opening op_out2]"
    using amount_of_opening_eq_hd[OF v4] .
  have amt_zero:
    "amount_of_opening op_in1 + amount_of_opening op_in2 -
     amount_of_opening op_out1 - amount_of_opening op_out2 = 0"
    using balance by linarith
  have amt_zero_grouped:
    "amount_of_opening op_in1 + amount_of_opening op_in2 -
     (amount_of_opening op_out1 + amount_of_opening op_out2) = 0"
    using balance by linarith
  show ?thesis
    unfolding aggregate_opening_def opening_sub_def opening_add_def
    using amt_zero amt_zero_grouped msg1 msg2 msg3 msg4
    by (simp add: vec_add_def vec_sub_def)
qed

lemma balance_commitment_from_openings:
  assumes params_ok: "valid_scalar_commit_params p"
      and key_ok: "valid_commit_key p ck"
      and v1: "valid_scalar_opening p op_in1"
      and v2: "valid_scalar_opening p op_in2"
      and v3: "valid_scalar_opening p op_out1"
      and v4: "valid_scalar_opening p op_out2"
      and balance:
        "amount_of_opening op_in1 + amount_of_opening op_in2 =
         amount_of_opening op_out1 + amount_of_opening op_out2"
  shows "balance_commitment
           (commit ck op_in1 (cp_q p))
           (commit ck op_in2 (cp_q p))
           (commit ck op_out1 (cp_q p))
           (commit ck op_out2 (cp_q p))
           (cp_q p) =
         rand_commit p ck (aggregate_randomness op_in1 op_in2 op_out1 op_out2)"
proof -
  have q_pos: "cp_q p > 0"
    using valid_scalar_commit_params_props(5)[OF params_ok] by simp
  have len_msg_in1: "length (open_msg op_in1) = cp_n1 p"
    using v1 unfolding valid_scalar_opening_def by (auto dest: valid_opening_msg_len)
  have len_msg_in2: "length (open_msg op_in2) = cp_n1 p"
    using v2 unfolding valid_scalar_opening_def by (auto dest: valid_opening_msg_len)
  have msg_in: "length (open_msg op_in1) = length (open_msg op_in2)"
    using len_msg_in1 len_msg_in2 by simp
  have len_rand_in1: "length (open_rand op_in1) = cp_n2 p"
    using v1 unfolding valid_scalar_opening_def by (auto dest: valid_opening_rand_len)
  have len_rand_in2: "length (open_rand op_in2) = cp_n2 p"
    using v2 unfolding valid_scalar_opening_def by (auto dest: valid_opening_rand_len)
  have rand_in: "length (open_rand op_in1) = length (open_rand op_in2)"
    using len_rand_in1 len_rand_in2 by simp
  have len_msg_out1: "length (open_msg op_out1) = cp_n1 p"
    using v3 unfolding valid_scalar_opening_def by (auto dest: valid_opening_msg_len)
  have len_msg_out2: "length (open_msg op_out2) = cp_n1 p"
    using v4 unfolding valid_scalar_opening_def by (auto dest: valid_opening_msg_len)
  have msg_out: "length (open_msg op_out1) = length (open_msg op_out2)"
    using len_msg_out1 len_msg_out2 by simp
  have len_rand_out1: "length (open_rand op_out1) = cp_n2 p"
    using v3 unfolding valid_scalar_opening_def by (auto dest: valid_opening_rand_len)
  have len_rand_out2: "length (open_rand op_out2) = cp_n2 p"
    using v4 unfolding valid_scalar_opening_def by (auto dest: valid_opening_rand_len)
  have rand_out: "length (open_rand op_out1) = length (open_rand op_out2)"
    using len_rand_out1 len_rand_out2 by simp
  have in_add:
    "commit ck (opening_add op_in1 op_in2) (cp_q p) =
      vec_mod (vec_add (commit ck op_in1 (cp_q p)) (commit ck op_in2 (cp_q p))) (cp_q p)"
    using commit_add_hom[OF msg_in rand_in q_pos] .
  have out_add:
    "commit ck (opening_add op_out1 op_out2) (cp_q p) =
      vec_mod (vec_add (commit ck op_out1 (cp_q p)) (commit ck op_out2 (cp_q p))) (cp_q p)"
    using commit_add_hom[OF msg_out rand_out q_pos] .
  have msg_add_len:
    "length (open_msg (opening_add op_in1 op_in2)) =
     length (open_msg (opening_add op_out1 op_out2))"
    using len_msg_in1 len_msg_in2 len_msg_out1 len_msg_out2
    unfolding opening_add_def by (simp add: vec_add_length)
  have rand_add_len:
    "length (open_rand (opening_add op_in1 op_in2)) =
     length (open_rand (opening_add op_out1 op_out2))"
    using len_rand_in1 len_rand_in2 len_rand_out1 len_rand_out2
    unfolding opening_add_def by (simp add: vec_add_length)
  have agg_commit:
    "commit ck (aggregate_opening op_in1 op_in2 op_out1 op_out2) (cp_q p) =
      balance_commitment
        (commit ck op_in1 (cp_q p))
        (commit ck op_in2 (cp_q p))
        (commit ck op_out1 (cp_q p))
        (commit ck op_out2 (cp_q p))
        (cp_q p)"
  proof -
    have sub_hom:
      "commit ck (aggregate_opening op_in1 op_in2 op_out1 op_out2) (cp_q p) =
        vec_mod
          (vec_sub
            (commit ck (opening_add op_in1 op_in2) (cp_q p))
            (commit ck (opening_add op_out1 op_out2) (cp_q p)))
          (cp_q p)"
      unfolding aggregate_opening_def
      using commit_sub_hom[OF msg_add_len rand_add_len q_pos] by simp
    have len_bal:
      "length (vec_add (commit ck op_in1 (cp_q p)) (commit ck op_in2 (cp_q p))) =
       length (vec_add (commit ck op_out1 (cp_q p)) (commit ck op_out2 (cp_q p)))"
      by (simp add: commit_length vec_add_length)
    show ?thesis
      unfolding balance_commitment_def
      using sub_hom in_add out_add vec_mod_sub_eq[OF len_bal q_pos]
      by simp
  qed
  have agg_zero:
    "commit ck (aggregate_opening op_in1 op_in2 op_out1 op_out2) (cp_q p) =
      rand_commit p ck (aggregate_randomness op_in1 op_in2 op_out1 op_out2)"
  proof -
    have rand_len:
      "valid_vec (aggregate_randomness op_in1 op_in2 op_out1 op_out2) (cp_n2 p)"
      using aggregate_randomness_length[OF v1 v2 v3 v4]
      unfolding valid_vec_def by simp
    let ?agg = "aggregate_opening op_in1 op_in2 op_out1 op_out2"
    have zero_msg:
      "open_msg ?agg = [0]"
      using aggregate_opening_zero_message[OF v1 v2 v3 v4 balance] .
    obtain msg rnd where agg_fields: "?agg = \<lparr> open_msg = msg, open_rand = rnd \<rparr>"
      by (cases ?agg) auto
    have msg_eq: "msg = [0]"
      using zero_msg agg_fields by simp
    have rnd_eq: "rnd = aggregate_randomness op_in1 op_in2 op_out1 op_out2"
      using agg_fields by (simp add: aggregate_randomness_def)
    have "?agg = zero_opening (aggregate_randomness op_in1 op_in2 op_out1 op_out2)"
      using agg_fields msg_eq rnd_eq by (simp add: zero_opening_def)
    then show ?thesis
      using commit_zero_opening_eq_rand_commit[OF params_ok key_ok rand_len] by simp
  qed
  from agg_commit agg_zero show ?thesis by simp
qed

lemma balance_relation_from_openings:
  assumes params_ok: "valid_scalar_commit_params p"
      and key_ok: "valid_confidential_commit_key p ck"
      and open1: "verify_opening p ck c_in1 op_in1"
      and open2: "verify_opening p ck c_in2 op_in2"
      and open3: "verify_opening p ck c_out1 op_out1"
      and open4: "verify_opening p ck c_out2 op_out2"
      and balance:
        "amount_of_opening op_in1 + amount_of_opening op_in2 =
         amount_of_opening op_out1 + amount_of_opening op_out2"
  shows "balance_relation p ck
           (balance_commitment c_in1 c_in2 c_out1 c_out2 (cp_q p))
           (aggregate_randomness op_in1 op_in2 op_out1 op_out2)"
proof -
  have raw_key_ok: "valid_commit_key p ck"
    using key_ok by (rule valid_confidential_commit_key_valid)
  have v1: "valid_scalar_opening p op_in1"
    using params_ok open1 unfolding valid_scalar_opening_def
    by (simp add: verify_opening_valid)
  have v2: "valid_scalar_opening p op_in2"
    using params_ok open2 unfolding valid_scalar_opening_def
    by (simp add: verify_opening_valid)
  have v3: "valid_scalar_opening p op_out1"
    using params_ok open3 unfolding valid_scalar_opening_def
    by (simp add: verify_opening_valid)
  have v4: "valid_scalar_opening p op_out2"
    using params_ok open4 unfolding valid_scalar_opening_def
    by (simp add: verify_opening_valid)
  have rand_len:
    "valid_vec (aggregate_randomness op_in1 op_in2 op_out1 op_out2) (cp_n2 p)"
    using aggregate_randomness_length[OF v1 v2 v3 v4]
    unfolding valid_vec_def by simp
  have rand_bound:
    "all_bounded (aggregate_randomness op_in1 op_in2 op_out1 op_out2) (4 * cp_beta p)"
    using aggregate_randomness_bounded[OF v1 v2 v3 v4] .
  have relation_eq:
    "rand_commit p ck (aggregate_randomness op_in1 op_in2 op_out1 op_out2) =
      balance_commitment c_in1 c_in2 c_out1 c_out2 (cp_q p)"
    using balance_commitment_from_openings[OF params_ok raw_key_ok v1 v2 v3 v4 balance]
          verify_opening_eq[OF open1] verify_opening_eq[OF open2]
          verify_opening_eq[OF open3] verify_opening_eq[OF open4]
    by simp
  show ?thesis
    unfolding balance_relation_def valid_balance_witness_def
    using params_ok key_ok rand_len rand_bound relation_eq
    by auto
qed

lemma balance_sigma_response_valid:
  assumes params_ok: "valid_scalar_commit_params p"
      and mask_ok: "valid_balance_mask p gamma y"
      and challenge_ok: "valid_balance_challenge p e"
      and witness_ok: "valid_balance_witness p r"
  shows "valid_balance_response p gamma e (balance_sigma_respond r y e)"
proof -
  have len_eq: "length y = length r"
    using mask_ok witness_ok
    unfolding valid_balance_mask_def valid_balance_witness_def valid_vec_def by simp
  have scaled_bounded:
    "all_bounded (scalar_mult e r) (abs e * (4 * cp_beta p))"
    using witness_ok
    unfolding valid_balance_witness_def
    by (auto intro: scalar_mult_bounded)
  have bounded:
    "all_bounded (vec_add y (scalar_mult e r)) (gamma + abs e * (4 * cp_beta p))"
    using vec_add_bounded[OF _ scaled_bounded]
          mask_ok len_eq
    unfolding valid_balance_mask_def
    by (simp add: scalar_mult_length)
  have len_z: "valid_vec (vec_add y (scalar_mult e r)) (cp_n2 p)"
    using mask_ok witness_ok len_eq
    unfolding valid_balance_mask_def valid_balance_witness_def valid_vec_def
    by (simp add: vec_add_length scalar_mult_length)
  show ?thesis
    using len_z bounded challenge_ok
    unfolding valid_balance_response_def balance_response_bound_def balance_sigma_respond_def
    by simp
qed

lemma balance_sigma_complete:
  assumes relation: "balance_relation_wellformed p ck c r"
      and mask_ok: "valid_balance_mask p gamma y"
      and challenge_ok: "valid_balance_challenge p e"
      and a_def: "a = balance_sigma_commit p ck y"
      and z_def: "z = balance_sigma_respond r y e"
  shows "balance_sigma_verify p gamma ck c a e z"
proof -
  obtain params_ok key_ok witness_ok c_eq where
      relation_props:
        "valid_scalar_commit_params p"
        "valid_commit_key p ck"
        "valid_balance_witness p r"
        "rand_commit p ck r = c"
    using relation unfolding balance_relation_wellformed_def by blast
  have key_ok: "valid_commit_key p ck"
    using relation_props(2) .
  have a_valid:
    "valid_commitment p a"
    using rand_commit_valid[OF valid_scalar_commit_params_props(1)[OF relation_props(1)] key_ok]
          mask_ok a_def
    unfolding balance_sigma_commit_def valid_balance_mask_def
    by simp
  have c_valid:
    "valid_commitment p c"
  proof -
    have "valid_commitment p (rand_commit p ck r)"
      using rand_commit_valid[OF valid_scalar_commit_params_props(1)[OF relation_props(1)] key_ok]
            relation_props(3)
      unfolding valid_balance_witness_def
      by simp
    then show ?thesis
      using relation_props(4) by simp
  qed
  have z_valid:
    "valid_balance_response p gamma e z"
    using balance_sigma_response_valid[OF relation_props(1) mask_ok challenge_ok relation_props(3)]
          z_def by simp
  have verify_eq:
    "rand_commit p ck z = vec_mod (vec_add a (scalar_mult e c)) (cp_q p)"
  proof -
    have len_y: "length y = cp_n2 p"
      using mask_ok unfolding valid_balance_mask_def valid_vec_def by simp
    have len_r: "length r = cp_n2 p"
      using relation_props(3) unfolding valid_balance_witness_def valid_vec_def by simp
    have q_pos: "cp_q p > 0"
      using valid_scalar_commit_params_props(5)[OF relation_props(1)] by linarith
    have len_a: "length a = cp_m p"
      using a_valid unfolding valid_commitment_def valid_vec_def by simp
    have len_c: "length c = cp_m p"
      using c_valid unfolding valid_commitment_def valid_vec_def by simp
    have a_mod: "vec_mod a (cp_q p) = a"
      using a_def q_pos
      unfolding balance_sigma_commit_def rand_commit_def
      by (simp add: vec_mod_idemp)
    have "rand_commit p ck z = rand_commit p ck (vec_add y (scalar_mult e r))"
      using z_def by (simp add: balance_sigma_respond_def)
    also have "... = vec_mod (vec_add (rand_commit p ck y) (rand_commit p ck (scalar_mult e r))) (cp_q p)"
      using rand_commit_add_hom[OF key_ok len_y, of "scalar_mult e r"]
            q_pos len_r
      by (simp add: scalar_mult_length)
    also have "... = vec_mod (vec_add a (rand_commit p ck (scalar_mult e r))) (cp_q p)"
      using a_def by (simp add: balance_sigma_commit_def)
    also have "... = vec_mod (vec_add a (vec_mod (scalar_mult e c) (cp_q p))) (cp_q p)"
      using rand_commit_scalar_hom[OF key_ok len_r q_pos]
            relation_props(4)
      by simp
    also have "... = vec_mod (vec_add a (scalar_mult e c)) (cp_q p)"
      using vec_mod_add_eq[OF _ q_pos, of a "scalar_mult e c"]
            len_a len_c a_mod
      by (simp add: scalar_mult_length)
    finally show ?thesis .
  qed
  show ?thesis
    unfolding balance_sigma_verify_def
    using relation_props key_ok a_valid challenge_ok z_valid verify_eq by auto
qed

lemma balance_fs_complete:
  assumes proof_def: "balance_fs_prove p gamma ck c r ys = Some proof"
  shows "balance_fs_verify p gamma ck c proof"
proof -
  obtain as es zs where
      as_def: "as = map (balance_sigma_commit p ck) ys"
      and es_def: "es = balance_fs_challenges p ck c as"
      and zs_def: "zs = balance_sigma_responds r ys es"
      and rel: "balance_relation_wellformed p ck c r"
      and ys_len: "length ys = balance_fs_rounds"
      and masks_ok: "\<forall>i < balance_fs_rounds. valid_balance_mask p gamma (ys ! i)"
      and zs_ok: "\<forall>i < balance_fs_rounds. valid_balance_response p gamma (es ! i) (zs ! i)"
      and proof_eq: "proof = \<lparr> balance_as = as, balance_zs = zs \<rparr>"
    using proof_def
    unfolding balance_fs_prove_def Let_def
    by (auto split: if_splits)
  have params_ok: "valid_scalar_commit_params p"
    using rel unfolding balance_relation_wellformed_def by simp
  have key_ok: "valid_commit_key p ck"
    using rel unfolding balance_relation_wellformed_def by simp
  have es_len: "length es = balance_fs_rounds"
    using as_def es_def by (simp add: balance_fs_challenges_length)
  have as_len: "length as = balance_fs_rounds"
    using as_def ys_len by simp
  have zs_len: "length zs = balance_fs_rounds"
    using ys_len es_len zs_def
    by (simp add: balance_sigma_responds_length)
  have sigma_ok:
    "\<forall>i < balance_fs_rounds. balance_sigma_verify p gamma ck c (as ! i) (es ! i) (zs ! i)"
  proof (intro allI impI)
    fix i
    assume i_lt: "i < balance_fs_rounds"
    have ys_es_len: "length ys = length es"
      using ys_len es_len by simp
    have i_lt_ys: "i < length ys"
      using i_lt ys_len by simp
    have mask_ok: "valid_balance_mask p gamma (ys ! i)"
      using masks_ok i_lt by simp
    have challenge_ok: "valid_balance_challenge p (es ! i)"
      using balance_fs_challenge_valid[OF params_ok i_lt]
      unfolding es_def .
    have a_def: "as ! i = balance_sigma_commit p ck (ys ! i)"
      using i_lt ys_len as_def
      by simp
    have z_def: "zs ! i = balance_sigma_respond r (ys ! i) (es ! i)"
      using balance_sigma_responds_nth[OF ys_es_len i_lt_ys] zs_def
      by simp
    have sigma_ok_i:
      "balance_sigma_verify p gamma ck c
        (balance_sigma_commit p ck (ys ! i))
        (es ! i)
        (balance_sigma_respond r (ys ! i) (es ! i))"
      using rel mask_ok challenge_ok
      by (rule balance_sigma_complete, simp_all)
    show "balance_sigma_verify p gamma ck c (as ! i) (es ! i) (zs ! i)"
    proof -
      have a_rev: "balance_sigma_commit p ck (ys ! i) = as ! i"
        using a_def by simp
      have z_rev: "balance_sigma_respond r (ys ! i) (es ! i) = zs ! i"
        using z_def by simp
      show ?thesis
        using sigma_ok_i a_rev z_rev
        by simp
    qed
  qed
  have sigma_core_ok:
    "\<forall>i < balance_fs_rounds. balance_sigma_verify_core p gamma ck c (as ! i) (es ! i) (zs ! i)"
    using sigma_ok balance_sigma_verify_imp_core by blast
  show ?thesis
    unfolding balance_fs_verify_def
    using proof_eq params_ok key_ok as_len es_len zs_len sigma_core_ok
    by (simp add: as_def es_def zs_def balance_fs_challenges_length)
qed

export_code
  valid_scalar_commit_params
  valid_confidential_commit_key
  rand_commit_key rand_commit
  amount_of_opening balance_commitment public_amount_commitment
  fee_balance_commitment aggregate_randomness
  valid_balance_witness valid_balance_mask
  balance_response_bound valid_balance_challenge valid_balance_response
  balance_relation
  balance_fs_rounds
  balance_sigma_commit balance_sigma_respond
  canonical_balance_challenge balance_fs_challenges balance_sigma_responds
  balance_proof.make balance_as balance_zs
  balance_sigma_verify
  balance_fs_prove balance_fs_verify
  in Haskell module_name "Canon.ZK.Confidential_Balance"

export_code
  valid_scalar_commit_params
  valid_confidential_commit_key
  rand_commit_key rand_commit
  amount_of_opening balance_commitment public_amount_commitment
  fee_balance_commitment aggregate_randomness
  valid_balance_witness valid_balance_mask
  balance_response_bound valid_balance_challenge valid_balance_response
  balance_relation
  balance_fs_rounds
  balance_sigma_commit balance_sigma_respond
  canonical_balance_challenge balance_fs_challenges balance_sigma_responds
  balance_proof.make balance_as balance_zs
  balance_sigma_verify
  balance_fs_prove balance_fs_verify
  in OCaml module_name Confidential_balance

end
