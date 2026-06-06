theory Confidential_Transaction
  imports Confidential_Range Authenticated_Ledger Authenticated_Merkle
begin

text \<open>
  Confidential transaction proofs over SIS commitments.

  This theory composes four verifier slices:

  1. deterministic nullifier proofs for input notes,
  2. explicit membership proofs for a commitment ledger,
  3. deterministic confidential-balance proofs for a 2-in/2-out transfer,
  4. deterministic confidential-range proofs for both outputs.

  The resulting verifier is intentionally contract-friendly: every check is a
  first-order deterministic predicate over finite lists and proof records.
  Linkability is captured as determinism of nullifiers for a fixed opening.

  This development does not claim collision resistance or uniqueness of
  openings as pure theorems. Those properties remain hardness assumptions tied
  to the SIS commitment layer.
\<close>

definition nullifier :: "commit_params \<Rightarrow> commit_key \<Rightarrow> commit_opening \<Rightarrow> commitment" where
  "nullifier p nk op = commit nk op (cp_q p)"

definition valid_nullifier_mask ::
  "commit_params \<Rightarrow> int \<Rightarrow> commit_opening \<Rightarrow> bool" where
  "valid_nullifier_mask p gamma y \<longleftrightarrow>
    valid_vec (open_msg y) (cp_n1 p) \<and>
    valid_vec (open_rand y) (cp_n2 p) \<and>
    all_bounded (open_msg y) gamma \<and>
    all_bounded (open_rand y) gamma"

definition nullifier_response_bound ::
  "commit_params \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int" where
  "nullifier_response_bound p gamma e = gamma + abs e * cp_beta p"

definition valid_nullifier_challenge ::
  "commit_params \<Rightarrow> int \<Rightarrow> bool" where
  "valid_nullifier_challenge p e \<longleftrightarrow> valid_balance_challenge p e"

lemma valid_nullifier_challenge_binary:
  assumes "valid_nullifier_challenge p e"
  shows "e = 0 \<or> e = 1"
  using assms
  unfolding valid_nullifier_challenge_def
  by (rule valid_balance_challenge_binary)

lemma nullifier_response_bound_binary:
  assumes "valid_nullifier_challenge p e"
  shows "nullifier_response_bound p gamma e =
    (if e = 0 then gamma else gamma + cp_beta p)"
  using valid_nullifier_challenge_binary[OF assms]
  unfolding nullifier_response_bound_def
  by auto

definition valid_nullifier_response ::
  "commit_params \<Rightarrow> int \<Rightarrow> int \<Rightarrow> commit_opening \<Rightarrow> bool" where
  "valid_nullifier_response p gamma e z \<longleftrightarrow>
    valid_vec (open_msg z) (cp_n1 p) \<and>
    valid_vec (open_rand z) (cp_n2 p) \<and>
    all_bounded (open_msg z) (nullifier_response_bound p gamma e) \<and>
    all_bounded (open_rand z) (nullifier_response_bound p gamma e)"

definition nullifier_relation ::
  "commit_params \<Rightarrow> commit_key \<Rightarrow> commit_key \<Rightarrow> commitment \<Rightarrow> commitment \<Rightarrow> commit_opening \<Rightarrow> bool" where
  "nullifier_relation p ck nk c nf op \<longleftrightarrow>
    valid_scalar_commit_params p \<and>
    valid_confidential_commit_key p ck \<and>
    valid_confidential_commit_key p nk \<and>
    verify_opening p ck c op \<and>
    nullifier p nk op = nf"

definition nullifier_relation_wellformed ::
  "commit_params \<Rightarrow> commit_key \<Rightarrow> commit_key \<Rightarrow> commitment \<Rightarrow> commitment \<Rightarrow> commit_opening \<Rightarrow> bool" where
  "nullifier_relation_wellformed p ck nk c nf op \<longleftrightarrow>
    valid_scalar_commit_params p \<and>
    valid_commit_key p ck \<and>
    valid_commit_key p nk \<and>
    verify_opening p ck c op \<and>
    nullifier p nk op = nf"

lemma nullifier_relation_imp_wellformed:
  assumes "nullifier_relation p ck nk c nf op"
  shows "nullifier_relation_wellformed p ck nk c nf op"
  using assms valid_confidential_commit_key_valid
  unfolding nullifier_relation_def nullifier_relation_wellformed_def
  by blast

definition nullifier_fs_rounds :: nat where
  "nullifier_fs_rounds = balance_fs_rounds"

definition nullifier_fs_domain :: transcript_domain where
  "nullifier_fs_domain = 3001"

definition nullifier_fs_fields ::
  "commit_key \<Rightarrow> commit_key \<Rightarrow> commitment \<Rightarrow> commitment \<Rightarrow>
   commitment list \<Rightarrow> commitment list \<Rightarrow> int list" where
  "nullifier_fs_fields ck nk c nf a_commits a_nullifiers =
    [sum_list (concat ck),
     sum_list (concat nk),
     sum_list c,
     sum_list nf,
     sum_list (concat a_commits),
     sum_list (concat a_nullifiers)]"

record nullifier_proof =
  nullifier_a_commits :: "commitment list"
  nullifier_a_nullifiers :: "commitment list"
  nullifier_z_msgs :: "int_vec list"
  nullifier_z_rands :: "int_vec list"

definition nullifier_sigma_respond ::
  "commit_opening \<Rightarrow> commit_opening \<Rightarrow> int \<Rightarrow> commit_opening" where
  "nullifier_sigma_respond op y e = opening_add y (opening_scale e op)"

definition canonical_nullifier_challenge ::
  "commit_params \<Rightarrow> commit_key \<Rightarrow> commit_key \<Rightarrow> commitment \<Rightarrow> commitment \<Rightarrow>
   commitment \<Rightarrow> commitment \<Rightarrow> int" where
  "canonical_nullifier_challenge p ck nk c nf a_commit a_nullifier =
    binary_fs_challenge nullifier_fs_domain
      (nullifier_fs_fields ck nk c nf [a_commit] [a_nullifier]) 0"

lemma canonical_nullifier_challenge_valid:
  assumes "valid_scalar_commit_params p"
  shows "valid_nullifier_challenge p
           (canonical_nullifier_challenge p ck nk c nf a_commit a_nullifier)"
proof -
  have bit:
    "canonical_nullifier_challenge p ck nk c nf a_commit a_nullifier = 0 \<or>
     canonical_nullifier_challenge p ck nk c nf a_commit a_nullifier = 1"
    unfolding canonical_nullifier_challenge_def
    by (rule binary_fs_challenge_bit)
  show ?thesis
    using assms bit
    unfolding valid_nullifier_challenge_def valid_balance_challenge_def
              canonical_nullifier_challenge_def
    by auto
qed

definition nullifier_fs_challenges ::
  "commit_params \<Rightarrow> commit_key \<Rightarrow> commit_key \<Rightarrow> commitment \<Rightarrow> commitment \<Rightarrow>
   commitment list \<Rightarrow> commitment list \<Rightarrow> int list" where
  "nullifier_fs_challenges p ck nk c nf a_commits a_nullifiers =
    binary_fs_challenges nullifier_fs_domain
      (nullifier_fs_fields ck nk c nf a_commits a_nullifiers)
      nullifier_fs_rounds"

definition nullifier_sigma_responses ::
  "commit_opening \<Rightarrow> commit_opening list \<Rightarrow> int list \<Rightarrow> commit_opening list" where
  "nullifier_sigma_responses op ys es =
    sigma_response_rounds nullifier_sigma_respond op ys es"

lemma nullifier_fs_challenges_length:
  "length (nullifier_fs_challenges p ck nk c nf a_commits a_nullifiers) = nullifier_fs_rounds"
  unfolding nullifier_fs_challenges_def
  by simp

lemma nullifier_fs_challenge_valid:
  assumes "valid_scalar_commit_params p"
      and "i < nullifier_fs_rounds"
  shows "valid_nullifier_challenge p
           ((nullifier_fs_challenges p ck nk c nf a_commits a_nullifiers) ! i)"
proof -
  have bit:
    "(nullifier_fs_challenges p ck nk c nf a_commits a_nullifiers) ! i = 0 \<or>
     (nullifier_fs_challenges p ck nk c nf a_commits a_nullifiers) ! i = 1"
    using assms(2)
    unfolding nullifier_fs_challenges_def
    by (rule binary_fs_challenges_bit)
  show ?thesis
    using assms(1) bit
    unfolding valid_nullifier_challenge_def valid_balance_challenge_def
    by auto
qed

lemma nullifier_sigma_responses_length:
  assumes "length ys = length es"
  shows "length (nullifier_sigma_responses op ys es) = length ys"
  using assms
  unfolding nullifier_sigma_responses_def
  by (rule sigma_response_rounds_length)

lemma nullifier_sigma_responses_nth:
  assumes "length ys = length es"
      and "i < length ys"
  shows "(nullifier_sigma_responses op ys es) ! i = nullifier_sigma_respond op (ys ! i) (es ! i)"
  using assms
  unfolding nullifier_sigma_responses_def
  by (rule sigma_response_rounds_nth)

definition nullifier_sigma_verify ::
  "commit_params \<Rightarrow> int \<Rightarrow> commit_key \<Rightarrow> commit_key \<Rightarrow> commitment \<Rightarrow> commitment \<Rightarrow>
   commitment \<Rightarrow> commitment \<Rightarrow> int \<Rightarrow> commit_opening \<Rightarrow> bool" where
  "nullifier_sigma_verify p gamma ck nk c nf a_commit a_nullifier e z \<longleftrightarrow>
    valid_scalar_commit_params p \<and>
    valid_commit_key p ck \<and>
    valid_commit_key p nk \<and>
    valid_commitment p c \<and>
    valid_commitment p nf \<and>
    valid_commitment p a_commit \<and>
    valid_commitment p a_nullifier \<and>
    valid_nullifier_challenge p e \<and>
    valid_nullifier_response p gamma e z \<and>
    commit ck z (cp_q p) =
      vec_mod (vec_add a_commit (scalar_mult e c)) (cp_q p) \<and>
    nullifier p nk z =
      vec_mod (vec_add a_nullifier (scalar_mult e nf)) (cp_q p)"

definition nullifier_sigma_sim_commit ::
  "commit_params \<Rightarrow> commit_key \<Rightarrow> commitment \<Rightarrow> int \<Rightarrow> commit_opening \<Rightarrow> commitment" where
  "nullifier_sigma_sim_commit p ck c e z =
    vec_mod (vec_sub (commit ck z (cp_q p)) (scalar_mult e c)) (cp_q p)"

definition nullifier_sigma_sim_nullifier ::
  "commit_params \<Rightarrow> commit_key \<Rightarrow> commitment \<Rightarrow> int \<Rightarrow> commit_opening \<Rightarrow> commitment" where
  "nullifier_sigma_sim_nullifier p nk nf e z =
    vec_mod (vec_sub (nullifier p nk z) (scalar_mult e nf)) (cp_q p)"

definition nullifier_scheduled_sim_a_commits ::
  "commit_params \<Rightarrow> commit_key \<Rightarrow> commitment \<Rightarrow> int list \<Rightarrow>
   commit_opening list \<Rightarrow> commitment list" where
  "nullifier_scheduled_sim_a_commits p ck c es zs =
    map2 (nullifier_sigma_sim_commit p ck c) es zs"

definition nullifier_scheduled_sim_a_nullifiers ::
  "commit_params \<Rightarrow> commit_key \<Rightarrow> commitment \<Rightarrow> int list \<Rightarrow>
   commit_opening list \<Rightarrow> commitment list" where
  "nullifier_scheduled_sim_a_nullifiers p nk nf es zs =
    map2 (nullifier_sigma_sim_nullifier p nk nf) es zs"

definition nullifier_scheduled_simulate ::
  "commit_params \<Rightarrow> commit_key \<Rightarrow> commit_key \<Rightarrow> commitment \<Rightarrow>
   commitment \<Rightarrow> int list \<Rightarrow> commit_opening list \<Rightarrow> nullifier_proof" where
  "nullifier_scheduled_simulate p ck nk c nf es zs =
    \<lparr> nullifier_a_commits = nullifier_scheduled_sim_a_commits p ck c es zs,
      nullifier_a_nullifiers = nullifier_scheduled_sim_a_nullifiers p nk nf es zs,
      nullifier_z_msgs = map open_msg zs,
      nullifier_z_rands = map open_rand zs \<rparr>"

definition nullifier_sigma_extract ::
  "int \<Rightarrow> commit_opening \<Rightarrow> int \<Rightarrow> commit_opening \<Rightarrow> commit_opening option" where
  "nullifier_sigma_extract e1 z1 e2 z2 =
    (if e1 = 1 \<and> e2 = 0 then Some (opening_sub z1 z2)
     else if e1 = 0 \<and> e2 = 1 then Some (opening_sub z2 z1)
     else None)"

lemma nullifier_sigma_extract_some_if_distinct_binary:
  assumes e1_ok: "valid_nullifier_challenge p e1"
      and e2_ok: "valid_nullifier_challenge p e2"
      and distinct: "e1 \<noteq> e2"
  shows "\<exists>op. nullifier_sigma_extract e1 z1 e2 z2 = Some op"
  using valid_nullifier_challenge_binary[OF e1_ok]
        valid_nullifier_challenge_binary[OF e2_ok]
        distinct
  unfolding nullifier_sigma_extract_def
  by auto

lemma nullifier_sigma_extract_response_bound:
  assumes z1_ok: "valid_nullifier_response p gamma e1 z1"
      and z2_ok: "valid_nullifier_response p gamma e2 z2"
      and ext: "nullifier_sigma_extract e1 z1 e2 z2 = Some op"
  shows "valid_vec (open_msg op) (cp_n1 p) \<and>
         valid_vec (open_rand op) (cp_n2 p) \<and>
         all_bounded (open_msg op)
           (nullifier_response_bound p gamma e1 +
            nullifier_response_bound p gamma e2) \<and>
         all_bounded (open_rand op)
           (nullifier_response_bound p gamma e1 +
            nullifier_response_bound p gamma e2)"
proof -
  have msg_len1: "length (open_msg z1) = cp_n1 p"
    using z1_ok unfolding valid_nullifier_response_def valid_vec_def by simp
  have msg_len2: "length (open_msg z2) = cp_n1 p"
    using z2_ok unfolding valid_nullifier_response_def valid_vec_def by simp
  have rand_len1: "length (open_rand z1) = cp_n2 p"
    using z1_ok unfolding valid_nullifier_response_def valid_vec_def by simp
  have rand_len2: "length (open_rand z2) = cp_n2 p"
    using z2_ok unfolding valid_nullifier_response_def valid_vec_def by simp
  have msg_b1: "all_bounded (open_msg z1) (nullifier_response_bound p gamma e1)"
    using z1_ok unfolding valid_nullifier_response_def by simp
  have msg_b2: "all_bounded (open_msg z2) (nullifier_response_bound p gamma e2)"
    using z2_ok unfolding valid_nullifier_response_def by simp
  have rand_b1: "all_bounded (open_rand z1) (nullifier_response_bound p gamma e1)"
    using z1_ok unfolding valid_nullifier_response_def by simp
  have rand_b2: "all_bounded (open_rand z2) (nullifier_response_bound p gamma e2)"
    using z2_ok unfolding valid_nullifier_response_def by simp
  show ?thesis
  proof (cases "e1 = 1 \<and> e2 = 0")
    case True
    then have op_eq: "op = opening_sub z1 z2"
      using ext unfolding nullifier_sigma_extract_def by simp
    have msg_len: "length (open_msg op) = cp_n1 p"
      using op_eq msg_len1 msg_len2
      unfolding opening_sub_def by (simp add: vec_sub_length)
    have rand_len: "length (open_rand op) = cp_n2 p"
      using op_eq rand_len1 rand_len2
      unfolding opening_sub_def by (simp add: vec_sub_length)
    have msg_bound:
      "all_bounded (open_msg op)
        (nullifier_response_bound p gamma e1 +
         nullifier_response_bound p gamma e2)"
      using vec_sub_bounded[OF msg_b1 msg_b2] op_eq
      unfolding opening_sub_def by simp
    have rand_bound:
      "all_bounded (open_rand op)
        (nullifier_response_bound p gamma e1 +
         nullifier_response_bound p gamma e2)"
      using vec_sub_bounded[OF rand_b1 rand_b2] op_eq
      unfolding opening_sub_def by simp
    show ?thesis
      using msg_len rand_len msg_bound rand_bound
      unfolding valid_vec_def by simp
  next
    case False
    then have alt: "e1 = 0 \<and> e2 = 1"
      using ext unfolding nullifier_sigma_extract_def by (auto split: if_splits)
    then have op_eq: "op = opening_sub z2 z1"
      using ext False unfolding nullifier_sigma_extract_def by simp
    have msg_len: "length (open_msg op) = cp_n1 p"
      using op_eq msg_len1 msg_len2
      unfolding opening_sub_def by (simp add: vec_sub_length)
    have rand_len: "length (open_rand op) = cp_n2 p"
      using op_eq rand_len1 rand_len2
      unfolding opening_sub_def by (simp add: vec_sub_length)
    have msg_bound:
      "all_bounded (open_msg op)
        (nullifier_response_bound p gamma e1 +
         nullifier_response_bound p gamma e2)"
    proof -
      have raw_bound:
        "all_bounded (open_msg op)
          (nullifier_response_bound p gamma e2 +
           nullifier_response_bound p gamma e1)"
        using vec_sub_bounded[OF msg_b2 msg_b1] op_eq
        unfolding opening_sub_def by simp
      have sum_comm:
        "nullifier_response_bound p gamma e2 + nullifier_response_bound p gamma e1 =
         nullifier_response_bound p gamma e1 + nullifier_response_bound p gamma e2"
        by simp
      show ?thesis
        using raw_bound sum_comm by simp
    qed
    have rand_bound:
      "all_bounded (open_rand op)
        (nullifier_response_bound p gamma e1 +
         nullifier_response_bound p gamma e2)"
    proof -
      have raw_bound:
        "all_bounded (open_rand op)
          (nullifier_response_bound p gamma e2 +
           nullifier_response_bound p gamma e1)"
        using vec_sub_bounded[OF rand_b2 rand_b1] op_eq
        unfolding opening_sub_def by simp
      have sum_comm:
        "nullifier_response_bound p gamma e2 + nullifier_response_bound p gamma e1 =
         nullifier_response_bound p gamma e1 + nullifier_response_bound p gamma e2"
        by simp
      show ?thesis
        using raw_bound sum_comm by simp
    qed
    show ?thesis
      using msg_len rand_len msg_bound rand_bound
      unfolding valid_vec_def by simp
  qed
qed

lemma nullifier_sigma_extract_distinct_binary_bound:
  assumes e1_ok: "valid_nullifier_challenge p e1"
      and e2_ok: "valid_nullifier_challenge p e2"
      and distinct: "e1 \<noteq> e2"
      and z1_ok: "valid_nullifier_response p gamma e1 z1"
      and z2_ok: "valid_nullifier_response p gamma e2 z2"
      and ext: "nullifier_sigma_extract e1 z1 e2 z2 = Some op"
  shows "valid_vec (open_msg op) (cp_n1 p) \<and>
         valid_vec (open_rand op) (cp_n2 p) \<and>
         all_bounded (open_msg op) (2 * gamma + cp_beta p) \<and>
         all_bounded (open_rand op) (2 * gamma + cp_beta p)"
proof -
  have extracted:
    "valid_vec (open_msg op) (cp_n1 p) \<and>
     valid_vec (open_rand op) (cp_n2 p) \<and>
     all_bounded (open_msg op)
       (nullifier_response_bound p gamma e1 +
        nullifier_response_bound p gamma e2) \<and>
     all_bounded (open_rand op)
       (nullifier_response_bound p gamma e1 +
        nullifier_response_bound p gamma e2)"
    using nullifier_sigma_extract_response_bound[OF z1_ok z2_ok ext] .
  have "nullifier_response_bound p gamma e1 +
        nullifier_response_bound p gamma e2 =
        2 * gamma + cp_beta p"
    using valid_nullifier_challenge_binary[OF e1_ok]
          valid_nullifier_challenge_binary[OF e2_ok]
          distinct
    unfolding nullifier_response_bound_def
    by auto
  then show ?thesis
    using extracted by simp
qed

lemma nullifier_extract_sub_commit:
  assumes q_pos: "cp_q p > 0"
      and msg_len: "length (open_msg z_hi) = length (open_msg z_lo)"
      and rand_len: "length (open_rand z_hi) = length (open_rand z_lo)"
      and hi_eq: "commit key z_hi (cp_q p) = vec_mod (vec_add a c) (cp_q p)"
      and lo_eq: "commit key z_lo (cp_q p) = vec_mod a (cp_q p)"
      and len_a_c: "length a = length c"
      and c_canonical: "vec_mod c (cp_q p) = c"
  shows "commit key (opening_sub z_hi z_lo) (cp_q p) = c"
proof -
  have "commit key (opening_sub z_hi z_lo) (cp_q p) =
        vec_mod (vec_sub (commit key z_hi (cp_q p))
                         (commit key z_lo (cp_q p))) (cp_q p)"
    using commit_sub_hom[OF msg_len rand_len q_pos] .
  also have "... =
        vec_mod (vec_sub (vec_mod (vec_add a c) (cp_q p)) (vec_mod a (cp_q p))) (cp_q p)"
    using hi_eq lo_eq by simp
  also have "... = c"
    using vec_mod_sub_add_cancel_left[OF len_a_c q_pos c_canonical] .
  finally show ?thesis .
qed

lemma nullifier_sigma_extract_algebraic_opening:
  assumes t1:
        "nullifier_sigma_verify p gamma ck nk c nf a_commit a_nullifier e1 z1"
      and t2:
        "nullifier_sigma_verify p gamma ck nk c nf a_commit a_nullifier e2 z2"
      and c_canonical: "vec_mod c (cp_q p) = c"
      and nf_canonical: "vec_mod nf (cp_q p) = nf"
      and ext: "nullifier_sigma_extract e1 z1 e2 z2 = Some op"
  shows "commit ck op (cp_q p) = c \<and> nullifier p nk op = nf"
proof -
  have params_ok: "valid_scalar_commit_params p"
    using t1 unfolding nullifier_sigma_verify_def by simp
  have c_valid: "valid_commitment p c"
    using t1 unfolding nullifier_sigma_verify_def by simp
  have nf_valid: "valid_commitment p nf"
    using t1 unfolding nullifier_sigma_verify_def by simp
  have a_commit_valid: "valid_commitment p a_commit"
    using t1 unfolding nullifier_sigma_verify_def by simp
  have a_nullifier_valid: "valid_commitment p a_nullifier"
    using t1 unfolding nullifier_sigma_verify_def by simp
  have z1_ok: "valid_nullifier_response p gamma e1 z1"
    using t1 unfolding nullifier_sigma_verify_def by simp
  have z2_ok: "valid_nullifier_response p gamma e2 z2"
    using t2 unfolding nullifier_sigma_verify_def by simp
  have commit_eq1:
    "commit ck z1 (cp_q p) =
      vec_mod (vec_add a_commit (scalar_mult e1 c)) (cp_q p)"
    using t1 unfolding nullifier_sigma_verify_def by simp
  have commit_eq2:
    "commit ck z2 (cp_q p) =
      vec_mod (vec_add a_commit (scalar_mult e2 c)) (cp_q p)"
    using t2 unfolding nullifier_sigma_verify_def by simp
  have nf_eq1:
    "commit nk z1 (cp_q p) =
      vec_mod (vec_add a_nullifier (scalar_mult e1 nf)) (cp_q p)"
    using t1 unfolding nullifier_sigma_verify_def nullifier_def by simp
  have nf_eq2:
    "commit nk z2 (cp_q p) =
      vec_mod (vec_add a_nullifier (scalar_mult e2 nf)) (cp_q p)"
    using t2 unfolding nullifier_sigma_verify_def nullifier_def by simp
  have q_pos: "cp_q p > 0"
    using valid_scalar_commit_params_props(5)[OF params_ok] by linarith
  have msg_len1: "length (open_msg z1) = cp_n1 p"
    using z1_ok unfolding valid_nullifier_response_def valid_vec_def by simp
  have msg_len2: "length (open_msg z2) = cp_n1 p"
    using z2_ok unfolding valid_nullifier_response_def valid_vec_def by simp
  have rand_len1: "length (open_rand z1) = cp_n2 p"
    using z1_ok unfolding valid_nullifier_response_def valid_vec_def by simp
  have rand_len2: "length (open_rand z2) = cp_n2 p"
    using z2_ok unfolding valid_nullifier_response_def valid_vec_def by simp
  have msg_len_eq: "length (open_msg z1) = length (open_msg z2)"
    using msg_len1 msg_len2 by simp
  have rand_len_eq: "length (open_rand z1) = length (open_rand z2)"
    using rand_len1 rand_len2 by simp
  have len_a_commit_c: "length a_commit = length c"
    using a_commit_valid c_valid unfolding valid_commitment_def valid_vec_def by simp
  have len_a_nf: "length a_nullifier = length nf"
    using a_nullifier_valid nf_valid unfolding valid_commitment_def valid_vec_def by simp
  show ?thesis
  proof (cases "e1 = 1 \<and> e2 = 0")
    case True
    then have e_vals: "e1 = 1" "e2 = 0"
      by auto
    have op_eq: "op = opening_sub z1 z2"
      using ext True unfolding nullifier_sigma_extract_def by simp
    have commit_hi:
      "commit ck z1 (cp_q p) = vec_mod (vec_add a_commit c) (cp_q p)"
      using commit_eq1 e_vals len_a_commit_c by (simp add: scalar_mult_one)
    have commit_lo:
      "commit ck z2 (cp_q p) = vec_mod a_commit (cp_q p)"
      using commit_eq2 e_vals len_a_commit_c by (simp add: vec_add_scalar_zero_right)
    have nf_hi:
      "commit nk z1 (cp_q p) = vec_mod (vec_add a_nullifier nf) (cp_q p)"
      using nf_eq1 e_vals len_a_nf by (simp add: scalar_mult_one)
    have nf_lo:
      "commit nk z2 (cp_q p) = vec_mod a_nullifier (cp_q p)"
      using nf_eq2 e_vals len_a_nf by (simp add: vec_add_scalar_zero_right)
    have commit_extract:
      "commit ck op (cp_q p) = c"
      using nullifier_extract_sub_commit[
        OF q_pos msg_len_eq rand_len_eq commit_hi commit_lo len_a_commit_c c_canonical]
      by (simp add: op_eq)
    have nf_extract:
      "nullifier p nk op = nf"
      unfolding nullifier_def
      using nullifier_extract_sub_commit[
        OF q_pos msg_len_eq rand_len_eq nf_hi nf_lo len_a_nf nf_canonical]
      by (simp add: op_eq)
    show ?thesis
      using commit_extract nf_extract by simp
  next
    case False
    have alt: "e1 = 0 \<and> e2 = 1"
      using ext False unfolding nullifier_sigma_extract_def by (auto split: if_splits)
    then have e_vals: "e1 = 0" "e2 = 1"
      by auto
    have op_eq: "op = opening_sub z2 z1"
      using ext False alt unfolding nullifier_sigma_extract_def by simp
    have commit_hi:
      "commit ck z2 (cp_q p) = vec_mod (vec_add a_commit c) (cp_q p)"
      using commit_eq2 e_vals len_a_commit_c by (simp add: scalar_mult_one)
    have commit_lo:
      "commit ck z1 (cp_q p) = vec_mod a_commit (cp_q p)"
      using commit_eq1 e_vals len_a_commit_c by (simp add: vec_add_scalar_zero_right)
    have nf_hi:
      "commit nk z2 (cp_q p) = vec_mod (vec_add a_nullifier nf) (cp_q p)"
      using nf_eq2 e_vals len_a_nf by (simp add: scalar_mult_one)
    have nf_lo:
      "commit nk z1 (cp_q p) = vec_mod a_nullifier (cp_q p)"
      using nf_eq1 e_vals len_a_nf by (simp add: vec_add_scalar_zero_right)
    have commit_extract:
      "commit ck op (cp_q p) = c"
      using nullifier_extract_sub_commit[
        OF q_pos _ _ commit_hi commit_lo len_a_commit_c c_canonical]
      using msg_len_eq rand_len_eq
      by (simp add: op_eq)
    have nf_extract:
      "nullifier p nk op = nf"
      unfolding nullifier_def
      using nullifier_extract_sub_commit[
        OF q_pos _ _ nf_hi nf_lo len_a_nf nf_canonical]
      using msg_len_eq rand_len_eq
      by (simp add: op_eq)
    show ?thesis
      using commit_extract nf_extract by simp
  qed
qed

definition nullifier_fs_prove ::
  "commit_params \<Rightarrow> int \<Rightarrow> commit_key \<Rightarrow> commit_key \<Rightarrow> commitment \<Rightarrow> commitment \<Rightarrow>
   commit_opening \<Rightarrow> commit_opening list \<Rightarrow> nullifier_proof option" where
  "nullifier_fs_prove p gamma ck nk c nf op ys =
    (let a_commits = map (\<lambda>y. commit ck y (cp_q p)) ys;
         a_nullifiers = map (\<lambda>y. nullifier p nk y) ys;
         es = nullifier_fs_challenges p ck nk c nf a_commits a_nullifiers;
         zs = nullifier_sigma_responses op ys es;
         proof =
           \<lparr> nullifier_a_commits = a_commits,
             nullifier_a_nullifiers = a_nullifiers,
             nullifier_z_msgs = map open_msg zs,
             nullifier_z_rands = map open_rand zs \<rparr>
     in if nullifier_relation_wellformed p ck nk c nf op \<and>
           length ys = nullifier_fs_rounds \<and>
           (\<forall>i < nullifier_fs_rounds. valid_nullifier_mask p gamma (ys ! i)) \<and>
           (\<forall>i < nullifier_fs_rounds. valid_nullifier_response p gamma (es ! i) (zs ! i))
        then Some proof
        else None)"

definition nullifier_fs_verify ::
  "commit_params \<Rightarrow> int \<Rightarrow> commit_key \<Rightarrow> commit_key \<Rightarrow> commitment \<Rightarrow> commitment \<Rightarrow>
   nullifier_proof \<Rightarrow> bool" where
  "nullifier_fs_verify p gamma ck nk c nf proof \<longleftrightarrow>
    (let a_commits = nullifier_a_commits proof;
         a_nullifiers = nullifier_a_nullifiers proof;
         z_msgs = nullifier_z_msgs proof;
         z_rands = nullifier_z_rands proof;
         es = nullifier_fs_challenges p ck nk c nf a_commits a_nullifiers
     in length a_commits = nullifier_fs_rounds \<and>
        length a_nullifiers = nullifier_fs_rounds \<and>
        length z_msgs = nullifier_fs_rounds \<and>
        length z_rands = nullifier_fs_rounds \<and>
        (\<forall>i < nullifier_fs_rounds.
          nullifier_sigma_verify p gamma ck nk c nf
            (a_commits ! i)
            (a_nullifiers ! i)
            (es ! i)
            \<lparr> open_msg = z_msgs ! i, open_rand = z_rands ! i \<rparr>))"

definition nullifier_scheduled_verify ::
  "commit_params \<Rightarrow> int \<Rightarrow> commit_key \<Rightarrow> commit_key \<Rightarrow>
   commitment \<Rightarrow> commitment \<Rightarrow> commitment list \<Rightarrow> commitment list \<Rightarrow>
   int list \<Rightarrow> commit_opening list \<Rightarrow> bool" where
  "nullifier_scheduled_verify p gamma ck nk c nf a_commits a_nullifiers es zs \<longleftrightarrow>
    length a_commits = nullifier_fs_rounds \<and>
    length a_nullifiers = nullifier_fs_rounds \<and>
    length es = nullifier_fs_rounds \<and>
    length zs = nullifier_fs_rounds \<and>
    (\<forall>i < nullifier_fs_rounds.
      nullifier_sigma_verify p gamma ck nk c nf
        (a_commits ! i) (a_nullifiers ! i) (es ! i) (zs ! i))"

definition nullifier_scheduled_fork_extract ::
  "int list \<Rightarrow> commit_opening list \<Rightarrow> int list \<Rightarrow> commit_opening list \<Rightarrow>
   nat \<Rightarrow> commit_opening option" where
  "nullifier_scheduled_fork_extract es1 zs1 es2 zs2 i =
    nullifier_sigma_extract (es1 ! i) (zs1 ! i) (es2 ! i) (zs2 ! i)"

lemma nullifier_scheduled_fork_extract_algebraic_opening:
  assumes left:
        "nullifier_scheduled_verify p gamma ck nk c nf
           a_commits a_nullifiers es1 zs1"
      and right:
        "nullifier_scheduled_verify p gamma ck nk c nf
           a_commits a_nullifiers es2 zs2"
      and fork: "forked_binary_challenge_schedules nullifier_fs_rounds es1 es2 i"
      and c_canonical: "vec_mod c (cp_q p) = c"
      and nf_canonical: "vec_mod nf (cp_q p) = nf"
  obtains op where
    "nullifier_scheduled_fork_extract es1 zs1 es2 zs2 i = Some op"
    "commit ck op (cp_q p) = c"
    "nullifier p nk op = nf"
    "valid_vec (open_msg op) (cp_n1 p)"
    "valid_vec (open_rand op) (cp_n2 p)"
    "all_bounded (open_msg op) (2 * gamma + cp_beta p)"
    "all_bounded (open_rand op) (2 * gamma + cp_beta p)"
proof -
  have i_lt: "i < nullifier_fs_rounds"
    using fork by (rule forked_binary_challenge_schedules_index(1))
  have distinct: "es1 ! i \<noteq> es2 ! i"
    using fork by (rule forked_binary_challenge_schedules_index(2))
  have t1:
    "nullifier_sigma_verify p gamma ck nk c nf
      (a_commits ! i) (a_nullifiers ! i) (es1 ! i) (zs1 ! i)"
    using left i_lt unfolding nullifier_scheduled_verify_def by simp
  have t2:
    "nullifier_sigma_verify p gamma ck nk c nf
      (a_commits ! i) (a_nullifiers ! i) (es2 ! i) (zs2 ! i)"
    using right i_lt unfolding nullifier_scheduled_verify_def by simp
  have e1_ok: "valid_nullifier_challenge p (es1 ! i)"
    using t1 unfolding nullifier_sigma_verify_def by simp
  have e2_ok: "valid_nullifier_challenge p (es2 ! i)"
    using t2 unfolding nullifier_sigma_verify_def by simp
  have z1_ok: "valid_nullifier_response p gamma (es1 ! i) (zs1 ! i)"
    using t1 unfolding nullifier_sigma_verify_def by simp
  have z2_ok: "valid_nullifier_response p gamma (es2 ! i) (zs2 ! i)"
    using t2 unfolding nullifier_sigma_verify_def by simp
  obtain op where ext:
    "nullifier_sigma_extract (es1 ! i) (zs1 ! i) (es2 ! i) (zs2 ! i) =
       Some op"
    using nullifier_sigma_extract_some_if_distinct_binary[
      OF e1_ok e2_ok distinct]
    by blast
  have fork_ext: "nullifier_scheduled_fork_extract es1 zs1 es2 zs2 i = Some op"
    using ext unfolding nullifier_scheduled_fork_extract_def by simp
  have algebraic:
    "commit ck op (cp_q p) = c \<and> nullifier p nk op = nf"
    using nullifier_sigma_extract_algebraic_opening[
      OF t1 t2 c_canonical nf_canonical ext] .
  have bounded:
    "valid_vec (open_msg op) (cp_n1 p) \<and>
     valid_vec (open_rand op) (cp_n2 p) \<and>
     all_bounded (open_msg op) (2 * gamma + cp_beta p) \<and>
     all_bounded (open_rand op) (2 * gamma + cp_beta p)"
    using nullifier_sigma_extract_distinct_binary_bound[
      OF e1_ok e2_ok distinct z1_ok z2_ok ext] .
  show ?thesis
    using that fork_ext algebraic bounded by blast
qed

record membership_proof =
  member_index :: nat
  member_root :: commitment
  member_siblings :: "commitment list"
  member_directions :: "bool list"

fun membership_index_of :: "commitment list \<Rightarrow> commitment \<Rightarrow> nat option" where
  "membership_index_of [] c = None"
| "membership_index_of (x # xs) c =
    (if x = c then Some 0 else map_option Suc (membership_index_of xs c))"

definition membership_prove ::
  "commit_params \<Rightarrow> commitment list \<Rightarrow> commitment \<Rightarrow> membership_proof option" where
  "membership_prove p ledger c =
    (case membership_index_of ledger c of
       None \<Rightarrow> None
     | Some i \<Rightarrow>
         map_option
           (\<lambda>sibs.
              \<lparr> member_index = i,
                member_root = ledger_root p ledger,
                member_siblings = sibs,
                member_directions = index_directions (length sibs) i \<rparr>)
           (membership_siblings p ledger i))"

definition membership_verify ::
  "commit_params \<Rightarrow> commitment \<Rightarrow> membership_proof \<Rightarrow> bool" where
  "membership_verify p c proof \<longleftrightarrow>
    length (member_siblings proof) = length (member_directions proof) \<and>
    member_directions proof =
      index_directions (length (member_siblings proof)) (member_index proof) \<and>
    auth_path_root p c (member_siblings proof) (member_directions proof) =
      member_root proof"

record merkle_membership_proof =
  merkle_member_index :: nat
  merkle_member_root :: digest
  merkle_member_siblings :: "digest list"
  merkle_member_directions :: "bool list"

definition merkle_membership_verify ::
  "merkle_hash \<Rightarrow> commitment \<Rightarrow> merkle_membership_proof \<Rightarrow> bool" where
  "merkle_membership_verify h c proof \<longleftrightarrow>
    length (merkle_member_siblings proof) = length (merkle_member_directions proof) \<and>
    merkle_member_directions proof =
      index_directions (length (merkle_member_siblings proof)) (merkle_member_index proof) \<and>
    merkle_membership_valid h c
      (merkle_member_root proof)
      (merkle_member_siblings proof)
      (merkle_member_directions proof)"

theorem merkle_membership_verify_same_path_sound:
  assumes cr: "collision_resistant_hash h"
      and valid1: "merkle_membership_verify h c1 proof"
      and valid2: "merkle_membership_verify h c2 proof"
  shows "c1 = c2"
  using merkle_membership_same_path_sound[OF cr, of c1
        "merkle_member_root proof"
        "merkle_member_siblings proof"
        "merkle_member_directions proof" c2]
        valid1 valid2
  unfolding merkle_membership_verify_def
  by blast

record verified_note =
  note_commitment :: commitment
  note_range_proof :: range_proof

definition commitment_ledger :: "verified_note list \<Rightarrow> commitment list" where
  "commitment_ledger notes = map note_commitment notes"

definition ledger_valid ::
  "commit_params \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> commit_key \<Rightarrow> commitment \<Rightarrow> verified_note list \<Rightarrow> commitment list \<Rightarrow> bool" where
  "ledger_valid p gamma k ck ledger_rt notes spent \<longleftrightarrow>
    valid_scalar_commit_params p \<and>
    valid_commit_key p ck \<and>
    ledger_rt = ledger_root p (commitment_ledger notes) \<and>
    distinct spent \<and>
    (\<forall>note \<in> set notes.
      range_fs_verify p gamma k ck (note_commitment note) (note_range_proof note))"

record transaction_proof =
  tx_in1_member :: membership_proof
  tx_in2_member :: membership_proof
  tx_in1_nullifier :: nullifier_proof
  tx_in2_nullifier :: nullifier_proof
  tx_balance :: balance_proof
  tx_out1_range :: range_proof
  tx_out2_range :: range_proof

record merkle_transaction_proof =
  tx_merkle_in1_member :: merkle_membership_proof
  tx_merkle_in2_member :: merkle_membership_proof
  tx_merkle_in1_nullifier :: nullifier_proof
  tx_merkle_in2_nullifier :: nullifier_proof
  tx_merkle_balance :: balance_proof
  tx_merkle_out1_range :: range_proof
  tx_merkle_out2_range :: range_proof

definition transaction_relation ::
  "commit_params \<Rightarrow> commit_key \<Rightarrow> commit_key \<Rightarrow> commitment list \<Rightarrow> commitment list \<Rightarrow>
   commitment \<Rightarrow> commitment \<Rightarrow> commitment \<Rightarrow> commitment \<Rightarrow> commitment \<Rightarrow> commitment \<Rightarrow>
   commit_opening \<Rightarrow> commit_opening \<Rightarrow> commit_opening \<Rightarrow> commit_opening \<Rightarrow>
   commit_opening list \<Rightarrow> commit_opening list \<Rightarrow> commit_opening list \<Rightarrow> commit_opening list \<Rightarrow> bool" where
  "transaction_relation p ck nk ledger spent c_in1 c_in2 c_out1 c_out2 nf1 nf2
      op_in1 op_in2 op_out1 op_out2 out1_bits out1_comps out2_bits out2_comps \<longleftrightarrow>
    nullifier_relation p ck nk c_in1 nf1 op_in1 \<and>
    nullifier_relation p ck nk c_in2 nf2 op_in2 \<and>
    c_in1 \<in> set ledger \<and>
    c_in2 \<in> set ledger \<and>
    nf1 \<notin> set spent \<and>
    nf2 \<notin> set spent \<and>
    nf1 \<noteq> nf2 \<and>
    range_relation p ck c_out1 op_out1 out1_bits out1_comps \<and>
    range_relation p ck c_out2 op_out2 out2_bits out2_comps \<and>
    amount_of_opening op_in1 + amount_of_opening op_in2 =
      amount_of_opening op_out1 + amount_of_opening op_out2"

definition transaction_relation_wellformed ::
  "commit_params \<Rightarrow> commit_key \<Rightarrow> commit_key \<Rightarrow> commitment list \<Rightarrow> commitment list \<Rightarrow>
   commitment \<Rightarrow> commitment \<Rightarrow> commitment \<Rightarrow> commitment \<Rightarrow> commitment \<Rightarrow> commitment \<Rightarrow>
   commit_opening \<Rightarrow> commit_opening \<Rightarrow> commit_opening \<Rightarrow> commit_opening \<Rightarrow>
   commit_opening list \<Rightarrow> commit_opening list \<Rightarrow> commit_opening list \<Rightarrow> commit_opening list \<Rightarrow> bool" where
  "transaction_relation_wellformed p ck nk ledger spent c_in1 c_in2 c_out1 c_out2 nf1 nf2
      op_in1 op_in2 op_out1 op_out2 out1_bits out1_comps out2_bits out2_comps \<longleftrightarrow>
    nullifier_relation_wellformed p ck nk c_in1 nf1 op_in1 \<and>
    nullifier_relation_wellformed p ck nk c_in2 nf2 op_in2 \<and>
    c_in1 \<in> set ledger \<and>
    c_in2 \<in> set ledger \<and>
    nf1 \<notin> set spent \<and>
    nf2 \<notin> set spent \<and>
    nf1 \<noteq> nf2 \<and>
    range_relation p ck c_out1 op_out1 out1_bits out1_comps \<and>
    range_relation p ck c_out2 op_out2 out2_bits out2_comps \<and>
    amount_of_opening op_in1 + amount_of_opening op_in2 =
      amount_of_opening op_out1 + amount_of_opening op_out2"

definition transaction_relation_fee ::
  "commit_params \<Rightarrow> commit_key \<Rightarrow> commit_key \<Rightarrow> commitment list \<Rightarrow> commitment list \<Rightarrow>
   int \<Rightarrow>
   commitment \<Rightarrow> commitment \<Rightarrow> commitment \<Rightarrow> commitment \<Rightarrow> commitment \<Rightarrow> commitment \<Rightarrow>
   commit_opening \<Rightarrow> commit_opening \<Rightarrow> commit_opening \<Rightarrow> commit_opening \<Rightarrow>
   commit_opening list \<Rightarrow> commit_opening list \<Rightarrow> commit_opening list \<Rightarrow> commit_opening list \<Rightarrow> bool" where
  "transaction_relation_fee p ck nk ledger spent public_fee
      c_in1 c_in2 c_out1 c_out2 nf1 nf2
      op_in1 op_in2 op_out1 op_out2 out1_bits out1_comps out2_bits out2_comps \<longleftrightarrow>
    public_fee \<ge> 0 \<and>
    nullifier_relation p ck nk c_in1 nf1 op_in1 \<and>
    nullifier_relation p ck nk c_in2 nf2 op_in2 \<and>
    c_in1 \<in> set ledger \<and>
    c_in2 \<in> set ledger \<and>
    nf1 \<notin> set spent \<and>
    nf2 \<notin> set spent \<and>
    nf1 \<noteq> nf2 \<and>
    range_relation p ck c_out1 op_out1 out1_bits out1_comps \<and>
    range_relation p ck c_out2 op_out2 out2_bits out2_comps \<and>
    amount_of_opening op_in1 + amount_of_opening op_in2 =
      amount_of_opening op_out1 + amount_of_opening op_out2 + public_fee"

definition transaction_relation_wellformed_fee ::
  "commit_params \<Rightarrow> commit_key \<Rightarrow> commit_key \<Rightarrow> commitment list \<Rightarrow> commitment list \<Rightarrow>
   int \<Rightarrow>
   commitment \<Rightarrow> commitment \<Rightarrow> commitment \<Rightarrow> commitment \<Rightarrow> commitment \<Rightarrow> commitment \<Rightarrow>
   commit_opening \<Rightarrow> commit_opening \<Rightarrow> commit_opening \<Rightarrow> commit_opening \<Rightarrow>
   commit_opening list \<Rightarrow> commit_opening list \<Rightarrow> commit_opening list \<Rightarrow> commit_opening list \<Rightarrow> bool" where
  "transaction_relation_wellformed_fee p ck nk ledger spent public_fee
      c_in1 c_in2 c_out1 c_out2 nf1 nf2
      op_in1 op_in2 op_out1 op_out2 out1_bits out1_comps out2_bits out2_comps \<longleftrightarrow>
    public_fee \<ge> 0 \<and>
    nullifier_relation_wellformed p ck nk c_in1 nf1 op_in1 \<and>
    nullifier_relation_wellformed p ck nk c_in2 nf2 op_in2 \<and>
    c_in1 \<in> set ledger \<and>
    c_in2 \<in> set ledger \<and>
    nf1 \<notin> set spent \<and>
    nf2 \<notin> set spent \<and>
    nf1 \<noteq> nf2 \<and>
    range_relation p ck c_out1 op_out1 out1_bits out1_comps \<and>
    range_relation p ck c_out2 op_out2 out2_bits out2_comps \<and>
    amount_of_opening op_in1 + amount_of_opening op_in2 =
      amount_of_opening op_out1 + amount_of_opening op_out2 + public_fee"

lemma transaction_relation_imp_wellformed:
  assumes "transaction_relation p ck nk ledger spent c_in1 c_in2 c_out1 c_out2 nf1 nf2
      op_in1 op_in2 op_out1 op_out2 out1_bits out1_comps out2_bits out2_comps"
  shows "transaction_relation_wellformed p ck nk ledger spent c_in1 c_in2 c_out1 c_out2 nf1 nf2
      op_in1 op_in2 op_out1 op_out2 out1_bits out1_comps out2_bits out2_comps"
  using assms nullifier_relation_imp_wellformed
  unfolding transaction_relation_def transaction_relation_wellformed_def
  by blast

lemma transaction_relation_fee_imp_wellformed:
  assumes "transaction_relation_fee p ck nk ledger spent public_fee
      c_in1 c_in2 c_out1 c_out2 nf1 nf2
      op_in1 op_in2 op_out1 op_out2 out1_bits out1_comps out2_bits out2_comps"
  shows "transaction_relation_wellformed_fee p ck nk ledger spent public_fee
      c_in1 c_in2 c_out1 c_out2 nf1 nf2
      op_in1 op_in2 op_out1 op_out2 out1_bits out1_comps out2_bits out2_comps"
  using assms nullifier_relation_imp_wellformed
  unfolding transaction_relation_fee_def transaction_relation_wellformed_fee_def
  by blast

lemma transaction_relation_fee_zero_iff:
  "transaction_relation_fee p ck nk ledger spent 0
      c_in1 c_in2 c_out1 c_out2 nf1 nf2
      op_in1 op_in2 op_out1 op_out2 out1_bits out1_comps out2_bits out2_comps
   \<longleftrightarrow>
   transaction_relation p ck nk ledger spent c_in1 c_in2 c_out1 c_out2 nf1 nf2
      op_in1 op_in2 op_out1 op_out2 out1_bits out1_comps out2_bits out2_comps"
  unfolding transaction_relation_fee_def transaction_relation_def
  by simp

definition transaction_fs_verify ::
  "commit_params \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> commit_key \<Rightarrow> commit_key \<Rightarrow> commitment \<Rightarrow> commitment list \<Rightarrow>
   commitment \<Rightarrow> commitment \<Rightarrow> commitment \<Rightarrow> commitment \<Rightarrow> commitment \<Rightarrow> commitment \<Rightarrow>
   transaction_proof \<Rightarrow> bool" where
  "transaction_fs_verify p gamma k ck nk ledger_rt spent c_in1 c_in2 c_out1 c_out2 nf1 nf2 proof \<longleftrightarrow>
    valid_commit_key p ck \<and>
    valid_commit_key p nk \<and>
    membership_verify p c_in1 (tx_in1_member proof) \<and>
    membership_verify p c_in2 (tx_in2_member proof) \<and>
    member_root (tx_in1_member proof) = ledger_rt \<and>
    member_root (tx_in2_member proof) = ledger_rt \<and>
    member_index (tx_in1_member proof) \<noteq> member_index (tx_in2_member proof) \<and>
    nf1 \<notin> set spent \<and>
    nf2 \<notin> set spent \<and>
    nf1 \<noteq> nf2 \<and>
    nullifier_fs_verify p gamma ck nk c_in1 nf1 (tx_in1_nullifier proof) \<and>
    nullifier_fs_verify p gamma ck nk c_in2 nf2 (tx_in2_nullifier proof) \<and>
    balance_fs_verify p gamma ck
      (balance_commitment c_in1 c_in2 c_out1 c_out2 (cp_q p))
      (tx_balance proof) \<and>
    range_fs_verify p gamma k ck c_out1 (tx_out1_range proof) \<and>
    range_fs_verify p gamma k ck c_out2 (tx_out2_range proof)"

definition transaction_fs_verify_merkle ::
  "merkle_hash \<Rightarrow> commit_params \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> commit_key \<Rightarrow> commit_key \<Rightarrow> digest \<Rightarrow> commitment list \<Rightarrow>
   commitment \<Rightarrow> commitment \<Rightarrow> commitment \<Rightarrow> commitment \<Rightarrow> commitment \<Rightarrow> commitment \<Rightarrow>
   merkle_transaction_proof \<Rightarrow> bool" where
  "transaction_fs_verify_merkle h p gamma k ck nk ledger_rt spent c_in1 c_in2 c_out1 c_out2 nf1 nf2 proof \<longleftrightarrow>
    valid_commit_key p ck \<and>
    valid_commit_key p nk \<and>
    merkle_membership_verify h c_in1 (tx_merkle_in1_member proof) \<and>
    merkle_membership_verify h c_in2 (tx_merkle_in2_member proof) \<and>
    merkle_member_root (tx_merkle_in1_member proof) = ledger_rt \<and>
    merkle_member_root (tx_merkle_in2_member proof) = ledger_rt \<and>
    merkle_member_index (tx_merkle_in1_member proof) \<noteq> merkle_member_index (tx_merkle_in2_member proof) \<and>
    nf1 \<notin> set spent \<and>
    nf2 \<notin> set spent \<and>
    nf1 \<noteq> nf2 \<and>
    nullifier_fs_verify p gamma ck nk c_in1 nf1 (tx_merkle_in1_nullifier proof) \<and>
    nullifier_fs_verify p gamma ck nk c_in2 nf2 (tx_merkle_in2_nullifier proof) \<and>
    balance_fs_verify p gamma ck
      (balance_commitment c_in1 c_in2 c_out1 c_out2 (cp_q p))
      (tx_merkle_balance proof) \<and>
    range_fs_verify p gamma k ck c_out1 (tx_merkle_out1_range proof) \<and>
    range_fs_verify p gamma k ck c_out2 (tx_merkle_out2_range proof)"

definition transaction_fs_verify_merkle_fee ::
  "merkle_hash \<Rightarrow> commit_params \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> commit_key \<Rightarrow> commit_key \<Rightarrow>
   digest \<Rightarrow> commitment list \<Rightarrow> int \<Rightarrow>
   commitment \<Rightarrow> commitment \<Rightarrow> commitment \<Rightarrow> commitment \<Rightarrow> commitment \<Rightarrow> commitment \<Rightarrow>
   merkle_transaction_proof \<Rightarrow> bool" where
  "transaction_fs_verify_merkle_fee h p gamma k ck nk ledger_rt spent public_fee
      c_in1 c_in2 c_out1 c_out2 nf1 nf2 proof \<longleftrightarrow>
    public_fee \<ge> 0 \<and>
    valid_commit_key p ck \<and>
    valid_commit_key p nk \<and>
    merkle_membership_verify h c_in1 (tx_merkle_in1_member proof) \<and>
    merkle_membership_verify h c_in2 (tx_merkle_in2_member proof) \<and>
    merkle_member_root (tx_merkle_in1_member proof) = ledger_rt \<and>
    merkle_member_root (tx_merkle_in2_member proof) = ledger_rt \<and>
    merkle_member_index (tx_merkle_in1_member proof) \<noteq> merkle_member_index (tx_merkle_in2_member proof) \<and>
    nf1 \<notin> set spent \<and>
    nf2 \<notin> set spent \<and>
    nf1 \<noteq> nf2 \<and>
    nullifier_fs_verify p gamma ck nk c_in1 nf1 (tx_merkle_in1_nullifier proof) \<and>
    nullifier_fs_verify p gamma ck nk c_in2 nf2 (tx_merkle_in2_nullifier proof) \<and>
    balance_fs_verify p gamma ck
      (fee_balance_commitment p ck c_in1 c_in2 c_out1 c_out2 public_fee)
      (tx_merkle_balance proof) \<and>
    range_fs_verify p gamma k ck c_out1 (tx_merkle_out1_range proof) \<and>
    range_fs_verify p gamma k ck c_out2 (tx_merkle_out2_range proof)"

lemma transaction_fs_verify_merkle_roots:
  assumes "transaction_fs_verify_merkle h p gamma k ck nk ledger_rt spent
    c_in1 c_in2 c_out1 c_out2 nf1 nf2 proof"
  shows "merkle_member_root (tx_merkle_in1_member proof) = ledger_rt"
    and "merkle_member_root (tx_merkle_in2_member proof) = ledger_rt"
  using assms
  unfolding transaction_fs_verify_merkle_def
  by blast+

theorem transaction_fs_verify_merkle_in1_same_path_sound:
  assumes cr: "collision_resistant_hash h"
      and verified: "transaction_fs_verify_merkle h p gamma k ck nk ledger_rt spent
        c_in1 c_in2 c_out1 c_out2 nf1 nf2 proof"
      and alternate: "merkle_membership_verify h c_in1' (tx_merkle_in1_member proof)"
  shows "c_in1' = c_in1"
  using merkle_membership_verify_same_path_sound[OF cr alternate]
        verified
  unfolding transaction_fs_verify_merkle_def
  by blast

theorem transaction_fs_verify_merkle_in2_same_path_sound:
  assumes cr: "collision_resistant_hash h"
      and verified: "transaction_fs_verify_merkle h p gamma k ck nk ledger_rt spent
        c_in1 c_in2 c_out1 c_out2 nf1 nf2 proof"
      and alternate: "merkle_membership_verify h c_in2' (tx_merkle_in2_member proof)"
  shows "c_in2' = c_in2"
  using merkle_membership_verify_same_path_sound[OF cr alternate]
        verified
  unfolding transaction_fs_verify_merkle_def
  by blast

theorem transaction_fs_verify_merkle_fee_in1_same_path_sound:
  assumes cr: "collision_resistant_hash h"
      and verified: "transaction_fs_verify_merkle_fee h p gamma k ck nk ledger_rt spent public_fee
        c_in1 c_in2 c_out1 c_out2 nf1 nf2 proof"
      and alternate: "merkle_membership_verify h c_in1' (tx_merkle_in1_member proof)"
  shows "c_in1' = c_in1"
  using merkle_membership_verify_same_path_sound[OF cr alternate]
        verified
  unfolding transaction_fs_verify_merkle_fee_def
  by blast

theorem transaction_fs_verify_merkle_fee_in2_same_path_sound:
  assumes cr: "collision_resistant_hash h"
      and verified: "transaction_fs_verify_merkle_fee h p gamma k ck nk ledger_rt spent public_fee
        c_in1 c_in2 c_out1 c_out2 nf1 nf2 proof"
      and alternate: "merkle_membership_verify h c_in2' (tx_merkle_in2_member proof)"
  shows "c_in2' = c_in2"
  using merkle_membership_verify_same_path_sound[OF cr alternate]
        verified
  unfolding transaction_fs_verify_merkle_fee_def
  by blast

definition transaction_fs_prove ::
  "commit_params \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> commit_key \<Rightarrow> commit_key \<Rightarrow> commitment list \<Rightarrow> commitment list \<Rightarrow>
   commitment \<Rightarrow> commitment \<Rightarrow> commitment \<Rightarrow> commitment \<Rightarrow> commitment \<Rightarrow> commitment \<Rightarrow>
   commit_opening \<Rightarrow> commit_opening \<Rightarrow> commit_opening \<Rightarrow> commit_opening \<Rightarrow>
   commit_opening list \<Rightarrow> commit_opening list \<Rightarrow> commit_opening list \<Rightarrow> commit_opening list \<Rightarrow>
   commit_opening list \<Rightarrow> commit_opening list \<Rightarrow> int_vec list \<Rightarrow>
   int_vec list \<Rightarrow> int_vec list list \<Rightarrow> int_vec list \<Rightarrow> int_vec list list \<Rightarrow> transaction_proof option" where
  "transaction_fs_prove p gamma k ck nk ledger spent c_in1 c_in2 c_out1 c_out2 nf1 nf2
      op_in1 op_in2 op_out1 op_out2 out1_bits out1_comps out2_bits out2_comps
      y_in1 y_in2 y_balance y_out1_amounts y_out1_pairss y_out2_amounts y_out2_pairss =
    (case (membership_prove p ledger c_in1,
           membership_prove p ledger c_in2,
           nullifier_fs_prove p gamma ck nk c_in1 nf1 op_in1 y_in1,
           nullifier_fs_prove p gamma ck nk c_in2 nf2 op_in2 y_in2,
           balance_fs_prove p gamma ck
             (balance_commitment c_in1 c_in2 c_out1 c_out2 (cp_q p))
             (aggregate_randomness op_in1 op_in2 op_out1 op_out2)
             y_balance,
           range_fs_prove p gamma k ck c_out1 op_out1 out1_bits out1_comps y_out1_amounts y_out1_pairss,
           range_fs_prove p gamma k ck c_out2 op_out2 out2_bits out2_comps y_out2_amounts y_out2_pairss) of
       (Some member1, Some member2, Some nf_proof1, Some nf_proof2, Some bal_proof, Some range1, Some range2) \<Rightarrow>
         if transaction_relation_wellformed p ck nk ledger spent c_in1 c_in2 c_out1 c_out2 nf1 nf2
              op_in1 op_in2 op_out1 op_out2 out1_bits out1_comps out2_bits out2_comps \<and>
            member_index member1 \<noteq> member_index member2
         then Some
            \<lparr> tx_in1_member = member1,
              tx_in2_member = member2,
              tx_in1_nullifier = nf_proof1,
              tx_in2_nullifier = nf_proof2,
              tx_balance = bal_proof,
              tx_out1_range = range1,
              tx_out2_range = range2 \<rparr>
         else None
     | _ \<Rightarrow> None)"

definition ledger_note_at :: "verified_note list \<Rightarrow> membership_proof \<Rightarrow> verified_note" where
  "ledger_note_at notes proof = notes ! member_index proof"

definition ledger_apply_notes ::
  "verified_note list \<Rightarrow> transaction_proof \<Rightarrow> commitment \<Rightarrow> commitment \<Rightarrow> verified_note list" where
  "ledger_apply_notes notes proof c_out1 c_out2 =
    (let note1 = ledger_note_at notes (tx_in1_member proof);
         note2 = ledger_note_at notes (tx_in2_member proof);
         remaining = remove1 note2 (remove1 note1 notes);
         out1 = \<lparr> note_commitment = c_out1, note_range_proof = tx_out1_range proof \<rparr>;
         out2 = \<lparr> note_commitment = c_out2, note_range_proof = tx_out2_range proof \<rparr>
     in out1 # out2 # remaining)"

definition ledger_apply_spent ::
  "commitment list \<Rightarrow> commitment \<Rightarrow> commitment \<Rightarrow> commitment list" where
  "ledger_apply_spent spent nf1 nf2 = nf1 # nf2 # spent"

text \<open>
  @{const ledger_valid} is intentionally only a local snapshot invariant: it
  says that the current note set has the claimed root, that spent nullifiers are
  duplicate-free, and that every stored output note carries a locally verifying
  range proof. Security-relevant ledger evolution is expressed separately by
  the \<open>ledger_step_semantic\<close> relation, which requires a witness to the abstract
  transfer relation and ties the consumed notes to authenticated membership
  proofs against the pre-state root.
\<close>

definition ledger_step_semantic ::
  "commit_params \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> commit_key \<Rightarrow> commit_key \<Rightarrow>
   verified_note list \<Rightarrow> commitment list \<Rightarrow>
   commitment \<Rightarrow> commitment \<Rightarrow> commitment \<Rightarrow> commitment \<Rightarrow> commitment \<Rightarrow> commitment \<Rightarrow>
   transaction_proof \<Rightarrow> verified_note list \<Rightarrow> commitment list \<Rightarrow> bool" where
  "ledger_step_semantic p gamma k ck nk notes spent
      c_in1 c_in2 c_out1 c_out2 nf1 nf2 proof notes' spent' \<longleftrightarrow>
    ledger_valid p gamma k ck (ledger_root p (commitment_ledger notes)) notes spent \<and>
    membership_verify p c_in1 (tx_in1_member proof) \<and>
    membership_verify p c_in2 (tx_in2_member proof) \<and>
    member_root (tx_in1_member proof) = ledger_root p (commitment_ledger notes) \<and>
    member_root (tx_in2_member proof) = ledger_root p (commitment_ledger notes) \<and>
    member_index (tx_in1_member proof) \<noteq> member_index (tx_in2_member proof) \<and>
    notes' = ledger_apply_notes notes proof c_out1 c_out2 \<and>
    spent' = ledger_apply_spent spent nf1 nf2 \<and>
    ledger_valid p gamma k ck (ledger_root p (commitment_ledger notes')) notes' spent' \<and>
    (\<exists>op_in1 op_in2 op_out1 op_out2 out1_bits out1_comps out2_bits out2_comps.
      transaction_relation p ck nk (commitment_ledger notes) spent
        c_in1 c_in2 c_out1 c_out2 nf1 nf2
        op_in1 op_in2 op_out1 op_out2
        out1_bits out1_comps out2_bits out2_comps)"

lemma ledger_step_semantic_pre_valid:
  assumes
    "ledger_step_semantic p gamma k ck nk notes spent
       c_in1 c_in2 c_out1 c_out2 nf1 nf2 proof notes' spent'"
  shows "ledger_valid p gamma k ck (ledger_root p (commitment_ledger notes)) notes spent"
  using assms
  unfolding ledger_step_semantic_def
  by blast

lemma ledger_step_semantic_post_notes:
  assumes
    "ledger_step_semantic p gamma k ck nk notes spent
       c_in1 c_in2 c_out1 c_out2 nf1 nf2 proof notes' spent'"
  shows "notes' = ledger_apply_notes notes proof c_out1 c_out2"
  using assms
  unfolding ledger_step_semantic_def
  by blast

lemma ledger_step_semantic_post_spent:
  assumes
    "ledger_step_semantic p gamma k ck nk notes spent
       c_in1 c_in2 c_out1 c_out2 nf1 nf2 proof notes' spent'"
  shows "spent' = ledger_apply_spent spent nf1 nf2"
  using assms
  unfolding ledger_step_semantic_def
  by blast

lemma ledger_step_semantic_post_valid:
  assumes
    "ledger_step_semantic p gamma k ck nk notes spent
       c_in1 c_in2 c_out1 c_out2 nf1 nf2 proof notes' spent'"
  shows "ledger_valid p gamma k ck (ledger_root p (commitment_ledger notes')) notes' spent'"
  using assms
  unfolding ledger_step_semantic_def
  by blast

lemma ledger_step_semantic_membership_roots:
  assumes
    "ledger_step_semantic p gamma k ck nk notes spent
       c_in1 c_in2 c_out1 c_out2 nf1 nf2 proof notes' spent'"
  shows "member_root (tx_in1_member proof) = ledger_root p (commitment_ledger notes)"
    and "member_root (tx_in2_member proof) = ledger_root p (commitment_ledger notes)"
  using assms
  unfolding ledger_step_semantic_def
  by blast+

lemma ledger_step_semantic_distinct_inputs:
  assumes
    "ledger_step_semantic p gamma k ck nk notes spent
       c_in1 c_in2 c_out1 c_out2 nf1 nf2 proof notes' spent'"
  shows "member_index (tx_in1_member proof) \<noteq> member_index (tx_in2_member proof)"
  using assms
  unfolding ledger_step_semantic_def
  by blast

lemma ledger_step_semanticE_transaction_relation:
  assumes
    "ledger_step_semantic p gamma k ck nk notes spent
       c_in1 c_in2 c_out1 c_out2 nf1 nf2 proof notes' spent'"
  obtains op_in1 op_in2 op_out1 op_out2 out1_bits out1_comps out2_bits out2_comps
    where
      "transaction_relation p ck nk (commitment_ledger notes) spent
         c_in1 c_in2 c_out1 c_out2 nf1 nf2
         op_in1 op_in2 op_out1 op_out2
         out1_bits out1_comps out2_bits out2_comps"
  using assms
  unfolding ledger_step_semantic_def
  by blast

inductive ledger_reachable ::
  "commit_params \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> commit_key \<Rightarrow> commit_key \<Rightarrow>
   verified_note list \<Rightarrow> commitment list \<Rightarrow> verified_note list \<Rightarrow> commitment list \<Rightarrow> bool" where
  ledger_reachable_refl:
    "ledger_valid p gamma k ck (ledger_root p (commitment_ledger notes0)) notes0 spent0 \<Longrightarrow>
     ledger_reachable p gamma k ck nk notes0 spent0 notes0 spent0"
| ledger_reachable_step:
    "ledger_reachable p gamma k ck nk notes0 spent0 notes spent \<Longrightarrow>
     ledger_step_semantic p gamma k ck nk notes spent
       c_in1 c_in2 c_out1 c_out2 nf1 nf2 proof notes' spent' \<Longrightarrow>
     ledger_reachable p gamma k ck nk notes0 spent0 notes' spent'"

lemma valid_opening_msg_bounded:
  assumes "valid_opening p op"
  shows "all_bounded (open_msg op) (cp_beta p)"
  using valid_opening_bounded[OF assms]
  unfolding all_bounded_def by auto

lemma valid_opening_rand_bounded:
  assumes "valid_opening p op"
  shows "all_bounded (open_rand op) (cp_beta p)"
  using valid_opening_bounded[OF assms]
  unfolding all_bounded_def by auto

lemma commit_shape_valid:
  assumes params_ok: "valid_commit_params p"
      and key_ok: "valid_commit_key p ck"
      and msg_ok: "valid_vec (open_msg op) (cp_n1 p)"
      and rand_ok: "valid_vec (open_rand op) (cp_n2 p)"
  shows "valid_commitment p (commit ck op (cp_q p))"
proof -
  have "length (commit ck op (cp_q p)) = length ck"
    by (simp add: commit_length)
  also have "... = cp_m p"
    using valid_commit_key_dims[OF key_ok] by simp
  finally show ?thesis
    unfolding valid_commitment_def valid_vec_def by simp
qed

lemma nullifier_valid:
  assumes params_ok: "valid_scalar_commit_params p"
      and key_ok: "valid_commit_key p nk"
      and open_ok: "valid_opening p op"
  shows "valid_commitment p (nullifier p nk op)"
  unfolding nullifier_def
  using commit_valid[OF valid_scalar_commit_params_props(1)[OF params_ok] key_ok open_ok] .

lemma nullifier_sigma_simulate_verify:
  assumes params_ok: "valid_scalar_commit_params p"
      and key_ok: "valid_commit_key p ck"
      and nf_key_ok: "valid_commit_key p nk"
      and c_valid: "valid_commitment p c"
      and nf_valid: "valid_commitment p nf"
      and challenge_ok: "valid_nullifier_challenge p e"
      and z_ok: "valid_nullifier_response p gamma e z"
      and a_commit_def: "a_commit = nullifier_sigma_sim_commit p ck c e z"
      and a_nullifier_def: "a_nullifier = nullifier_sigma_sim_nullifier p nk nf e z"
  shows "nullifier_sigma_verify p gamma ck nk c nf a_commit a_nullifier e z"
proof -
  have msg_vec: "valid_vec (open_msg z) (cp_n1 p)"
    using z_ok unfolding valid_nullifier_response_def by simp
  have rand_vec: "valid_vec (open_rand z) (cp_n2 p)"
    using z_ok unfolding valid_nullifier_response_def by simp
  have commit_z_valid: "valid_commitment p (commit ck z (cp_q p))"
    using commit_shape_valid[OF valid_scalar_commit_params_props(1)[OF params_ok]
          key_ok msg_vec rand_vec] .
  have nullifier_z_valid: "valid_commitment p (nullifier p nk z)"
    unfolding nullifier_def
    using commit_shape_valid[OF valid_scalar_commit_params_props(1)[OF params_ok]
          nf_key_ok msg_vec rand_vec] .
  have len_commit_z: "length (commit ck z (cp_q p)) = cp_m p"
    using commit_z_valid unfolding valid_commitment_def valid_vec_def by simp
  have len_nullifier_z: "length (nullifier p nk z) = cp_m p"
    using nullifier_z_valid unfolding valid_commitment_def valid_vec_def by simp
  have len_c: "length c = cp_m p"
    using c_valid unfolding valid_commitment_def valid_vec_def by simp
  have len_nf: "length nf = cp_m p"
    using nf_valid unfolding valid_commitment_def valid_vec_def by simp
  have a_commit_valid: "valid_commitment p a_commit"
    unfolding a_commit_def nullifier_sigma_sim_commit_def valid_commitment_def valid_vec_def
    using len_commit_z len_c
    by (simp add: vec_sub_length scalar_mult_length vec_mod_length)
  have a_nullifier_valid: "valid_commitment p a_nullifier"
    unfolding a_nullifier_def nullifier_sigma_sim_nullifier_def valid_commitment_def valid_vec_def
    using len_nullifier_z len_nf
    by (simp add: vec_sub_length scalar_mult_length vec_mod_length)
  have q_pos: "cp_q p > 0"
    using valid_scalar_commit_params_props(5)[OF params_ok] by linarith
  have commit_len_eq:
    "length (commit ck z (cp_q p)) = length (scalar_mult e c)"
    using len_commit_z len_c by (simp add: scalar_mult_length)
  have nullifier_len_eq:
    "length (nullifier p nk z) = length (scalar_mult e nf)"
    using len_nullifier_z len_nf by (simp add: scalar_mult_length)
  have commit_canonical:
    "vec_mod (commit ck z (cp_q p)) (cp_q p) = commit ck z (cp_q p)"
    unfolding commit_def
    using q_pos by (simp add: vec_mod_idemp)
  have nullifier_canonical:
    "vec_mod (nullifier p nk z) (cp_q p) = nullifier p nk z"
    unfolding nullifier_def commit_def
    using q_pos by (simp add: vec_mod_idemp)
  have commit_eq:
    "commit ck z (cp_q p) =
      vec_mod (vec_add a_commit (scalar_mult e c)) (cp_q p)"
    unfolding a_commit_def nullifier_sigma_sim_commit_def
    using vec_mod_sub_add_cancel_right[OF commit_len_eq q_pos commit_canonical]
    by simp
  have nullifier_eq:
    "nullifier p nk z =
      vec_mod (vec_add a_nullifier (scalar_mult e nf)) (cp_q p)"
    unfolding a_nullifier_def nullifier_sigma_sim_nullifier_def
    using vec_mod_sub_add_cancel_right[OF nullifier_len_eq q_pos nullifier_canonical]
    by simp
  show ?thesis
    unfolding nullifier_sigma_verify_def
    using params_ok key_ok nf_key_ok c_valid nf_valid a_commit_valid a_nullifier_valid
          challenge_ok z_ok commit_eq nullifier_eq
    by simp
qed

lemma nullifier_scheduled_sim_a_commits_nth:
  assumes len_eq: "length es = length zs"
      and i_lt: "i < length es"
  shows "nullifier_scheduled_sim_a_commits p ck c es zs ! i =
         nullifier_sigma_sim_commit p ck c (es ! i) (zs ! i)"
  using assms
  unfolding nullifier_scheduled_sim_a_commits_def
  by simp

lemma nullifier_scheduled_sim_a_nullifiers_nth:
  assumes len_eq: "length es = length zs"
      and i_lt: "i < length es"
  shows "nullifier_scheduled_sim_a_nullifiers p nk nf es zs ! i =
         nullifier_sigma_sim_nullifier p nk nf (es ! i) (zs ! i)"
  using assms
  unfolding nullifier_scheduled_sim_a_nullifiers_def
  by simp

lemma nullifier_scheduled_simulate_verify:
  assumes params_ok: "valid_scalar_commit_params p"
      and key_ok: "valid_commit_key p ck"
      and nf_key_ok: "valid_commit_key p nk"
      and c_valid: "valid_commitment p c"
      and nf_valid: "valid_commitment p nf"
      and es_len: "length es = nullifier_fs_rounds"
      and zs_len: "length zs = nullifier_fs_rounds"
      and challenges_ok:
        "\<forall>i < nullifier_fs_rounds. valid_nullifier_challenge p (es ! i)"
      and responses_ok:
        "\<forall>i < nullifier_fs_rounds. valid_nullifier_response p gamma (es ! i) (zs ! i)"
  shows "nullifier_scheduled_verify p gamma ck nk c nf
           (nullifier_a_commits
             (nullifier_scheduled_simulate p ck nk c nf es zs))
           (nullifier_a_nullifiers
             (nullifier_scheduled_simulate p ck nk c nf es zs))
           es
           zs"
proof -
  have len_eq: "length es = length zs"
    using es_len zs_len by simp
  have commits_len:
    "length (nullifier_scheduled_sim_a_commits p ck c es zs) =
     nullifier_fs_rounds"
    using es_len zs_len
    unfolding nullifier_scheduled_sim_a_commits_def
    by simp
  have nullifiers_len:
    "length (nullifier_scheduled_sim_a_nullifiers p nk nf es zs) =
     nullifier_fs_rounds"
    using es_len zs_len
    unfolding nullifier_scheduled_sim_a_nullifiers_def
    by simp
  have sigma_ok:
    "\<forall>i < nullifier_fs_rounds.
      nullifier_sigma_verify p gamma ck nk c nf
        (nullifier_scheduled_sim_a_commits p ck c es zs ! i)
        (nullifier_scheduled_sim_a_nullifiers p nk nf es zs ! i)
        (es ! i)
        (zs ! i)"
  proof (intro allI impI)
    fix i
    assume i_lt: "i < nullifier_fs_rounds"
    have i_lt_es: "i < length es"
      using i_lt es_len by simp
    have a_commit_def:
      "nullifier_scheduled_sim_a_commits p ck c es zs ! i =
       nullifier_sigma_sim_commit p ck c (es ! i) (zs ! i)"
      using nullifier_scheduled_sim_a_commits_nth[OF len_eq i_lt_es] .
    have a_nullifier_def:
      "nullifier_scheduled_sim_a_nullifiers p nk nf es zs ! i =
       nullifier_sigma_sim_nullifier p nk nf (es ! i) (zs ! i)"
      using nullifier_scheduled_sim_a_nullifiers_nth[OF len_eq i_lt_es] .
    show "nullifier_sigma_verify p gamma ck nk c nf
            (nullifier_scheduled_sim_a_commits p ck c es zs ! i)
            (nullifier_scheduled_sim_a_nullifiers p nk nf es zs ! i)
            (es ! i)
            (zs ! i)"
      using nullifier_sigma_simulate_verify[
        OF params_ok key_ok nf_key_ok c_valid nf_valid
           challenges_ok[rule_format, OF i_lt]
           responses_ok[rule_format, OF i_lt]
           a_commit_def a_nullifier_def]
      .
  qed
  show ?thesis
    unfolding nullifier_scheduled_simulate_def nullifier_scheduled_verify_def
    using es_len commits_len nullifiers_len zs_len sigma_ok
    by simp
qed

lemma nullifier_scheduled_verify_imp_fs_verify_if_challenges_match:
  assumes scheduled:
        "nullifier_scheduled_verify p gamma ck nk c nf
          (nullifier_a_commits proof) (nullifier_a_nullifiers proof) es zs"
      and z_msgs_len: "length (nullifier_z_msgs proof) = nullifier_fs_rounds"
      and z_rands_len: "length (nullifier_z_rands proof) = nullifier_fs_rounds"
      and zs_match:
        "zs =
          map (\<lambda>i. \<lparr> open_msg = nullifier_z_msgs proof ! i,
                       open_rand = nullifier_z_rands proof ! i \<rparr>)
            [0..<nullifier_fs_rounds]"
      and challenge_match:
        "nullifier_fs_challenges p ck nk c nf
          (nullifier_a_commits proof) (nullifier_a_nullifiers proof) = es"
  shows "nullifier_fs_verify p gamma ck nk c nf proof"
proof -
  have commits_len: "length (nullifier_a_commits proof) = nullifier_fs_rounds"
    using scheduled unfolding nullifier_scheduled_verify_def by simp
  have nullifiers_len: "length (nullifier_a_nullifiers proof) = nullifier_fs_rounds"
    using scheduled unfolding nullifier_scheduled_verify_def by simp
  have sigma_ok:
    "\<forall>i < nullifier_fs_rounds.
      nullifier_sigma_verify p gamma ck nk c nf
        (nullifier_a_commits proof ! i)
        (nullifier_a_nullifiers proof ! i)
        (nullifier_fs_challenges p ck nk c nf
          (nullifier_a_commits proof) (nullifier_a_nullifiers proof) ! i)
        \<lparr> open_msg = nullifier_z_msgs proof ! i,
          open_rand = nullifier_z_rands proof ! i \<rparr>"
  proof (intro allI impI)
    fix i
    assume i_lt: "i < nullifier_fs_rounds"
    have zs_i:
      "zs ! i =
       \<lparr> open_msg = nullifier_z_msgs proof ! i,
         open_rand = nullifier_z_rands proof ! i \<rparr>"
      using zs_match i_lt by simp
    have sigma:
      "nullifier_sigma_verify p gamma ck nk c nf
        (nullifier_a_commits proof ! i)
        (nullifier_a_nullifiers proof ! i)
        (es ! i)
        (zs ! i)"
      using scheduled i_lt unfolding nullifier_scheduled_verify_def by simp
    show "nullifier_sigma_verify p gamma ck nk c nf
            (nullifier_a_commits proof ! i)
            (nullifier_a_nullifiers proof ! i)
            (nullifier_fs_challenges p ck nk c nf
              (nullifier_a_commits proof) (nullifier_a_nullifiers proof) ! i)
            \<lparr> open_msg = nullifier_z_msgs proof ! i,
              open_rand = nullifier_z_rands proof ! i \<rparr>"
      using sigma zs_i challenge_match by simp
  qed
  show ?thesis
    unfolding nullifier_fs_verify_def Let_def
    using commits_len nullifiers_len z_msgs_len z_rands_len sigma_ok
    by simp
qed

lemma nullifier_fs_verify_scheduled_simulate_if_challenges_match:
  assumes params_ok: "valid_scalar_commit_params p"
      and key_ok: "valid_commit_key p ck"
      and nf_key_ok: "valid_commit_key p nk"
      and c_valid: "valid_commitment p c"
      and nf_valid: "valid_commitment p nf"
      and es_len: "length es = nullifier_fs_rounds"
      and zs_len: "length zs = nullifier_fs_rounds"
      and challenges_ok:
        "\<forall>i < nullifier_fs_rounds. valid_nullifier_challenge p (es ! i)"
      and responses_ok:
        "\<forall>i < nullifier_fs_rounds. valid_nullifier_response p gamma (es ! i) (zs ! i)"
      and challenge_match:
        "nullifier_fs_challenges p ck nk c nf
          (nullifier_a_commits
            (nullifier_scheduled_simulate p ck nk c nf es zs))
          (nullifier_a_nullifiers
            (nullifier_scheduled_simulate p ck nk c nf es zs)) = es"
  shows "nullifier_fs_verify p gamma ck nk c nf
           (nullifier_scheduled_simulate p ck nk c nf es zs)"
proof -
  let ?proof = "nullifier_scheduled_simulate p ck nk c nf es zs"
  have scheduled:
    "nullifier_scheduled_verify p gamma ck nk c nf
      (nullifier_a_commits ?proof) (nullifier_a_nullifiers ?proof) es zs"
    using nullifier_scheduled_simulate_verify[
      OF params_ok key_ok nf_key_ok c_valid nf_valid es_len zs_len
         challenges_ok responses_ok] .
  have z_msgs_len: "length (nullifier_z_msgs ?proof) = nullifier_fs_rounds"
    using zs_len unfolding nullifier_scheduled_simulate_def by simp
  have z_rands_len: "length (nullifier_z_rands ?proof) = nullifier_fs_rounds"
    using zs_len unfolding nullifier_scheduled_simulate_def by simp
  have zs_match:
    "zs =
      map (\<lambda>i. \<lparr> open_msg = nullifier_z_msgs ?proof ! i,
                   open_rand = nullifier_z_rands ?proof ! i \<rparr>)
        [0..<nullifier_fs_rounds]"
  proof (rule sym, rule nth_equalityI)
    show "length
            (map (\<lambda>i. \<lparr> open_msg = nullifier_z_msgs ?proof ! i,
                         open_rand = nullifier_z_rands ?proof ! i \<rparr>)
              [0..<nullifier_fs_rounds]) = length zs"
      using zs_len by simp
  next
    fix i
    assume i_lt:
      "i < length
            (map (\<lambda>i. \<lparr> open_msg = nullifier_z_msgs ?proof ! i,
                         open_rand = nullifier_z_rands ?proof ! i \<rparr>)
              [0..<nullifier_fs_rounds])"
    then have i_lt_rounds: "i < nullifier_fs_rounds"
      by simp
    then have i_lt_zs: "i < length zs"
      using zs_len by simp
    show "map (\<lambda>i. \<lparr> open_msg = nullifier_z_msgs ?proof ! i,
                    open_rand = nullifier_z_rands ?proof ! i \<rparr>)
             [0..<nullifier_fs_rounds] ! i = zs ! i"
      using i_lt_rounds i_lt_zs
      unfolding nullifier_scheduled_simulate_def
      by simp
  qed
  show ?thesis
    using nullifier_scheduled_verify_imp_fs_verify_if_challenges_match[
      OF scheduled z_msgs_len z_rands_len zs_match challenge_match] .
qed

lemma nullifier_response_valid:
  assumes params_ok: "valid_scalar_commit_params p"
      and mask_ok: "valid_nullifier_mask p gamma y"
      and challenge_ok: "valid_nullifier_challenge p e"
      and witness_ok: "valid_opening p op"
  shows "valid_nullifier_response p gamma e (nullifier_sigma_respond op y e)"
proof -
  have msg_len:
    "length (open_msg y) = length (open_msg (opening_scale e op))"
    using mask_ok witness_ok
    unfolding valid_nullifier_mask_def opening_scale_def
    by (simp add: valid_opening_msg_len valid_vec_def scalar_mult_length)
  have rand_len:
    "length (open_rand y) = length (open_rand (opening_scale e op))"
    using mask_ok witness_ok
    unfolding valid_nullifier_mask_def opening_scale_def
    by (simp add: valid_opening_rand_len valid_vec_def scalar_mult_length)
  have msg_bound_y: "all_bounded (open_msg y) gamma"
    using mask_ok unfolding valid_nullifier_mask_def by simp
  have rand_bound_y: "all_bounded (open_rand y) gamma"
    using mask_ok unfolding valid_nullifier_mask_def by simp
  have msg_bound_scaled:
    "all_bounded (open_msg (opening_scale e op)) (abs e * cp_beta p)"
    using valid_opening_msg_bounded[OF witness_ok]
    unfolding opening_scale_def
    by (auto intro: scalar_mult_bounded)
  have rand_bound_scaled:
    "all_bounded (open_rand (opening_scale e op)) (abs e * cp_beta p)"
    using valid_opening_rand_bounded[OF witness_ok]
    unfolding opening_scale_def
    by (auto intro: scalar_mult_bounded)
  have msg_bound:
    "all_bounded
       (vec_add (open_msg y) (open_msg (opening_scale e op)))
       (nullifier_response_bound p gamma e)"
    using vec_add_bounded[OF msg_bound_y msg_bound_scaled msg_len]
    unfolding nullifier_response_bound_def by simp
  have rand_bound:
    "all_bounded
       (vec_add (open_rand y) (open_rand (opening_scale e op)))
       (nullifier_response_bound p gamma e)"
    using vec_add_bounded[OF rand_bound_y rand_bound_scaled rand_len]
    unfolding nullifier_response_bound_def by simp
  have msg_valid:
    "valid_vec (vec_add (open_msg y) (open_msg (opening_scale e op))) (cp_n1 p)"
    using mask_ok witness_ok msg_len
    unfolding valid_nullifier_mask_def valid_vec_def opening_scale_def
    by (simp add: vec_add_length valid_opening_msg_len scalar_mult_length)
  have rand_valid:
    "valid_vec (vec_add (open_rand y) (open_rand (opening_scale e op))) (cp_n2 p)"
    using mask_ok witness_ok rand_len
    unfolding valid_nullifier_mask_def valid_vec_def opening_scale_def
    by (simp add: vec_add_length valid_opening_rand_len scalar_mult_length)
  show ?thesis
    using msg_valid rand_valid msg_bound rand_bound challenge_ok
    unfolding valid_nullifier_response_def nullifier_sigma_respond_def opening_add_def by simp
qed

lemma nullifier_deterministic:
  assumes rel1: "nullifier_relation p ck nk c nf1 op"
      and rel2: "nullifier_relation p ck nk c nf2 op"
  shows "nf1 = nf2"
  using rel1 rel2 unfolding nullifier_relation_def by simp

lemma nullifier_sigma_complete:
  assumes relation: "nullifier_relation_wellformed p ck nk c nf op"
      and mask_ok: "valid_nullifier_mask p gamma y"
      and challenge_ok: "valid_nullifier_challenge p e"
      and a_commit_def: "a_commit = commit ck y (cp_q p)"
      and a_nf_def: "a_nf = nullifier p nk y"
      and z_def: "z = nullifier_sigma_respond op y e"
  shows "nullifier_sigma_verify p gamma ck nk c nf a_commit a_nf e z"
proof -
  obtain params_ok key_ok nf_key_ok open_ok nf_eq where
      relation_props:
        "valid_scalar_commit_params p"
        "valid_commit_key p ck"
        "valid_commit_key p nk"
        "verify_opening p ck c op"
        "nullifier p nk op = nf"
    using relation unfolding nullifier_relation_wellformed_def by blast
  have key_ok: "valid_commit_key p ck"
    using relation_props(2) .
  have nf_key_ok: "valid_commit_key p nk"
    using relation_props(3) .
  have open_valid: "valid_opening p op"
    using relation_props(4) by (rule verify_opening_valid)
  have c_valid: "valid_commitment p c"
    using relation_props(4) relation_props(1)
          commit_valid[OF valid_scalar_commit_params_props(1)[OF relation_props(1)] key_ok open_valid]
          verify_opening_eq[OF relation_props(4)]
    by simp
  have nf_valid: "valid_commitment p nf"
    using nullifier_valid[OF relation_props(1) nf_key_ok open_valid]
          relation_props(5)
    by simp
  have mask_msg_ok: "valid_vec (open_msg y) (cp_n1 p)"
    using mask_ok unfolding valid_nullifier_mask_def by simp
  have mask_rand_ok: "valid_vec (open_rand y) (cp_n2 p)"
    using mask_ok unfolding valid_nullifier_mask_def by simp
  have a_commit_valid:
    "valid_commitment p a_commit"
    using commit_shape_valid[OF valid_scalar_commit_params_props(1)[OF relation_props(1)] key_ok
            mask_msg_ok mask_rand_ok]
          a_commit_def by simp
  have a_nf_valid:
    "valid_commitment p a_nf"
    unfolding a_nf_def nullifier_def
    using commit_shape_valid[OF valid_scalar_commit_params_props(1)[OF relation_props(1)] nf_key_ok
            mask_msg_ok mask_rand_ok]
    by simp
  have z_valid:
    "valid_nullifier_response p gamma e z"
  proof -
    show ?thesis
      using nullifier_response_valid[OF relation_props(1) mask_ok challenge_ok open_valid]
            z_def
      by simp
  qed
  have commit_eq:
    "commit ck z (cp_q p) =
      vec_mod (vec_add a_commit (scalar_mult e c)) (cp_q p)"
  proof -
    have msg_len:
      "length (open_msg y) = length (open_msg (opening_scale e op))"
      using mask_ok open_valid
      unfolding valid_nullifier_mask_def opening_scale_def
      by (simp add: valid_opening_msg_len valid_vec_def scalar_mult_length)
    have rand_len:
      "length (open_rand y) = length (open_rand (opening_scale e op))"
      using mask_ok open_valid
      unfolding valid_nullifier_mask_def opening_scale_def
      by (simp add: valid_opening_rand_len valid_vec_def scalar_mult_length)
    have q_pos: "cp_q p > 0"
      using valid_scalar_commit_params_props(5)[OF relation_props(1)] by linarith
    have len_a_commit: "length a_commit = cp_m p"
      using a_commit_valid unfolding valid_commitment_def valid_vec_def by simp
    have len_c: "length c = cp_m p"
      using c_valid unfolding valid_commitment_def valid_vec_def by simp
    have a_commit_mod: "vec_mod a_commit (cp_q p) = a_commit"
      using a_commit_def q_pos unfolding commit_def by (simp add: vec_mod_idemp)
    have "commit ck z (cp_q p) =
          commit ck (nullifier_sigma_respond op y e) (cp_q p)"
      using z_def by simp
    also have "... =
          vec_mod (vec_add (commit ck y (cp_q p)) (commit ck (opening_scale e op) (cp_q p))) (cp_q p)"
      unfolding nullifier_sigma_respond_def
      using commit_add_hom[OF msg_len rand_len] q_pos by simp
    also have "... =
          vec_mod (vec_add a_commit (vec_mod (scalar_mult e (commit ck op (cp_q p))) (cp_q p))) (cp_q p)"
      using a_commit_def commit_scale_hom[OF q_pos, of ck e op] by simp
    also have "... = vec_mod (vec_add a_commit (scalar_mult e c)) (cp_q p)"
      using verify_opening_eq[OF relation_props(4)]
            vec_mod_add_eq[OF _ q_pos, of a_commit "scalar_mult e c"]
            len_a_commit len_c a_commit_mod
      by (simp add: scalar_mult_length)
    finally show ?thesis .
  qed
  have nullifier_eq:
    "nullifier p nk z =
      vec_mod (vec_add a_nf (scalar_mult e nf)) (cp_q p)"
  proof -
    have msg_len:
      "length (open_msg y) = length (open_msg (opening_scale e op))"
      using mask_ok open_valid
      unfolding valid_nullifier_mask_def opening_scale_def
      by (simp add: valid_opening_msg_len valid_vec_def scalar_mult_length)
    have rand_len:
      "length (open_rand y) = length (open_rand (opening_scale e op))"
      using mask_ok open_valid
      unfolding valid_nullifier_mask_def opening_scale_def
      by (simp add: valid_opening_rand_len valid_vec_def scalar_mult_length)
    have q_pos: "cp_q p > 0"
      using valid_scalar_commit_params_props(5)[OF relation_props(1)] by linarith
    have len_a_nf: "length a_nf = cp_m p"
      using a_nf_valid unfolding valid_commitment_def valid_vec_def by simp
    have len_nf: "length nf = cp_m p"
      using nf_valid unfolding valid_commitment_def valid_vec_def by simp
    have a_nf_mod: "vec_mod a_nf (cp_q p) = a_nf"
      using a_nf_def q_pos unfolding nullifier_def commit_def by (simp add: vec_mod_idemp)
    have "nullifier p nk z =
          nullifier p nk (nullifier_sigma_respond op y e)"
      using z_def by simp
    also have "... =
          vec_mod (vec_add (commit nk y (cp_q p)) (commit nk (opening_scale e op) (cp_q p))) (cp_q p)"
      unfolding nullifier_def
      unfolding nullifier_sigma_respond_def
      using commit_add_hom[OF msg_len rand_len] q_pos by simp
    also have "... =
          vec_mod (vec_add (nullifier p nk y) (commit nk (opening_scale e op) (cp_q p))) (cp_q p)"
      unfolding nullifier_def by simp
    also have "... =
          vec_mod (vec_add a_nf (vec_mod (scalar_mult e (commit nk op (cp_q p))) (cp_q p))) (cp_q p)"
      using a_nf_def commit_scale_hom[OF q_pos, of nk e op] by simp
    also have "... = vec_mod (vec_add a_nf (scalar_mult e nf)) (cp_q p)"
      using relation_props(5)
            vec_mod_add_eq[OF _ q_pos, of a_nf "scalar_mult e nf"]
            len_a_nf len_nf a_nf_mod
      unfolding nullifier_def
      by (simp add: scalar_mult_length)
    finally show ?thesis .
  qed
  show ?thesis
    unfolding nullifier_sigma_verify_def
    using relation_props c_valid nf_valid a_commit_valid a_nf_valid challenge_ok z_valid commit_eq nullifier_eq
    by auto
qed

lemma nullifier_fs_complete:
  assumes proof_def: "nullifier_fs_prove p gamma ck nk c nf op ys = Some proof"
  shows "nullifier_fs_verify p gamma ck nk c nf proof"
proof -
  obtain a_commits a_nullifiers es zs where
      a_commits_def: "a_commits = map (\<lambda>y. commit ck y (cp_q p)) ys"
      and a_nullifiers_def: "a_nullifiers = map (\<lambda>y. nullifier p nk y) ys"
      and es_def: "es = nullifier_fs_challenges p ck nk c nf a_commits a_nullifiers"
      and zs_def: "zs = nullifier_sigma_responses op ys es"
      and relation: "nullifier_relation_wellformed p ck nk c nf op"
      and ys_len: "length ys = nullifier_fs_rounds"
      and masks_ok: "\<forall>i < nullifier_fs_rounds. valid_nullifier_mask p gamma (ys ! i)"
      and zs_valid: "\<forall>i < nullifier_fs_rounds. valid_nullifier_response p gamma (es ! i) (zs ! i)"
      and proof_eq:
        "proof =
          \<lparr> nullifier_a_commits = a_commits,
            nullifier_a_nullifiers = a_nullifiers,
            nullifier_z_msgs = map open_msg zs,
            nullifier_z_rands = map open_rand zs \<rparr>"
    using proof_def
    unfolding nullifier_fs_prove_def Let_def
    by (auto split: if_splits)
  have params_ok: "valid_scalar_commit_params p"
    using relation unfolding nullifier_relation_wellformed_def by simp
  have es_len: "length es = nullifier_fs_rounds"
    using es_def by (simp add: nullifier_fs_challenges_length)
  have a_commits_len: "length a_commits = nullifier_fs_rounds"
    using a_commits_def ys_len by simp
  have a_nullifiers_len: "length a_nullifiers = nullifier_fs_rounds"
    using a_nullifiers_def ys_len by simp
  have ys_es_len: "length ys = length es"
    using ys_len es_len by simp
  have zs_len: "length zs = nullifier_fs_rounds"
    using nullifier_sigma_responses_length[OF ys_es_len] zs_def ys_len by simp
  have sigma_ok:
    "\<forall>i < nullifier_fs_rounds.
      nullifier_sigma_verify p gamma ck nk c nf
        (a_commits ! i)
        (a_nullifiers ! i)
        (es ! i)
        (zs ! i)"
  proof (intro allI impI)
    fix i
    assume i_lt: "i < nullifier_fs_rounds"
    have i_lt_ys: "i < length ys"
      using i_lt ys_len by simp
    have challenge_ok: "valid_nullifier_challenge p (es ! i)"
      using nullifier_fs_challenge_valid[OF params_ok i_lt]
      unfolding es_def .
    have mask_ok: "valid_nullifier_mask p gamma (ys ! i)"
      using masks_ok i_lt by simp
    have a_commit_i: "a_commits ! i = commit ck (ys ! i) (cp_q p)"
      using i_lt ys_len a_commits_def by simp
    have a_nf_i: "a_nullifiers ! i = nullifier p nk (ys ! i)"
      using i_lt ys_len a_nullifiers_def by simp
    have z_round:
      "nullifier_sigma_responses op ys es ! i =
       nullifier_sigma_respond op (ys ! i) (es ! i)"
      using nullifier_sigma_responses_nth[OF ys_es_len i_lt_ys] .
    have z_def: "zs ! i = nullifier_sigma_respond op (ys ! i) (es ! i)"
      using z_round
      unfolding zs_def
      by simp
    have sigma_ok_i:
      "nullifier_sigma_verify p gamma ck nk c nf
         (commit ck (ys ! i) (cp_q p))
         (nullifier p nk (ys ! i))
         (es ! i)
         (zs ! i)"
    proof (rule nullifier_sigma_complete[OF relation mask_ok challenge_ok])
      show "commit ck (ys ! i) (cp_q p) = commit ck (ys ! i) (cp_q p)"
        by simp
      show "nullifier p nk (ys ! i) = nullifier p nk (ys ! i)"
        by simp
      show "zs ! i = nullifier_sigma_respond op (ys ! i) (es ! i)"
        using z_def .
    qed
    show "nullifier_sigma_verify p gamma ck nk c nf
            (a_commits ! i) (a_nullifiers ! i) (es ! i) (zs ! i)"
      using sigma_ok_i a_commit_i a_nf_i by simp
  qed
  have sigma_ok_proof:
    "\<forall>i < nullifier_fs_rounds.
      nullifier_sigma_verify p gamma ck nk c nf
        (a_commits ! i)
        (a_nullifiers ! i)
        (es ! i)
        \<lparr> open_msg = nullifier_z_msgs proof ! i,
          open_rand = nullifier_z_rands proof ! i \<rparr>"
  proof (intro allI impI)
    fix i
    assume i_lt: "i < nullifier_fs_rounds"
    have msg_eq: "nullifier_z_msgs proof ! i = open_msg (zs ! i)"
      using proof_eq i_lt zs_len by simp
    have rand_eq: "nullifier_z_rands proof ! i = open_rand (zs ! i)"
      using proof_eq i_lt zs_len by simp
    have z_rebuild: "\<lparr>open_msg = open_msg (zs ! i), open_rand = open_rand (zs ! i)\<rparr> = zs ! i"
      by (cases "zs ! i") simp
    have z_proof_eq:
      "\<lparr> open_msg = nullifier_z_msgs proof ! i,
         open_rand = nullifier_z_rands proof ! i \<rparr> = zs ! i"
      using msg_eq rand_eq z_rebuild by simp
    show "nullifier_sigma_verify p gamma ck nk c nf
            (a_commits ! i)
            (a_nullifiers ! i)
            (es ! i)
            \<lparr> open_msg = nullifier_z_msgs proof ! i,
              open_rand = nullifier_z_rands proof ! i \<rparr>"
      using sigma_ok[rule_format, OF i_lt] z_proof_eq
      by simp
  qed
  show ?thesis
    unfolding nullifier_fs_verify_def
    using proof_eq a_commits_len a_nullifiers_len zs_len sigma_ok_proof
    by (simp add: es_def)
qed

lemma membership_prove_complete:
  assumes prove_def: "membership_prove p ledger c = Some mp"
  shows "membership_verify p c mp"
proof -
  obtain i sibs where
      idx_def: "membership_index_of ledger c = Some i"
      and sibs_def: "membership_siblings p ledger i = Some sibs"
      and mp_def:
        "mp =
          \<lparr> member_index = i,
            member_root = ledger_root p ledger,
            member_siblings = sibs,
            member_directions = index_directions (length sibs) i \<rparr>"
    using prove_def
    unfolding membership_prove_def
    by (auto split: option.splits)
  have idx_lt: "i < length ledger"
    using idx_def
  proof (induct ledger arbitrary: i)
    case Nil
    then show ?case by simp
  next
    case (Cons x xs)
    show ?case
    proof (cases "x = c")
      case True
      with Cons.prems show ?thesis by simp
    next
      case False
      then obtain j where "membership_index_of xs c = Some j" "i = Suc j"
        using Cons.prems by (cases "membership_index_of xs c") auto
      then show ?thesis
        using Cons.hyps by simp
    qed
  qed
  have nth_eq: "ledger ! i = c"
    using idx_def
  proof (induct ledger arbitrary: i)
    case Nil
    then show ?case by simp
  next
    case (Cons x xs)
    show ?case
    proof (cases "x = c")
      case True
      with Cons.prems show ?thesis by simp
    next
      case False
      then obtain j where j_def: "membership_index_of xs c = Some j" "i = Suc j"
        using Cons.prems by (cases "membership_index_of xs c") auto
      then show ?thesis
        using Cons.hyps by simp
    qed
  qed
  have root_eq:
    "auth_path_root p c sibs (index_directions (length sibs) i) = ledger_root p ledger"
    using membership_siblings_root[OF sibs_def] idx_lt nth_eq by simp
  show ?thesis
    unfolding membership_verify_def mp_def
    using root_eq by simp
qed

lemma membership_index_of_in_bounds:
  assumes "membership_index_of ledger c = Some i"
  shows "i < length ledger"
  using assms
proof (induct ledger arbitrary: i)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  show ?case
  proof (cases "x = c")
    case True
    then show ?thesis using Cons.prems by simp
  next
    case False
    then obtain j where "membership_index_of xs c = Some j" "i = Suc j"
      using Cons.prems by (cases "membership_index_of xs c") auto
    then show ?thesis
      using Cons.hyps by simp
  qed
qed

lemma membership_index_of_nth:
  assumes "membership_index_of ledger c = Some i"
  shows "ledger ! i = c"
  using assms
proof (induct ledger arbitrary: i)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  show ?case
  proof (cases "x = c")
    case True
    then show ?thesis using Cons.prems by simp
  next
    case False
    then obtain j where "membership_index_of xs c = Some j" "i = Suc j"
      using Cons.prems by (cases "membership_index_of xs c") auto
    then show ?thesis
      using Cons.hyps by simp
  qed
qed

lemma membership_verify_in_set:
  assumes "membership_prove p ledger c = Some proof"
  shows "c \<in> set ledger"
proof -
  obtain i sibs where
      idx_def: "membership_index_of ledger c = Some i"
    using assms unfolding membership_prove_def by (auto split: option.splits)
  have "i < length ledger"
    using membership_index_of_in_bounds[OF idx_def] .
  moreover have "ledger ! i = c"
    using membership_index_of_nth[OF idx_def] .
  ultimately show ?thesis
    by (metis nth_mem)
qed

lemma remove1_set_subset:
  "set (remove1 x xs) \<subseteq> set xs"
  by (induct xs) auto

lemma membership_index_of_exists:
  assumes "c \<in> set ledger"
  shows "\<exists>i. membership_index_of ledger c = Some i"
  using assms
proof (induct ledger)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  show ?case
  proof (cases "x = c")
    case True
    then show ?thesis by simp
  next
    case False
    have "c \<in> set xs"
      using Cons.prems False by simp
    then obtain i where "membership_index_of xs c = Some i"
      using Cons.hyps by blast
    then show ?thesis
      using False by simp
  qed
qed

lemma membership_exists:
  assumes "c \<in> set ledger"
  shows "\<exists>mp. membership_prove p ledger c = Some mp"
proof -
  obtain i where "membership_index_of ledger c = Some i"
    using membership_index_of_exists[OF assms] by blast
  have idx_lt: "i < length ledger"
    using membership_index_of_in_bounds[OF \<open>membership_index_of ledger c = Some i\<close>] .
  then obtain sibs where sibs_def: "membership_siblings p ledger i = Some sibs"
    using membership_siblings_exists by blast
  then show ?thesis
    unfolding membership_prove_def
    using \<open>membership_index_of ledger c = Some i\<close> sibs_def by auto
qed

lemma commitment_ledger_length:
  "length (commitment_ledger notes) = length notes"
  unfolding commitment_ledger_def by simp

lemma ledger_note_at_commitment:
  assumes prove_def: "membership_prove p (commitment_ledger notes) c = Some mp"
  shows "note_commitment (ledger_note_at notes mp) = c"
proof -
  obtain i sibs where
      idx_def: "membership_index_of (commitment_ledger notes) c = Some i"
      and mp_def:
        "mp =
          \<lparr> member_index = i,
            member_root = ledger_root p (commitment_ledger notes),
            member_siblings = sibs,
            member_directions = index_directions (length sibs) i \<rparr>"
    using prove_def
    unfolding membership_prove_def
    by (auto split: option.splits)
  have idx_lt: "i < length notes"
    using membership_index_of_in_bounds[OF idx_def]
    by (simp add: commitment_ledger_length)
  have nth_eq: "commitment_ledger notes ! i = c"
    using membership_index_of_nth[OF idx_def] .
  show ?thesis
  proof -
    have "map note_commitment notes ! i = c"
      using nth_eq unfolding commitment_ledger_def by simp
    then have "note_commitment (notes ! i) = c"
      using idx_lt by simp
    then show ?thesis
      unfolding ledger_note_at_def mp_def by simp
  qed
qed

lemma ledger_note_at_in_set:
  assumes prove_def: "membership_prove p (commitment_ledger notes) c = Some mp"
  shows "ledger_note_at notes mp \<in> set notes"
proof -
  obtain i sibs where
      idx_def: "membership_index_of (commitment_ledger notes) c = Some i"
      and mp_def:
        "mp =
          \<lparr> member_index = i,
            member_root = ledger_root p (commitment_ledger notes),
            member_siblings = sibs,
            member_directions = index_directions (length sibs) i \<rparr>"
    using prove_def
    unfolding membership_prove_def
    by (auto split: option.splits)
  have idx_lt: "i < length notes"
    using membership_index_of_in_bounds[OF idx_def]
    by (simp add: commitment_ledger_length)
  show ?thesis
    unfolding ledger_note_at_def mp_def
    using idx_lt nth_mem by simp
qed

lemma transaction_fs_complete:
  assumes proof_def:
    "transaction_fs_prove p gamma k ck nk ledger spent c_in1 c_in2 c_out1 c_out2 nf1 nf2
      op_in1 op_in2 op_out1 op_out2 out1_bits out1_comps out2_bits out2_comps
      y_in1 y_in2 y_balance y_out1_amounts y_out1_pairss y_out2_amounts y_out2_pairss = Some proof"
  shows "transaction_fs_verify p gamma k ck nk (ledger_root p ledger) spent
           c_in1 c_in2 c_out1 c_out2 nf1 nf2 proof"
proof -
  obtain member1 member2 nf_proof1 nf_proof2 bal_proof range1 range2 where
      member1_def: "membership_prove p ledger c_in1 = Some member1"
      and member2_def: "membership_prove p ledger c_in2 = Some member2"
      and nf1_def: "nullifier_fs_prove p gamma ck nk c_in1 nf1 op_in1 y_in1 = Some nf_proof1"
      and nf2_def: "nullifier_fs_prove p gamma ck nk c_in2 nf2 op_in2 y_in2 = Some nf_proof2"
      and bal_def:
        "balance_fs_prove p gamma ck
          (balance_commitment c_in1 c_in2 c_out1 c_out2 (cp_q p))
          (aggregate_randomness op_in1 op_in2 op_out1 op_out2) y_balance = Some bal_proof"
      and range1_def:
        "range_fs_prove p gamma k ck c_out1 op_out1 out1_bits out1_comps y_out1_amounts y_out1_pairss = Some range1"
      and range2_def:
        "range_fs_prove p gamma k ck c_out2 op_out2 out2_bits out2_comps y_out2_amounts y_out2_pairss = Some range2"
      and rel:
        "transaction_relation_wellformed p ck nk ledger spent c_in1 c_in2 c_out1 c_out2 nf1 nf2
          op_in1 op_in2 op_out1 op_out2 out1_bits out1_comps out2_bits out2_comps"
      and idx_ne: "member_index member1 \<noteq> member_index member2"
      and proof_eq:
        "proof =
          \<lparr> tx_in1_member = member1,
            tx_in2_member = member2,
            tx_in1_nullifier = nf_proof1,
            tx_in2_nullifier = nf_proof2,
            tx_balance = bal_proof,
            tx_out1_range = range1,
            tx_out2_range = range2 \<rparr>"
    using proof_def
    unfolding transaction_fs_prove_def
    by (auto split: option.splits if_splits)
  have member1_ok: "membership_verify p c_in1 member1"
    using membership_prove_complete[OF member1_def] .
  have member2_ok: "membership_verify p c_in2 member2"
    using membership_prove_complete[OF member2_def] .
  have root1_eq: "member_root member1 = ledger_root p ledger"
    using member1_def unfolding membership_prove_def
    by (auto split: option.splits)
  have root2_eq: "member_root member2 = ledger_root p ledger"
    using member2_def unfolding membership_prove_def
    by (auto split: option.splits)
  have nf1_ok: "nullifier_fs_verify p gamma ck nk c_in1 nf1 nf_proof1"
    using nullifier_fs_complete[OF nf1_def] .
  have nf2_ok: "nullifier_fs_verify p gamma ck nk c_in2 nf2 nf_proof2"
    using nullifier_fs_complete[OF nf2_def] .
  have bal_ok:
    "balance_fs_verify p gamma ck
      (balance_commitment c_in1 c_in2 c_out1 c_out2 (cp_q p))
      bal_proof"
    using balance_fs_complete[OF bal_def] .
  have range1_ok: "range_fs_verify p gamma k ck c_out1 range1"
    using range_fs_complete[OF range1_def] .
  have range2_ok: "range_fs_verify p gamma k ck c_out2 range2"
    using range_fs_complete[OF range2_def] .
  have spent_ok:
    "nf1 \<notin> set spent \<and> nf2 \<notin> set spent \<and> nf1 \<noteq> nf2"
    using rel unfolding transaction_relation_wellformed_def by simp
  have ck_ok: "valid_commit_key p ck"
    using rel unfolding transaction_relation_wellformed_def nullifier_relation_wellformed_def by blast
  have nk_ok: "valid_commit_key p nk"
    using rel unfolding transaction_relation_wellformed_def nullifier_relation_wellformed_def by blast
  show ?thesis
    unfolding transaction_fs_verify_def
    using ck_ok nk_ok member1_ok member2_ok root1_eq root2_eq idx_ne spent_ok nf1_ok nf2_ok bal_ok range1_ok range2_ok proof_eq
    by simp
qed

lemma ledger_reachable_snapshot_valid:
  assumes "ledger_reachable p gamma k ck nk notes0 spent0 notes spent"
  shows "ledger_valid p gamma k ck (ledger_root p (commitment_ledger notes)) notes spent"
  using assms
  by (induction rule: ledger_reachable.induct) (auto simp: ledger_step_semantic_def)

lemma ledger_reachable_invariant:
  assumes "ledger_reachable p gamma k ck nk notes0 spent0 notes spent"
  shows "ledger_valid p gamma k ck (ledger_root p (commitment_ledger notes)) notes spent"
  using ledger_reachable_snapshot_valid[OF assms] .

lemma ledger_snapshot_valid_after_transaction:
  assumes ledger_ok:
        "ledger_valid p gamma k ck (ledger_root p (commitment_ledger notes)) notes spent"
      and tx_prove:
        "transaction_fs_prove p gamma k ck nk (commitment_ledger notes) spent
          c_in1 c_in2 c_out1 c_out2 nf1 nf2
          op_in1 op_in2 op_out1 op_out2
          out1_bits out1_comps out2_bits out2_comps
          y_in1 y_in2 y_balance y_out1_amounts y_out1_pairss y_out2_amounts y_out2_pairss = Some proof"
  shows "ledger_valid p gamma k ck
           (ledger_root p (commitment_ledger (ledger_apply_notes notes proof c_out1 c_out2)))
           (ledger_apply_notes notes proof c_out1 c_out2)
           (ledger_apply_spent spent nf1 nf2)"
proof -
  have params_ok: "valid_scalar_commit_params p"
    using ledger_ok unfolding ledger_valid_def by simp
  have key_ok: "valid_commit_key p ck"
    using ledger_ok unfolding ledger_valid_def by simp
  have spent_distinct: "distinct spent"
    using ledger_ok unfolding ledger_valid_def by simp
  have tx_ok:
    "transaction_fs_verify p gamma k ck nk (ledger_root p (commitment_ledger notes)) spent
      c_in1 c_in2 c_out1 c_out2 nf1 nf2 proof"
    using transaction_fs_complete[OF tx_prove] .
  have idx_ne:
    "member_index (tx_in1_member proof) \<noteq> member_index (tx_in2_member proof)"
    using tx_ok unfolding transaction_fs_verify_def by simp
  have out1_ok: "range_fs_verify p gamma k ck c_out1 (tx_out1_range proof)"
    using tx_ok unfolding transaction_fs_verify_def by simp
  have out2_ok: "range_fs_verify p gamma k ck c_out2 (tx_out2_range proof)"
    using tx_ok unfolding transaction_fs_verify_def by simp
  have spent_fresh:
    "nf1 \<notin> set spent \<and> nf2 \<notin> set spent \<and> nf1 \<noteq> nf2"
    using tx_ok unfolding transaction_fs_verify_def by simp
  let ?note1 = "ledger_note_at notes (tx_in1_member proof)"
  let ?note2 = "ledger_note_at notes (tx_in2_member proof)"
  have note1_commit: "note_commitment ?note1 = c_in1"
    using tx_prove ledger_note_at_commitment
    unfolding transaction_fs_prove_def
    by (auto split: option.splits if_splits)
  have note2_commit: "note_commitment ?note2 = c_in2"
    using tx_prove ledger_note_at_commitment
    unfolding transaction_fs_prove_def
    by (auto split: option.splits if_splits)
  have note1_in: "?note1 \<in> set notes"
    using tx_prove ledger_note_at_in_set
    unfolding transaction_fs_prove_def
    by (auto split: option.splits if_splits)
  have note2_in: "?note2 \<in> set notes"
    using tx_prove ledger_note_at_in_set
    unfolding transaction_fs_prove_def
    by (auto split: option.splits if_splits)
  have remaining_subset:
    "set (remove1 ?note2 (remove1 ?note1 notes)) \<subseteq> set notes"
    using remove1_set_subset[where x = ?note2 and xs = "remove1 ?note1 notes"]
          remove1_set_subset[where x = ?note1 and xs = "notes"]
    by blast
  have old_notes_ok:
    "\<forall>note \<in> set (remove1 ?note2 (remove1 ?note1 notes)).
      range_fs_verify p gamma k ck (note_commitment note) (note_range_proof note)"
    using ledger_ok remaining_subset unfolding ledger_valid_def by blast
  have spent_distinct':
    "distinct (ledger_apply_spent spent nf1 nf2)"
    using spent_distinct spent_fresh
    unfolding ledger_apply_spent_def by auto
  show ?thesis
    unfolding ledger_valid_def ledger_apply_notes_def ledger_apply_spent_def Let_def
  proof (intro conjI ballI)
    show "valid_scalar_commit_params p"
      using params_ok .
    show "valid_commit_key p ck"
      using key_ok .
    show "ledger_root p
        (commitment_ledger
          (\<lparr>note_commitment = c_out1, note_range_proof = tx_out1_range proof\<rparr> #
           \<lparr>note_commitment = c_out2, note_range_proof = tx_out2_range proof\<rparr> #
           remove1 ?note2 (remove1 ?note1 notes))) =
      ledger_root p
        (commitment_ledger
          (\<lparr>note_commitment = c_out1, note_range_proof = tx_out1_range proof\<rparr> #
           \<lparr>note_commitment = c_out2, note_range_proof = tx_out2_range proof\<rparr> #
           remove1 ?note2 (remove1 ?note1 notes)))"
      by simp
    show "distinct (nf1 # nf2 # spent)"
      using spent_distinct' unfolding ledger_apply_spent_def .
    fix n
    assume note_in:
      "n \<in> set
        (\<lparr>note_commitment = c_out1, note_range_proof = tx_out1_range proof\<rparr> #
         \<lparr>note_commitment = c_out2, note_range_proof = tx_out2_range proof\<rparr> #
         remove1 ?note2 (remove1 ?note1 notes))"
    then have note_cases:
      "n = \<lparr>note_commitment = c_out1, note_range_proof = tx_out1_range proof\<rparr> \<or>
       n = \<lparr>note_commitment = c_out2, note_range_proof = tx_out2_range proof\<rparr> \<or>
       n \<in> set (remove1 ?note2 (remove1 ?note1 notes))"
      by auto
    then show "range_fs_verify p gamma k ck (note_commitment n) (note_range_proof n)"
    proof
      assume "n = \<lparr>note_commitment = c_out1, note_range_proof = tx_out1_range proof\<rparr>"
      then show ?thesis using out1_ok by simp
    next
      assume rest:
        "n = \<lparr>note_commitment = c_out2, note_range_proof = tx_out2_range proof\<rparr> \<or>
         n \<in> set (remove1 ?note2 (remove1 ?note1 notes))"
      then show ?thesis
      proof
        assume "n = \<lparr>note_commitment = c_out2, note_range_proof = tx_out2_range proof\<rparr>"
        then show ?thesis using out2_ok by simp
      next
        assume "n \<in> set (remove1 ?note2 (remove1 ?note1 notes))"
        then show ?thesis
          using old_notes_ok by blast
      qed
    qed
  qed
qed

lemma ledger_step_semantic_after_transaction:
  assumes ledger_ok:
        "ledger_valid p gamma k ck (ledger_root p (commitment_ledger notes)) notes spent"
      and tx_prove:
        "transaction_fs_prove p gamma k ck nk (commitment_ledger notes) spent
          c_in1 c_in2 c_out1 c_out2 nf1 nf2
          op_in1 op_in2 op_out1 op_out2
          out1_bits out1_comps out2_bits out2_comps
          y_in1 y_in2 y_balance y_out1_amounts y_out1_pairss y_out2_amounts y_out2_pairss = Some proof"
      and tx_relation:
        "transaction_relation p ck nk (commitment_ledger notes) spent
          c_in1 c_in2 c_out1 c_out2 nf1 nf2
          op_in1 op_in2 op_out1 op_out2 out1_bits out1_comps out2_bits out2_comps"
  shows "ledger_step_semantic p gamma k ck nk notes spent
           c_in1 c_in2 c_out1 c_out2 nf1 nf2 proof
           (ledger_apply_notes notes proof c_out1 c_out2)
           (ledger_apply_spent spent nf1 nf2)"
proof -
  obtain member1 member2 nf_proof1 nf_proof2 bal_proof range1 range2 where
      member1_def: "membership_prove p (commitment_ledger notes) c_in1 = Some member1"
      and member2_def: "membership_prove p (commitment_ledger notes) c_in2 = Some member2"
      and nf1_def:
        "nullifier_fs_prove p gamma ck nk c_in1 nf1 op_in1 y_in1 = Some nf_proof1"
      and nf2_def:
        "nullifier_fs_prove p gamma ck nk c_in2 nf2 op_in2 y_in2 = Some nf_proof2"
      and bal_def:
        "balance_fs_prove p gamma ck
          (balance_commitment c_in1 c_in2 c_out1 c_out2 (cp_q p))
          (aggregate_randomness op_in1 op_in2 op_out1 op_out2) y_balance = Some bal_proof"
      and range1_def:
        "range_fs_prove p gamma k ck c_out1 op_out1 out1_bits out1_comps y_out1_amounts y_out1_pairss = Some range1"
      and range2_def:
        "range_fs_prove p gamma k ck c_out2 op_out2 out2_bits out2_comps y_out2_amounts y_out2_pairss = Some range2"
      and rel:
        "transaction_relation_wellformed p ck nk (commitment_ledger notes) spent
          c_in1 c_in2 c_out1 c_out2 nf1 nf2
          op_in1 op_in2 op_out1 op_out2 out1_bits out1_comps out2_bits out2_comps"
      and idx_ne: "member_index member1 \<noteq> member_index member2"
      and proof_eq:
        "proof =
          \<lparr> tx_in1_member = member1,
            tx_in2_member = member2,
            tx_in1_nullifier = nf_proof1,
            tx_in2_nullifier = nf_proof2,
            tx_balance = bal_proof,
            tx_out1_range = range1,
            tx_out2_range = range2 \<rparr>"
    using tx_prove
    unfolding transaction_fs_prove_def
    by (auto split: option.splits if_splits)
  have member1_ok: "membership_verify p c_in1 member1"
    using membership_prove_complete[OF member1_def] .
  have member2_ok: "membership_verify p c_in2 member2"
    using membership_prove_complete[OF member2_def] .
  have root1_eq: "member_root member1 = ledger_root p (commitment_ledger notes)"
    using member1_def unfolding membership_prove_def
    by (auto split: option.splits)
  have root2_eq: "member_root member2 = ledger_root p (commitment_ledger notes)"
    using member2_def unfolding membership_prove_def
    by (auto split: option.splits)
  have post_ok:
    "ledger_valid p gamma k ck
      (ledger_root p (commitment_ledger (ledger_apply_notes notes proof c_out1 c_out2)))
      (ledger_apply_notes notes proof c_out1 c_out2)
      (ledger_apply_spent spent nf1 nf2)"
    using ledger_snapshot_valid_after_transaction[OF ledger_ok tx_prove] .
  have member1_ok': "membership_verify p c_in1 (tx_in1_member proof)"
    using member1_ok proof_eq by simp
  have member2_ok': "membership_verify p c_in2 (tx_in2_member proof)"
    using member2_ok proof_eq by simp
  have root1_eq': "member_root (tx_in1_member proof) = ledger_root p (commitment_ledger notes)"
    using root1_eq proof_eq by simp
  have root2_eq': "member_root (tx_in2_member proof) = ledger_root p (commitment_ledger notes)"
    using root2_eq proof_eq by simp
  have idx_ne': "member_index (tx_in1_member proof) \<noteq> member_index (tx_in2_member proof)"
    using idx_ne proof_eq by simp
  show ?thesis
    unfolding ledger_step_semantic_def
    using ledger_ok member1_ok' member2_ok' root1_eq' root2_eq' idx_ne' post_ok tx_relation proof_eq
    by blast
qed

lemma ledger_reachable_after_transaction:
  assumes reach:
        "ledger_reachable p gamma k ck nk notes0 spent0 notes spent"
      and tx_prove:
        "transaction_fs_prove p gamma k ck nk (commitment_ledger notes) spent
          c_in1 c_in2 c_out1 c_out2 nf1 nf2
          op_in1 op_in2 op_out1 op_out2
          out1_bits out1_comps out2_bits out2_comps
          y_in1 y_in2 y_balance y_out1_amounts y_out1_pairss y_out2_amounts y_out2_pairss = Some proof"
      and tx_relation:
        "transaction_relation p ck nk (commitment_ledger notes) spent
          c_in1 c_in2 c_out1 c_out2 nf1 nf2
          op_in1 op_in2 op_out1 op_out2 out1_bits out1_comps out2_bits out2_comps"
  shows "ledger_reachable p gamma k ck nk notes0 spent0
           (ledger_apply_notes notes proof c_out1 c_out2)
           (ledger_apply_spent spent nf1 nf2)"
proof -
  have ledger_ok:
    "ledger_valid p gamma k ck (ledger_root p (commitment_ledger notes)) notes spent"
    using ledger_reachable_snapshot_valid[OF reach] .
  have step_ok:
    "ledger_step_semantic p gamma k ck nk notes spent
      c_in1 c_in2 c_out1 c_out2 nf1 nf2 proof
      (ledger_apply_notes notes proof c_out1 c_out2)
      (ledger_apply_spent spent nf1 nf2)"
    using ledger_step_semantic_after_transaction[OF ledger_ok tx_prove tx_relation] .
  show ?thesis
    using reach step_ok by (meson ledger_reachable.intros)
qed

text \<open>
  Security-facing contracts.

  The executable verifier lemmas above prove completeness and ledger-state
  preservation. Knowledge soundness and zero knowledge are exposed below as
  explicit extractor and simulator assumptions. This keeps the current
  formalization honest: a production LaZer-grade proof must instantiate these
  predicates with concrete extractors, simulators, distribution bounds, and
  Fiat--Shamir assumptions.
\<close>

type_synonym balance_fs_extractor =
  "commit_params \<Rightarrow> int \<Rightarrow> commit_key \<Rightarrow> commitment \<Rightarrow> balance_proof \<Rightarrow> int_vec option"

type_synonym range_fs_extractor =
  "commit_params \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> commit_key \<Rightarrow> commitment \<Rightarrow> range_proof \<Rightarrow>
    (commit_opening \<times> commit_opening list \<times> commit_opening list) option"

type_synonym nullifier_fs_extractor =
  "commit_params \<Rightarrow> int \<Rightarrow> commit_key \<Rightarrow> commit_key \<Rightarrow> commitment \<Rightarrow>
    commitment \<Rightarrow> nullifier_proof \<Rightarrow> commit_opening option"

definition balance_fs_extractor_correct :: "balance_fs_extractor \<Rightarrow> bool" where
  "balance_fs_extractor_correct E \<longleftrightarrow>
    (\<forall>p gamma ck c proof.
      balance_fs_verify p gamma ck c proof \<longrightarrow>
      (\<exists>r. E p gamma ck c proof = Some r \<and> balance_relation p ck c r))"

definition range_fs_extractor_correct :: "range_fs_extractor \<Rightarrow> bool" where
  "range_fs_extractor_correct E \<longleftrightarrow>
    (\<forall>p gamma k ck c proof.
      range_fs_verify p gamma k ck c proof \<longrightarrow>
      (\<exists>op_amount ops_bits ops_comps.
        E p gamma k ck c proof = Some (op_amount, ops_bits, ops_comps) \<and>
        range_relation p ck c op_amount ops_bits ops_comps))"

definition nullifier_fs_extractor_correct :: "nullifier_fs_extractor \<Rightarrow> bool" where
  "nullifier_fs_extractor_correct E \<longleftrightarrow>
    (\<forall>p gamma ck nk c nf proof.
      nullifier_fs_verify p gamma ck nk c nf proof \<longrightarrow>
      (\<exists>op. E p gamma ck nk c nf proof = Some op \<and> nullifier_relation p ck nk c nf op))"

lemma balance_fs_knowledge_sound_if_extractor_correct:
  assumes "balance_fs_extractor_correct E"
      and "balance_fs_verify p gamma ck c proof"
  obtains r where
    "E p gamma ck c proof = Some r"
    "balance_relation p ck c r"
  using assms
  unfolding balance_fs_extractor_correct_def
  by blast

lemma range_fs_knowledge_sound_if_extractor_correct:
  assumes "range_fs_extractor_correct E"
      and "range_fs_verify p gamma k ck c proof"
  obtains op_amount ops_bits ops_comps where
    "E p gamma k ck c proof = Some (op_amount, ops_bits, ops_comps)"
    "range_relation p ck c op_amount ops_bits ops_comps"
  using assms
  unfolding range_fs_extractor_correct_def
  by blast

theorem range_fs_soundness_in_range_if_extractor_correct:
  assumes corr: "range_fs_extractor_correct E"
      and verify: "range_fs_verify p gamma k ck c proof"
  obtains op_amount ops_bits ops_comps where
    "E p gamma k ck c proof = Some (op_amount, ops_bits, ops_comps)"
    "range_relation p ck c op_amount ops_bits ops_comps"
    "0 \<le> amount_of_opening op_amount"
    "amount_of_opening op_amount < 2 ^ length ops_bits"
proof -
  obtain op_amount ops_bits ops_comps where extracted:
    "E p gamma k ck c proof = Some (op_amount, ops_bits, ops_comps)"
    "range_relation p ck c op_amount ops_bits ops_comps"
    using range_fs_knowledge_sound_if_extractor_correct[OF corr verify] by blast
  have lower: "0 \<le> amount_of_opening op_amount"
    using range_relation_in_range(1)[OF extracted(2)] .
  have upper: "amount_of_opening op_amount < 2 ^ length ops_bits"
    using range_relation_in_range(2)[OF extracted(2)] .
  show ?thesis
    using that extracted lower upper by blast
qed

lemma nullifier_fs_knowledge_sound_if_extractor_correct:
  assumes "nullifier_fs_extractor_correct E"
      and "nullifier_fs_verify p gamma ck nk c nf proof"
  obtains op where
    "E p gamma ck nk c nf proof = Some op"
    "nullifier_relation p ck nk c nf op"
  using assms
  unfolding nullifier_fs_extractor_correct_def
  by blast

definition balance_fs_scheduled_forking_assumption ::
  "commit_params \<Rightarrow> int \<Rightarrow> commit_key \<Rightarrow> commitment \<Rightarrow> balance_proof \<Rightarrow> bool" where
  "balance_fs_scheduled_forking_assumption p gamma ck c proof \<longleftrightarrow>
    (balance_fs_verify p gamma ck c proof \<longrightarrow>
      (\<exists>es1 zs1 es2 zs2 i.
        balance_scheduled_verify p gamma ck c (balance_as proof) es1 zs1 \<and>
        balance_scheduled_verify p gamma ck c (balance_as proof) es2 zs2 \<and>
        forked_binary_challenge_schedules balance_fs_rounds es1 es2 i))"

definition range_fs_scheduled_forking_assumption ::
  "commit_params \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> commit_key \<Rightarrow> commitment \<Rightarrow> range_proof \<Rightarrow> bool" where
  "range_fs_scheduled_forking_assumption p gamma k ck c proof \<longleftrightarrow>
    (range_fs_verify p gamma k ck c proof \<longrightarrow>
      (\<exists>es1 z_amounts1 z_pairss1 es2 z_amounts2 z_pairss2 i.
        range_scheduled_verify p gamma k ck c
          (range_bits proof) (range_comps proof)
          (range_amount_as proof) (range_pair_ass proof)
          es1 z_amounts1 z_pairss1 \<and>
        range_scheduled_verify p gamma k ck c
          (range_bits proof) (range_comps proof)
          (range_amount_as proof) (range_pair_ass proof)
          es2 z_amounts2 z_pairss2 \<and>
        forked_binary_challenge_schedules range_fs_rounds es1 es2 i))"

definition nullifier_fs_scheduled_forking_assumption ::
  "commit_params \<Rightarrow> int \<Rightarrow> commit_key \<Rightarrow> commit_key \<Rightarrow>
   commitment \<Rightarrow> commitment \<Rightarrow> nullifier_proof \<Rightarrow> bool" where
  "nullifier_fs_scheduled_forking_assumption p gamma ck nk c nf proof \<longleftrightarrow>
    (nullifier_fs_verify p gamma ck nk c nf proof \<longrightarrow>
      (\<exists>es1 zs1 es2 zs2 i.
        nullifier_scheduled_verify p gamma ck nk c nf
          (nullifier_a_commits proof) (nullifier_a_nullifiers proof) es1 zs1 \<and>
        nullifier_scheduled_verify p gamma ck nk c nf
          (nullifier_a_commits proof) (nullifier_a_nullifiers proof) es2 zs2 \<and>
        forked_binary_challenge_schedules nullifier_fs_rounds es1 es2 i))"

lemma balance_fs_bounded_opening_if_scheduled_forking:
  assumes fork_model: "balance_fs_scheduled_forking_assumption p gamma ck c proof"
      and verify: "balance_fs_verify p gamma ck c proof"
      and c_valid: "valid_commitment p c"
      and c_canonical: "vec_mod c (cp_q p) = c"
  obtains es1 zs1 es2 zs2 i r where
    "balance_scheduled_verify p gamma ck c (balance_as proof) es1 zs1"
    "balance_scheduled_verify p gamma ck c (balance_as proof) es2 zs2"
    "forked_binary_challenge_schedules balance_fs_rounds es1 es2 i"
    "balance_scheduled_fork_extract es1 zs1 es2 zs2 i = Some r"
    "rand_commit p ck r = c"
    "valid_vec r (cp_n2 p)"
    "all_bounded r (2 * gamma + 4 * cp_beta p)"
proof -
  obtain es1 zs1 es2 zs2 i where forked:
    "balance_scheduled_verify p gamma ck c (balance_as proof) es1 zs1"
    "balance_scheduled_verify p gamma ck c (balance_as proof) es2 zs2"
    "forked_binary_challenge_schedules balance_fs_rounds es1 es2 i"
    using fork_model verify
    unfolding balance_fs_scheduled_forking_assumption_def
    by blast
  obtain r where extracted:
    "balance_scheduled_fork_extract es1 zs1 es2 zs2 i = Some r"
    "rand_commit p ck r = c"
    "valid_vec r (cp_n2 p)"
    "all_bounded r (2 * gamma + 4 * cp_beta p)"
    using balance_scheduled_fork_extract_algebraic_opening[
      OF forked(1) forked(2) forked(3) c_valid c_canonical]
    by blast
  show ?thesis
    using that forked extracted by blast
qed

lemma range_fs_amount_residual_opening_if_scheduled_forking:
  assumes fork_model: "range_fs_scheduled_forking_assumption p gamma k ck c proof"
      and verify: "range_fs_verify p gamma k ck c proof"
      and c_valid:
        "valid_commitment p (range_amount_commitment p ck c (range_bits proof))"
      and c_canonical:
        "vec_mod (range_amount_commitment p ck c (range_bits proof)) (cp_q p) =
         range_amount_commitment p ck c (range_bits proof)"
  obtains es1 z_amounts1 z_pairss1 es2 z_amounts2 z_pairss2 i r where
    "range_scheduled_verify p gamma k ck c
      (range_bits proof) (range_comps proof)
      (range_amount_as proof) (range_pair_ass proof)
      es1 z_amounts1 z_pairss1"
    "range_scheduled_verify p gamma k ck c
      (range_bits proof) (range_comps proof)
      (range_amount_as proof) (range_pair_ass proof)
      es2 z_amounts2 z_pairss2"
    "forked_binary_challenge_schedules range_fs_rounds es1 es2 i"
    "range_scheduled_fork_extract_amount es1 z_amounts1 es2 z_amounts2 i =
       Some r"
    "rand_commit p ck r = range_amount_commitment p ck c (range_bits proof)"
    "valid_vec r (cp_n2 p)"
    "all_bounded r (2 * gamma + range_amount_witness_bound p k)"
proof -
  obtain es1 z_amounts1 z_pairss1 es2 z_amounts2 z_pairss2 i where forked:
    "range_scheduled_verify p gamma k ck c
      (range_bits proof) (range_comps proof)
      (range_amount_as proof) (range_pair_ass proof)
      es1 z_amounts1 z_pairss1"
    "range_scheduled_verify p gamma k ck c
      (range_bits proof) (range_comps proof)
      (range_amount_as proof) (range_pair_ass proof)
      es2 z_amounts2 z_pairss2"
    "forked_binary_challenge_schedules range_fs_rounds es1 es2 i"
    using fork_model verify
    unfolding range_fs_scheduled_forking_assumption_def
    by blast
  obtain r where extracted:
    "range_scheduled_fork_extract_amount es1 z_amounts1 es2 z_amounts2 i =
       Some r"
    "rand_commit p ck r = range_amount_commitment p ck c (range_bits proof)"
    "valid_vec r (cp_n2 p)"
    "all_bounded r (2 * gamma + range_amount_witness_bound p k)"
    using range_scheduled_fork_extract_amount_algebraic_opening[
      OF forked(1) forked(2) forked(3) c_valid c_canonical]
    by blast
  show ?thesis
    using that forked extracted by blast
qed

lemma range_fs_pair_residual_opening_if_scheduled_forking:
  assumes fork_model: "range_fs_scheduled_forking_assumption p gamma k ck c proof"
      and verify: "range_fs_verify p gamma k ck c proof"
      and j_lt: "j < k"
      and c_valid:
        "valid_commitment p
          ((range_pair_commitments p ck (range_bits proof) (range_comps proof)) ! j)"
      and c_canonical:
        "vec_mod
          ((range_pair_commitments p ck (range_bits proof) (range_comps proof)) ! j)
          (cp_q p) =
         (range_pair_commitments p ck (range_bits proof) (range_comps proof)) ! j"
  obtains es1 z_amounts1 z_pairss1 es2 z_amounts2 z_pairss2 i r where
    "range_scheduled_verify p gamma k ck c
      (range_bits proof) (range_comps proof)
      (range_amount_as proof) (range_pair_ass proof)
      es1 z_amounts1 z_pairss1"
    "range_scheduled_verify p gamma k ck c
      (range_bits proof) (range_comps proof)
      (range_amount_as proof) (range_pair_ass proof)
      es2 z_amounts2 z_pairss2"
    "forked_binary_challenge_schedules range_fs_rounds es1 es2 i"
    "range_scheduled_fork_extract_pair es1 z_pairss1 es2 z_pairss2 i j =
       Some r"
    "rand_commit p ck r =
      (range_pair_commitments p ck (range_bits proof) (range_comps proof)) ! j"
    "valid_vec r (cp_n2 p)"
    "all_bounded r (2 * gamma + range_pair_witness_bound p)"
proof -
  obtain es1 z_amounts1 z_pairss1 es2 z_amounts2 z_pairss2 i where forked:
    "range_scheduled_verify p gamma k ck c
      (range_bits proof) (range_comps proof)
      (range_amount_as proof) (range_pair_ass proof)
      es1 z_amounts1 z_pairss1"
    "range_scheduled_verify p gamma k ck c
      (range_bits proof) (range_comps proof)
      (range_amount_as proof) (range_pair_ass proof)
      es2 z_amounts2 z_pairss2"
    "forked_binary_challenge_schedules range_fs_rounds es1 es2 i"
    using fork_model verify
    unfolding range_fs_scheduled_forking_assumption_def
    by blast
  obtain r where extracted:
    "range_scheduled_fork_extract_pair es1 z_pairss1 es2 z_pairss2 i j =
       Some r"
    "rand_commit p ck r =
      (range_pair_commitments p ck (range_bits proof) (range_comps proof)) ! j"
    "valid_vec r (cp_n2 p)"
    "all_bounded r (2 * gamma + range_pair_witness_bound p)"
    using range_scheduled_fork_extract_pair_algebraic_opening[
      OF forked(1) forked(2) forked(3) j_lt c_valid c_canonical]
    by blast
  show ?thesis
    using that forked extracted by blast
qed

lemma nullifier_fs_opening_if_scheduled_forking:
  assumes fork_model:
        "nullifier_fs_scheduled_forking_assumption p gamma ck nk c nf proof"
      and verify: "nullifier_fs_verify p gamma ck nk c nf proof"
      and c_canonical: "vec_mod c (cp_q p) = c"
      and nf_canonical: "vec_mod nf (cp_q p) = nf"
  obtains es1 zs1 es2 zs2 i op where
    "nullifier_scheduled_verify p gamma ck nk c nf
      (nullifier_a_commits proof) (nullifier_a_nullifiers proof) es1 zs1"
    "nullifier_scheduled_verify p gamma ck nk c nf
      (nullifier_a_commits proof) (nullifier_a_nullifiers proof) es2 zs2"
    "forked_binary_challenge_schedules nullifier_fs_rounds es1 es2 i"
    "nullifier_scheduled_fork_extract es1 zs1 es2 zs2 i = Some op"
    "commit ck op (cp_q p) = c"
    "nullifier p nk op = nf"
    "valid_vec (open_msg op) (cp_n1 p)"
    "valid_vec (open_rand op) (cp_n2 p)"
    "all_bounded (open_msg op) (2 * gamma + cp_beta p)"
    "all_bounded (open_rand op) (2 * gamma + cp_beta p)"
proof -
  obtain es1 zs1 es2 zs2 i where forked:
    "nullifier_scheduled_verify p gamma ck nk c nf
      (nullifier_a_commits proof) (nullifier_a_nullifiers proof) es1 zs1"
    "nullifier_scheduled_verify p gamma ck nk c nf
      (nullifier_a_commits proof) (nullifier_a_nullifiers proof) es2 zs2"
    "forked_binary_challenge_schedules nullifier_fs_rounds es1 es2 i"
    using fork_model verify
    unfolding nullifier_fs_scheduled_forking_assumption_def
    by blast
  obtain op where extracted:
    "nullifier_scheduled_fork_extract es1 zs1 es2 zs2 i = Some op"
    "commit ck op (cp_q p) = c"
    "nullifier p nk op = nf"
    "valid_vec (open_msg op) (cp_n1 p)"
    "valid_vec (open_rand op) (cp_n2 p)"
    "all_bounded (open_msg op) (2 * gamma + cp_beta p)"
    "all_bounded (open_rand op) (2 * gamma + cp_beta p)"
    using nullifier_scheduled_fork_extract_algebraic_opening[
      OF forked(1) forked(2) forked(3) c_canonical nf_canonical]
    by blast
  show ?thesis
    using that forked extracted by blast
qed

type_synonym balance_fs_simulator =
  "commit_params \<Rightarrow> int \<Rightarrow> commit_key \<Rightarrow> commitment \<Rightarrow> balance_proof"

type_synonym range_fs_simulator =
  "commit_params \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> commit_key \<Rightarrow> commitment \<Rightarrow> range_proof"

type_synonym nullifier_fs_simulator =
  "commit_params \<Rightarrow> int \<Rightarrow> commit_key \<Rightarrow> commit_key \<Rightarrow> commitment \<Rightarrow>
    commitment \<Rightarrow> nullifier_proof"

definition balance_fs_hvzk_assumption ::
  "balance_fs_simulator \<Rightarrow> balance_fs_simulator \<Rightarrow> (balance_proof \<Rightarrow> balance_proof \<Rightarrow> bool) \<Rightarrow> bool" where
  "balance_fs_hvzk_assumption simulator real_transcript indist \<longleftrightarrow>
    (\<forall>p gamma ck c.
      balance_fs_verify p gamma ck c (simulator p gamma ck c) \<and>
      indist (simulator p gamma ck c) (real_transcript p gamma ck c))"

definition range_fs_hvzk_assumption ::
  "range_fs_simulator \<Rightarrow> range_fs_simulator \<Rightarrow> (range_proof \<Rightarrow> range_proof \<Rightarrow> bool) \<Rightarrow> bool" where
  "range_fs_hvzk_assumption simulator real_transcript indist \<longleftrightarrow>
    (\<forall>p gamma k ck c.
      range_fs_verify p gamma k ck c (simulator p gamma k ck c) \<and>
      indist (simulator p gamma k ck c) (real_transcript p gamma k ck c))"

definition nullifier_fs_hvzk_assumption ::
  "nullifier_fs_simulator \<Rightarrow> nullifier_fs_simulator \<Rightarrow>
   (nullifier_proof \<Rightarrow> nullifier_proof \<Rightarrow> bool) \<Rightarrow> bool" where
  "nullifier_fs_hvzk_assumption simulator real_transcript indist \<longleftrightarrow>
    (\<forall>p gamma ck nk c nf.
      nullifier_fs_verify p gamma ck nk c nf (simulator p gamma ck nk c nf) \<and>
      indist (simulator p gamma ck nk c nf) (real_transcript p gamma ck nk c nf))"

lemma balance_fs_hvzk_if_assumed:
  assumes "balance_fs_hvzk_assumption simulator real_transcript indist"
  shows "balance_fs_verify p gamma ck c (simulator p gamma ck c)"
    and "indist (simulator p gamma ck c) (real_transcript p gamma ck c)"
  using assms
  unfolding balance_fs_hvzk_assumption_def
  by auto

lemma range_fs_hvzk_if_assumed:
  assumes "range_fs_hvzk_assumption simulator real_transcript indist"
  shows "range_fs_verify p gamma k ck c (simulator p gamma k ck c)"
    and "indist (simulator p gamma k ck c) (real_transcript p gamma k ck c)"
  using assms
  unfolding range_fs_hvzk_assumption_def
  by auto

lemma nullifier_fs_hvzk_if_assumed:
  assumes "nullifier_fs_hvzk_assumption simulator real_transcript indist"
  shows "nullifier_fs_verify p gamma ck nk c nf (simulator p gamma ck nk c nf)"
    and "indist (simulator p gamma ck nk c nf) (real_transcript p gamma ck nk c nf)"
  using assms
  unfolding nullifier_fs_hvzk_assumption_def
  by auto

text \<open>
  The following programmed-schedule HVZK interfaces narrow the older simulator
  assumptions above. They expose the concrete scheduled simulator, response
  validity checks, and the exact Fiat--Shamir challenge-match condition that a
  programmable transcript theorem must justify. They still do not prove
  distributional indistinguishability or rejection-sampling bounds.
\<close>

definition balance_fs_programmed_hvzk_assumption ::
  "commit_params \<Rightarrow> int \<Rightarrow> commit_key \<Rightarrow> commitment \<Rightarrow>
   int list \<Rightarrow> int_vec list \<Rightarrow> balance_proof \<Rightarrow>
   (balance_proof \<Rightarrow> balance_proof \<Rightarrow> bool) \<Rightarrow> bool" where
  "balance_fs_programmed_hvzk_assumption p gamma ck c es zs real_proof indist \<longleftrightarrow>
    valid_scalar_commit_params p \<and>
    valid_commit_key p ck \<and>
    valid_commitment p c \<and>
    length es = balance_fs_rounds \<and>
    length zs = balance_fs_rounds \<and>
    (\<forall>i < balance_fs_rounds. valid_balance_challenge p (es ! i)) \<and>
    (\<forall>i < balance_fs_rounds. valid_balance_response p gamma (es ! i) (zs ! i)) \<and>
    balance_fs_challenges p ck c
      (balance_as (balance_scheduled_simulate p ck c es zs)) = es \<and>
    indist (balance_scheduled_simulate p ck c es zs) real_proof"

lemma balance_fs_hvzk_if_programmed_scheduled:
  assumes programmed:
    "balance_fs_programmed_hvzk_assumption p gamma ck c es zs real_proof indist"
  shows "balance_fs_verify p gamma ck c (balance_scheduled_simulate p ck c es zs)"
    and "indist (balance_scheduled_simulate p ck c es zs) real_proof"
proof -
  show "balance_fs_verify p gamma ck c (balance_scheduled_simulate p ck c es zs)"
    using programmed
    unfolding balance_fs_programmed_hvzk_assumption_def
    by (auto intro: balance_fs_verify_scheduled_simulate_if_challenges_match)
  show "indist (balance_scheduled_simulate p ck c es zs) real_proof"
    using programmed
    unfolding balance_fs_programmed_hvzk_assumption_def
    by simp
qed

definition range_fs_programmed_hvzk_assumption ::
  "commit_params \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> commit_key \<Rightarrow> commitment \<Rightarrow>
   commitment list \<Rightarrow> commitment list \<Rightarrow> int list \<Rightarrow>
   int_vec list \<Rightarrow> int_vec list list \<Rightarrow> range_proof \<Rightarrow>
   (range_proof \<Rightarrow> range_proof \<Rightarrow> bool) \<Rightarrow> bool" where
  "range_fs_programmed_hvzk_assumption
      p gamma k ck c_amount c_bits c_comps es z_amounts z_pairss
      real_proof indist \<longleftrightarrow>
    valid_scalar_commit_params p \<and>
    valid_commit_key p ck \<and>
    valid_commitment p c_amount \<and>
    valid_commitment p (range_amount_commitment p ck c_amount c_bits) \<and>
    length (range_pair_commitments p ck c_bits c_comps) = k \<and>
    (\<forall>j < k.
      valid_commitment p
        ((range_pair_commitments p ck c_bits c_comps) ! j)) \<and>
    length c_bits = k \<and>
    length c_comps = k \<and>
    length es = range_fs_rounds \<and>
    length z_amounts = range_fs_rounds \<and>
    length z_pairss = range_fs_rounds \<and>
    (\<forall>i < range_fs_rounds. valid_range_challenge p (es ! i)) \<and>
    (\<forall>i < range_fs_rounds.
      valid_range_amount_response p gamma k (es ! i) (z_amounts ! i)) \<and>
    (\<forall>i < range_fs_rounds. length (z_pairss ! i) = k) \<and>
    (\<forall>i < range_fs_rounds.
      (\<forall>j < k.
        valid_range_pair_response p gamma (es ! i) ((z_pairss ! i) ! j))) \<and>
    range_fs_challenges p ck c_amount c_bits c_comps
      (range_amount_as
        (range_scheduled_simulate p ck c_amount c_bits c_comps
          es z_amounts z_pairss))
      (range_pair_ass
        (range_scheduled_simulate p ck c_amount c_bits c_comps
          es z_amounts z_pairss)) = es \<and>
    indist
      (range_scheduled_simulate p ck c_amount c_bits c_comps
        es z_amounts z_pairss)
      real_proof"

lemma range_fs_hvzk_if_programmed_scheduled:
  assumes programmed:
    "range_fs_programmed_hvzk_assumption
      p gamma k ck c_amount c_bits c_comps es z_amounts z_pairss
      real_proof indist"
  shows "range_fs_verify p gamma k ck c_amount
           (range_scheduled_simulate p ck c_amount c_bits c_comps
             es z_amounts z_pairss)"
    and "indist
          (range_scheduled_simulate p ck c_amount c_bits c_comps
            es z_amounts z_pairss)
          real_proof"
proof -
  show "range_fs_verify p gamma k ck c_amount
          (range_scheduled_simulate p ck c_amount c_bits c_comps
            es z_amounts z_pairss)"
    using programmed
    unfolding range_fs_programmed_hvzk_assumption_def
    by (auto intro: range_fs_verify_scheduled_simulate_if_challenges_match)
  show "indist
          (range_scheduled_simulate p ck c_amount c_bits c_comps
            es z_amounts z_pairss)
          real_proof"
    using programmed
    unfolding range_fs_programmed_hvzk_assumption_def
    by simp
qed

definition nullifier_fs_programmed_hvzk_assumption ::
  "commit_params \<Rightarrow> int \<Rightarrow> commit_key \<Rightarrow> commit_key \<Rightarrow>
   commitment \<Rightarrow> commitment \<Rightarrow> int list \<Rightarrow> commit_opening list \<Rightarrow>
   nullifier_proof \<Rightarrow> (nullifier_proof \<Rightarrow> nullifier_proof \<Rightarrow> bool) \<Rightarrow> bool" where
  "nullifier_fs_programmed_hvzk_assumption
      p gamma ck nk c nf es zs real_proof indist \<longleftrightarrow>
    valid_scalar_commit_params p \<and>
    valid_commit_key p ck \<and>
    valid_commit_key p nk \<and>
    valid_commitment p c \<and>
    valid_commitment p nf \<and>
    length es = nullifier_fs_rounds \<and>
    length zs = nullifier_fs_rounds \<and>
    (\<forall>i < nullifier_fs_rounds. valid_nullifier_challenge p (es ! i)) \<and>
    (\<forall>i < nullifier_fs_rounds.
      valid_nullifier_response p gamma (es ! i) (zs ! i)) \<and>
    nullifier_fs_challenges p ck nk c nf
      (nullifier_a_commits
        (nullifier_scheduled_simulate p ck nk c nf es zs))
      (nullifier_a_nullifiers
        (nullifier_scheduled_simulate p ck nk c nf es zs)) = es \<and>
    indist (nullifier_scheduled_simulate p ck nk c nf es zs) real_proof"

lemma nullifier_fs_hvzk_if_programmed_scheduled:
  assumes programmed:
    "nullifier_fs_programmed_hvzk_assumption
      p gamma ck nk c nf es zs real_proof indist"
  shows "nullifier_fs_verify p gamma ck nk c nf
           (nullifier_scheduled_simulate p ck nk c nf es zs)"
    and "indist (nullifier_scheduled_simulate p ck nk c nf es zs) real_proof"
proof -
  show "nullifier_fs_verify p gamma ck nk c nf
          (nullifier_scheduled_simulate p ck nk c nf es zs)"
    using programmed
    unfolding nullifier_fs_programmed_hvzk_assumption_def
    by (auto intro: nullifier_fs_verify_scheduled_simulate_if_challenges_match)
  show "indist (nullifier_scheduled_simulate p ck nk c nf es zs) real_proof"
    using programmed
    unfolding nullifier_fs_programmed_hvzk_assumption_def
    by simp
qed

theorem verified_opening_collision_yields_sis:
  assumes params_ok: "valid_commit_params p"
      and key_ok: "valid_commit_key p ck"
      and open1: "verify_opening p ck c op1"
      and open2: "verify_opening p ck c op2"
      and diff: "opening_vec op1 \<noteq> opening_vec op2"
  shows "\<exists>z. valid_vec z (cp_n1 p + cp_n2 p) \<and>
             \<not> is_zero_vec z \<and>
             all_bounded z (2 * cp_beta p) \<and>
             is_zero_vec (vec_mod (mat_vec_mult ck z) (cp_q p))"
proof -
  have break: "is_binding_break p ck c op1 op2"
    using open1 open2 diff
    unfolding is_binding_break_def
    by simp
  show ?thesis
    using binding_implies_sis[OF params_ok key_ok break] .
qed

theorem bounded_opening_collision_yields_sis:
  assumes params_ok: "valid_commit_params p"
      and key_ok: "valid_commit_key p ck"
      and len1: "length (opening_vec op1) = cp_n1 p + cp_n2 p"
      and len2: "length (opening_vec op2) = cp_n1 p + cp_n2 p"
      and bounded1: "all_bounded (opening_vec op1) B1"
      and bounded2: "all_bounded (opening_vec op2) B2"
      and collision: "commit ck op1 (cp_q p) = commit ck op2 (cp_q p)"
      and diff: "opening_vec op1 \<noteq> opening_vec op2"
  shows "\<exists>z. valid_sis_instance (commit_to_sis_params_bound p (B1 + B2)) \<lparr> sis_A = ck \<rparr> \<and>
             is_sis_solution (commit_to_sis_params_bound p (B1 + B2)) \<lparr> sis_A = ck \<rparr> z"
  using commit_collision_yields_sis_bound[
    OF params_ok key_ok len1 len2 bounded1 bounded2 collision diff] .

export_code
  nullifier
  valid_nullifier_mask
  nullifier_response_bound valid_nullifier_challenge valid_nullifier_response
  nullifier_relation
  nullifier_fs_rounds
  nullifier_proof.make
    nullifier_a_commits nullifier_a_nullifiers nullifier_z_msgs nullifier_z_rands
  nullifier_sigma_respond canonical_nullifier_challenge
  nullifier_fs_challenges nullifier_sigma_responses nullifier_sigma_verify
  nullifier_fs_prove nullifier_fs_verify
  empty_commitment ledger_hash ledger_root index_directions auth_path_root membership_siblings
  membership_proof.make member_index member_root member_siblings member_directions
  membership_prove membership_verify
  merkle_membership_proof.make
    merkle_member_index merkle_member_root merkle_member_siblings merkle_member_directions
  merkle_membership_verify
  verified_note.make note_commitment note_range_proof
  commitment_ledger ledger_valid
  transaction_proof.make
    tx_in1_member tx_in2_member tx_in1_nullifier tx_in2_nullifier
    tx_balance tx_out1_range tx_out2_range
  merkle_transaction_proof.make
    tx_merkle_in1_member tx_merkle_in2_member
    tx_merkle_in1_nullifier tx_merkle_in2_nullifier
    tx_merkle_balance tx_merkle_out1_range tx_merkle_out2_range
  transaction_relation transaction_relation_fee
  transaction_fs_prove transaction_fs_verify transaction_fs_verify_merkle
  transaction_fs_verify_merkle_fee
  ledger_apply_notes ledger_apply_spent
  in Haskell module_name "Canon.ZK.Confidential_Transaction"

export_code
  nullifier
  valid_nullifier_mask
  nullifier_response_bound valid_nullifier_challenge valid_nullifier_response
  nullifier_relation
  nullifier_fs_rounds
  nullifier_proof.make
    nullifier_a_commits nullifier_a_nullifiers nullifier_z_msgs nullifier_z_rands
  nullifier_sigma_respond canonical_nullifier_challenge
  nullifier_fs_challenges nullifier_sigma_responses nullifier_sigma_verify
  nullifier_fs_prove nullifier_fs_verify
  empty_commitment ledger_hash ledger_root index_directions auth_path_root membership_siblings
  membership_proof.make member_index member_root member_siblings member_directions
  membership_prove membership_verify
  merkle_membership_proof.make
    merkle_member_index merkle_member_root merkle_member_siblings merkle_member_directions
  merkle_membership_verify
  verified_note.make note_commitment note_range_proof
  commitment_ledger ledger_valid
  transaction_proof.make
    tx_in1_member tx_in2_member tx_in1_nullifier tx_in2_nullifier
    tx_balance tx_out1_range tx_out2_range
  merkle_transaction_proof.make
    tx_merkle_in1_member tx_merkle_in2_member
    tx_merkle_in1_nullifier tx_merkle_in2_nullifier
    tx_merkle_balance tx_merkle_out1_range tx_merkle_out2_range
  transaction_relation transaction_relation_fee
  transaction_fs_prove transaction_fs_verify transaction_fs_verify_merkle
  transaction_fs_verify_merkle_fee
  ledger_apply_notes ledger_apply_spent
  in OCaml module_name Confidential_transaction

end
