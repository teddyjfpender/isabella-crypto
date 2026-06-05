theory Confidential_Range
  imports Confidential_Balance Canon_Gadgets.Decomp
begin

text \<open>
  Confidential range proofs over SIS commitments.

  This theory extends the confidential-balance slice with a bounded-amount
  proof for a single scalar commitment. The construction is intentionally
  linear: the prover commits to bit openings and complement-bit openings,
  proves that each pair sums to one, and proves that the committed amount
  equals the base-2 recomposition of the bit openings.

  The verifier only checks deterministic Fiat-Shamir transcripts over
  zero-message residual commitments, which keeps the eventual smart-contract
  verifier path explicit and simple.
\<close>

definition one_opening :: "commit_params \<Rightarrow> commit_opening" where
  "one_opening p = \<lparr> open_msg = [1], open_rand = replicate (cp_n2 p) 0 \<rparr>"

definition opening_scale :: "int \<Rightarrow> commit_opening \<Rightarrow> commit_opening" where
  "opening_scale k op =
    \<lparr> open_msg = scalar_mult k (open_msg op),
      open_rand = scalar_mult k (open_rand op) \<rparr>"

fun all_valid_scalar_openings :: "commit_params \<Rightarrow> commit_opening list \<Rightarrow> bool" where
  "all_valid_scalar_openings p [] = True"
| "all_valid_scalar_openings p (op # ops) =
    (valid_scalar_opening p op \<and> all_valid_scalar_openings p ops)"

definition valid_bit_opening :: "commit_params \<Rightarrow> commit_opening \<Rightarrow> bool" where
  "valid_bit_opening p op \<longleftrightarrow>
    valid_scalar_opening p op \<and> all_bounded (open_msg op) 1"

definition bit_pair_relation ::
  "commit_params \<Rightarrow> commit_opening \<Rightarrow> commit_opening \<Rightarrow> bool" where
  "bit_pair_relation p op_bit op_comp \<longleftrightarrow>
    valid_bit_opening p op_bit \<and>
    valid_bit_opening p op_comp \<and>
    amount_of_opening op_bit + amount_of_opening op_comp = 1"

fun all_bit_pairs ::
  "commit_params \<Rightarrow> commit_opening list \<Rightarrow> commit_opening list \<Rightarrow> bool" where
  "all_bit_pairs p [] [] = True"
| "all_bit_pairs p (op_bit # ops_bits) (op_comp # ops_comps) =
    (bit_pair_relation p op_bit op_comp \<and>
     all_bit_pairs p ops_bits ops_comps)"
| "all_bit_pairs p _ _ = False"

fun weighted_opening ::
  "commit_params \<Rightarrow> int \<Rightarrow> commit_opening list \<Rightarrow> commit_opening" where
  "weighted_opening p B [] = zero_opening (replicate (cp_n2 p) 0)"
| "weighted_opening p B (op # ops) =
    opening_add op (opening_scale B (weighted_opening p B ops))"

fun weighted_commitment ::
  "commit_params \<Rightarrow> commit_key \<Rightarrow> int \<Rightarrow> commitment list \<Rightarrow> commitment" where
  "weighted_commitment p ck B [] = rand_commit p ck (replicate (cp_n2 p) 0)"
| "weighted_commitment p ck B (c # cs) =
    vec_mod
      (vec_add c (scalar_mult B (weighted_commitment p ck B cs)))
      (cp_q p)"

definition range_amount_opening ::
  "commit_params \<Rightarrow> commit_opening \<Rightarrow> commit_opening list \<Rightarrow> commit_opening" where
  "range_amount_opening p op_amount ops_bits =
    opening_sub op_amount (weighted_opening p 2 ops_bits)"

definition range_amount_randomness ::
  "commit_params \<Rightarrow> commit_opening \<Rightarrow> commit_opening list \<Rightarrow> int_vec" where
  "range_amount_randomness p op_amount ops_bits =
    open_rand (range_amount_opening p op_amount ops_bits)"

definition range_pair_opening ::
  "commit_params \<Rightarrow> commit_opening \<Rightarrow> commit_opening \<Rightarrow> commit_opening" where
  "range_pair_opening p op_bit op_comp =
    opening_sub (opening_add op_bit op_comp) (one_opening p)"

definition range_pair_randomness ::
  "commit_params \<Rightarrow> commit_opening \<Rightarrow> commit_opening \<Rightarrow> int_vec" where
  "range_pair_randomness p op_bit op_comp =
    open_rand (range_pair_opening p op_bit op_comp)"

fun range_pair_randomnesses ::
  "commit_params \<Rightarrow> commit_opening list \<Rightarrow> commit_opening list \<Rightarrow> int_vec list" where
  "range_pair_randomnesses p [] [] = []"
| "range_pair_randomnesses p (op_bit # ops_bits) (op_comp # ops_comps) =
    range_pair_randomness p op_bit op_comp #
    range_pair_randomnesses p ops_bits ops_comps"
| "range_pair_randomnesses p _ _ = []"

definition one_commitment ::
  "commit_params \<Rightarrow> commit_key \<Rightarrow> commitment" where
  "one_commitment p ck = commit ck (one_opening p) (cp_q p)"

definition range_amount_commitment ::
  "commit_params \<Rightarrow> commit_key \<Rightarrow> commitment \<Rightarrow> commitment list \<Rightarrow> commitment" where
  "range_amount_commitment p ck c_amount c_bits =
    vec_mod
      (vec_sub c_amount (weighted_commitment p ck 2 c_bits))
      (cp_q p)"

definition range_pair_commitment ::
  "commit_params \<Rightarrow> commit_key \<Rightarrow> commitment \<Rightarrow> commitment \<Rightarrow> commitment" where
  "range_pair_commitment p ck c_bit c_comp =
    vec_mod
      (vec_sub (vec_add c_bit c_comp) (one_commitment p ck))
      (cp_q p)"

fun range_pair_commitments ::
  "commit_params \<Rightarrow> commit_key \<Rightarrow> commitment list \<Rightarrow> commitment list \<Rightarrow> commitment list" where
  "range_pair_commitments p ck [] [] = []"
| "range_pair_commitments p ck (c_bit # c_bits) (c_comp # c_comps) =
    range_pair_commitment p ck c_bit c_comp #
    range_pair_commitments p ck c_bits c_comps"
| "range_pair_commitments p ck _ _ = []"

definition range_relation ::
  "commit_params \<Rightarrow> commit_key \<Rightarrow> commitment \<Rightarrow>
   commit_opening \<Rightarrow> commit_opening list \<Rightarrow> commit_opening list \<Rightarrow> bool" where
  "range_relation p ck c_amount op_amount ops_bits ops_comps \<longleftrightarrow>
    valid_scalar_commit_params p \<and>
    valid_commit_key p ck \<and>
    verify_opening p ck c_amount op_amount \<and>
    all_bit_pairs p ops_bits ops_comps \<and>
    amount_of_opening op_amount = recompose 2 (map amount_of_opening ops_bits)"

definition range_amount_witness_bound :: "commit_params \<Rightarrow> nat \<Rightarrow> int" where
  "range_amount_witness_bound p k = 2 ^ k * cp_beta p"

definition range_pair_witness_bound :: "commit_params \<Rightarrow> int" where
  "range_pair_witness_bound p = 2 * cp_beta p"

definition valid_range_amount_witness ::
  "commit_params \<Rightarrow> nat \<Rightarrow> int_vec \<Rightarrow> bool" where
  "valid_range_amount_witness p k r \<longleftrightarrow>
    valid_vec r (cp_n2 p) \<and>
    all_bounded r (range_amount_witness_bound p k)"

definition valid_range_pair_witness ::
  "commit_params \<Rightarrow> int_vec \<Rightarrow> bool" where
  "valid_range_pair_witness p r \<longleftrightarrow>
    valid_vec r (cp_n2 p) \<and>
    all_bounded r (range_pair_witness_bound p)"

definition range_amount_residual_relation ::
  "commit_params \<Rightarrow> nat \<Rightarrow> commit_key \<Rightarrow> commitment \<Rightarrow> int_vec \<Rightarrow> bool" where
  "range_amount_residual_relation p k ck c r \<longleftrightarrow>
    valid_scalar_commit_params p \<and>
    valid_commit_key p ck \<and>
    valid_range_amount_witness p k r \<and>
    rand_commit p ck r = c"

definition range_pair_residual_relation ::
  "commit_params \<Rightarrow> commit_key \<Rightarrow> commitment \<Rightarrow> int_vec \<Rightarrow> bool" where
  "range_pair_residual_relation p ck c r \<longleftrightarrow>
    valid_scalar_commit_params p \<and>
    valid_commit_key p ck \<and>
    valid_range_pair_witness p r \<and>
    rand_commit p ck r = c"

fun all_range_pair_residual_relations ::
  "commit_params \<Rightarrow> commit_key \<Rightarrow> commitment list \<Rightarrow> int_vec list \<Rightarrow> bool" where
  "all_range_pair_residual_relations p ck [] [] = True"
| "all_range_pair_residual_relations p ck (c # cs) (r # rs) =
    (range_pair_residual_relation p ck c r \<and>
     all_range_pair_residual_relations p ck cs rs)"
| "all_range_pair_residual_relations p ck _ _ = False"

definition valid_range_mask ::
  "commit_params \<Rightarrow> int \<Rightarrow> int_vec \<Rightarrow> bool" where
  "valid_range_mask p gamma y \<longleftrightarrow>
    valid_vec y (cp_n2 p) \<and> all_bounded y gamma"

definition range_amount_response_bound ::
  "commit_params \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> int" where
  "range_amount_response_bound p gamma k e =
    gamma + abs e * range_amount_witness_bound p k"

definition range_pair_response_bound ::
  "commit_params \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int" where
  "range_pair_response_bound p gamma e =
    gamma + abs e * range_pair_witness_bound p"

definition valid_range_challenge :: "commit_params \<Rightarrow> int \<Rightarrow> bool" where
  "valid_range_challenge p e \<longleftrightarrow> valid_balance_challenge p e"

definition valid_range_amount_response ::
  "commit_params \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> int_vec \<Rightarrow> bool" where
  "valid_range_amount_response p gamma k e z \<longleftrightarrow>
    valid_vec z (cp_n2 p) \<and>
    all_bounded z (range_amount_response_bound p gamma k e)"

definition valid_range_pair_response ::
  "commit_params \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int_vec \<Rightarrow> bool" where
  "valid_range_pair_response p gamma e z \<longleftrightarrow>
    valid_vec z (cp_n2 p) \<and>
    all_bounded z (range_pair_response_bound p gamma e)"

fun valid_range_masks ::
  "commit_params \<Rightarrow> int \<Rightarrow> int_vec list \<Rightarrow> bool" where
  "valid_range_masks p gamma [] = True"
| "valid_range_masks p gamma (y # ys) =
    (valid_range_mask p gamma y \<and> valid_range_masks p gamma ys)"

fun valid_range_pair_responses ::
  "commit_params \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int_vec list \<Rightarrow> bool" where
  "valid_range_pair_responses p gamma e [] = True"
| "valid_range_pair_responses p gamma e (z # zs) =
    (valid_range_pair_response p gamma e z \<and>
     valid_range_pair_responses p gamma e zs)"

fun range_sigma_announcements ::
  "commit_params \<Rightarrow> commit_key \<Rightarrow> int_vec list \<Rightarrow> commitment list" where
  "range_sigma_announcements p ck [] = []"
| "range_sigma_announcements p ck (y # ys) =
    rand_commit p ck y # range_sigma_announcements p ck ys"

fun range_sigma_responses ::
  "int_vec list \<Rightarrow> int_vec list \<Rightarrow> int \<Rightarrow> int_vec list" where
  "range_sigma_responses [] [] e = []"
| "range_sigma_responses (r # rs) (y # ys) e =
    balance_sigma_respond r y e # range_sigma_responses rs ys e"
| "range_sigma_responses _ _ e = []"

record range_proof =
  range_bits :: "commitment list"
  range_comps :: "commitment list"
  range_amount_as :: "commitment list"
  range_amount_zs :: "int_vec list"
  range_pair_ass :: "commitment list list"
  range_pair_zss :: "int_vec list list"

definition range_fs_rounds :: nat where
  "range_fs_rounds = balance_fs_rounds"

definition canonical_range_challenge ::
  "commit_params \<Rightarrow> commit_key \<Rightarrow> commitment \<Rightarrow> commitment list \<Rightarrow>
   commitment list \<Rightarrow> commitment list \<Rightarrow> commitment list list \<Rightarrow> int" where
  "canonical_range_challenge p ck c_amount c_bits c_comps a_amounts a_pairss =
    (sum_list (concat ck) +
     sum_list c_amount +
     sum_list (concat c_bits) +
     sum_list (concat c_comps) +
     sum_list (concat a_amounts) +
     sum_list (concat (concat a_pairss))) mod 2"

lemma canonical_range_challenge_valid:
  assumes "valid_scalar_commit_params p"
  shows "valid_range_challenge p
           (canonical_range_challenge p ck c_amount c_bits c_comps a_amounts a_pairss)"
proof -
  show ?thesis
    using assms
    unfolding valid_range_challenge_def valid_balance_challenge_def
              canonical_range_challenge_def
    by auto
qed

definition range_amount_sigma_verify ::
  "commit_params \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> commit_key \<Rightarrow> commitment \<Rightarrow>
   commitment \<Rightarrow> int \<Rightarrow> int_vec \<Rightarrow> bool" where
  "range_amount_sigma_verify p gamma k ck c a e z \<longleftrightarrow>
    valid_scalar_commit_params p \<and>
    valid_commit_key p ck \<and>
    valid_commitment p a \<and>
    valid_range_challenge p e \<and>
    valid_range_amount_response p gamma k e z \<and>
    rand_commit p ck z =
      vec_mod (vec_add a (scalar_mult e c)) (cp_q p)"

definition range_pair_sigma_verify ::
  "commit_params \<Rightarrow> int \<Rightarrow> commit_key \<Rightarrow> commitment \<Rightarrow>
   commitment \<Rightarrow> int \<Rightarrow> int_vec \<Rightarrow> bool" where
  "range_pair_sigma_verify p gamma ck c a e z \<longleftrightarrow>
    valid_scalar_commit_params p \<and>
    valid_commit_key p ck \<and>
    valid_commitment p a \<and>
    valid_range_challenge p e \<and>
    valid_range_pair_response p gamma e z \<and>
    rand_commit p ck z =
      vec_mod (vec_add a (scalar_mult e c)) (cp_q p)"

fun range_sigma_verify_pairs ::
  "commit_params \<Rightarrow> int \<Rightarrow> commit_key \<Rightarrow> commitment list \<Rightarrow>
   commitment list \<Rightarrow> int \<Rightarrow> int_vec list \<Rightarrow> bool" where
  "range_sigma_verify_pairs p gamma ck [] [] e [] = True"
| "range_sigma_verify_pairs p gamma ck (c # cs) (a # as) e (z # zs) =
    (range_pair_sigma_verify p gamma ck c a e z \<and>
     range_sigma_verify_pairs p gamma ck cs as e zs)"
| "range_sigma_verify_pairs p gamma ck _ _ e _ = False"

definition range_fs_challenges ::
  "commit_params \<Rightarrow> commit_key \<Rightarrow> commitment \<Rightarrow> commitment list \<Rightarrow>
   commitment list \<Rightarrow> commitment list \<Rightarrow> commitment list list \<Rightarrow> int list" where
  "range_fs_challenges p ck c_amount c_bits c_comps a_amounts a_pairss =
    bool_fs_challenges range_fs_rounds
      (sum_list (concat ck) +
       sum_list c_amount +
       sum_list (concat c_bits) +
       sum_list (concat c_comps) +
       sum_list (concat a_amounts) +
       sum_list (concat (concat a_pairss)))"

definition range_amount_sigma_announcements ::
  "commit_params \<Rightarrow> commit_key \<Rightarrow> int_vec list \<Rightarrow> commitment list" where
  "range_amount_sigma_announcements p ck y_amounts =
    map (rand_commit p ck) y_amounts"

definition range_amount_sigma_responses ::
  "int_vec \<Rightarrow> int_vec list \<Rightarrow> int list \<Rightarrow> int_vec list" where
  "range_amount_sigma_responses r_amount y_amounts es =
    balance_sigma_responds r_amount y_amounts es"

definition range_pair_sigma_announcement_rounds ::
  "commit_params \<Rightarrow> commit_key \<Rightarrow> int_vec list list \<Rightarrow> commitment list list" where
  "range_pair_sigma_announcement_rounds p ck y_pairss =
    map (range_sigma_announcements p ck) y_pairss"

definition range_pair_sigma_response_rounds ::
  "int_vec list \<Rightarrow> int_vec list list \<Rightarrow> int list \<Rightarrow> int_vec list list" where
  "range_pair_sigma_response_rounds rs y_pairss es =
    sigma_response_rounds range_sigma_responses rs y_pairss es"

definition range_fs_verify ::
  "commit_params \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> commit_key \<Rightarrow> commitment \<Rightarrow> range_proof \<Rightarrow> bool" where
  "range_fs_verify p gamma k ck c_amount proof \<longleftrightarrow>
    (let c_bits = range_bits proof;
         c_comps = range_comps proof;
         a_amounts = range_amount_as proof;
         a_pairss = range_pair_ass proof;
         z_amounts = range_amount_zs proof;
         z_pairss = range_pair_zss proof;
         es = range_fs_challenges p ck c_amount c_bits c_comps a_amounts a_pairss;
         c_amount_res = range_amount_commitment p ck c_amount c_bits;
         c_pair_res = range_pair_commitments p ck c_bits c_comps
     in valid_commitment p c_amount \<and>
        length c_bits = k \<and>
        length c_comps = k \<and>
        length a_amounts = range_fs_rounds \<and>
        length a_pairss = range_fs_rounds \<and>
        length z_amounts = range_fs_rounds \<and>
        length z_pairss = range_fs_rounds \<and>
        (\<forall>i < range_fs_rounds.
          length (a_pairss ! i) = k \<and>
          length (z_pairss ! i) = k \<and>
          range_amount_sigma_verify p gamma k ck c_amount_res
            (a_amounts ! i) (es ! i) (z_amounts ! i) \<and>
          range_sigma_verify_pairs p gamma ck c_pair_res
            (a_pairss ! i) (es ! i) (z_pairss ! i)))"

definition range_fs_prove ::
  "commit_params \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> commit_key \<Rightarrow> commitment \<Rightarrow>
   commit_opening \<Rightarrow> commit_opening list \<Rightarrow> commit_opening list \<Rightarrow>
   int_vec list \<Rightarrow> int_vec list list \<Rightarrow> range_proof option" where
  "range_fs_prove p gamma k ck c_amount op_amount ops_bits ops_comps y_amounts y_pairss =
    (let c_bits = map (\<lambda>op. commit ck op (cp_q p)) ops_bits;
         c_comps = map (\<lambda>op. commit ck op (cp_q p)) ops_comps;
         r_amount = range_amount_randomness p op_amount ops_bits;
         r_pairs = range_pair_randomnesses p ops_bits ops_comps;
         a_amounts = range_amount_sigma_announcements p ck y_amounts;
         a_pairss = range_pair_sigma_announcement_rounds p ck y_pairss;
         es = range_fs_challenges p ck c_amount c_bits c_comps a_amounts a_pairss;
         z_amounts = range_amount_sigma_responses r_amount y_amounts es;
         z_pairss = range_pair_sigma_response_rounds r_pairs y_pairss es
     in if range_relation p ck c_amount op_amount ops_bits ops_comps \<and>
           length ops_bits = k \<and>
           length ops_comps = k \<and>
           length y_amounts = range_fs_rounds \<and>
           length y_pairss = range_fs_rounds \<and>
           (\<forall>i < range_fs_rounds. valid_range_mask p gamma (y_amounts ! i)) \<and>
           (\<forall>i < range_fs_rounds.
             length (y_pairss ! i) = k \<and>
             valid_range_masks p gamma (y_pairss ! i)) \<and>
           (\<forall>i < range_fs_rounds.
             valid_range_amount_response p gamma k (es ! i) (z_amounts ! i)) \<and>
           (\<forall>i < range_fs_rounds.
             length (z_pairss ! i) = k \<and>
             valid_range_pair_responses p gamma (es ! i) (z_pairss ! i))
        then Some
          \<lparr> range_bits = c_bits,
            range_comps = c_comps,
            range_amount_as = a_amounts,
            range_amount_zs = z_amounts,
            range_pair_ass = a_pairss,
            range_pair_zss = z_pairss \<rparr>
        else None)"

lemma scalar_mult_append_eq:
  "scalar_mult c (xs @ ys) = scalar_mult c xs @ scalar_mult c ys"
  unfolding scalar_mult_def by simp

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

lemma opening_vec_scale:
  "opening_vec (opening_scale k op) = scalar_mult k (opening_vec op)"
  unfolding opening_scale_def opening_vec_def
  by (simp add: scalar_mult_append_eq)

lemma inner_prod_scalar_mult_right:
  "inner_prod u (scalar_mult c v) = c * inner_prod u v"
proof -
  let ?n = "min (length u) (length v)"
  have "inner_prod u (scalar_mult c v) =
        (\<Sum>i = 0 ..< ?n. u ! i * ((scalar_mult c v) ! i))"
    by (simp add: inner_prod_nth_min scalar_mult_length)
  also have "... = (\<Sum>i = 0 ..< ?n. u ! i * (c * v ! i))"
  proof (rule sum.cong, simp)
    fix i
    assume "i \<in> {0 ..< ?n}"
    then have i_v: "i < length v"
      by auto
    show "u ! i * (scalar_mult c v ! i) = u ! i * (c * v ! i)"
      using i_v by (simp add: scalar_mult_def)
  qed
  also have "... = (\<Sum>i = 0 ..< ?n. c * (u ! i * v ! i))"
    by (simp add: algebra_simps)
  also have "... = c * (\<Sum>i = 0 ..< ?n. u ! i * v ! i)"
    by (simp add: sum_distrib_left)
  also have "... = c * inner_prod u v"
    by (simp add: inner_prod_nth_min)
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
    have "mat_vec_mult A (scalar_mult c v) ! i = inner_prod (A ! i) (scalar_mult c v)"
      using i_A by (simp add: mat_vec_mult_nth)
    also have "... = c * inner_prod (A ! i) v"
      by (rule inner_prod_scalar_mult_right)
    also have "... = c * (mat_vec_mult A v ! i)"
      using i_A by (simp add: mat_vec_mult_nth)
    also have "... = scalar_mult c (mat_vec_mult A v) ! i"
      using i_A by (simp add: scalar_mult_def mat_vec_mult_length)
    finally show ?thesis .
  qed
qed

lemma vec_mod_scalar_eq:
  assumes q_pos: "q > 0"
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
      using lhs rhs q_pos by (simp add: mod_mult_right_eq)
  qed
qed

lemma commit_scale_hom:
  assumes q_pos: "q > 0"
  shows "commit ck (opening_scale c op) q =
    vec_mod (scalar_mult c (commit ck op q)) q"
proof -
  have raw:
    "mat_vec_mult ck (opening_vec (opening_scale c op)) =
      scalar_mult c (mat_vec_mult ck (opening_vec op))"
    unfolding opening_vec_scale
    by (simp add: mat_vec_mult_scalar_eq)
  have "commit ck (opening_scale c op) q =
        vec_mod (mat_vec_mult ck (opening_vec (opening_scale c op))) q"
    unfolding commit_def by simp
  also have "... = vec_mod (scalar_mult c (mat_vec_mult ck (opening_vec op))) q"
    using raw by simp
  also have "... =
        vec_mod (scalar_mult c (vec_mod (mat_vec_mult ck (opening_vec op)) q)) q"
    using vec_mod_scalar_eq[OF q_pos, of c "mat_vec_mult ck (opening_vec op)"] by simp
  also have "... = vec_mod (scalar_mult c (commit ck op q)) q"
    unfolding commit_def by simp
  finally show ?thesis .
qed

lemma all_bit_pairs_length:
  assumes "all_bit_pairs p ops_bits ops_comps"
  shows "length ops_bits = length ops_comps"
  using assms
  by (induct ops_bits ops_comps rule: all_bit_pairs.induct) auto

lemma all_bit_pairs_scalar_bits:
  assumes "all_bit_pairs p ops_bits ops_comps"
  shows "all_valid_scalar_openings p ops_bits"
  using assms
proof (induct ops_bits arbitrary: ops_comps)
  case Nil
  then show ?case
    by (cases ops_comps) simp_all
next
  case (Cons op_bit ops_bits)
  then obtain op_comp ops_comps'
    where comps_eq: "ops_comps = op_comp # ops_comps'"
    by (cases ops_comps) auto
  have pair_ok: "bit_pair_relation p op_bit op_comp"
    using Cons.prems comps_eq by simp
  have head_bit: "valid_scalar_opening p op_bit"
    using pair_ok unfolding bit_pair_relation_def valid_bit_opening_def by simp
  have tail_bits: "all_valid_scalar_openings p ops_bits"
    using Cons.hyps[of ops_comps'] Cons.prems comps_eq by simp
  show ?case
    using head_bit tail_bits by simp
qed

lemma all_bit_pairs_scalar_comps:
  assumes "all_bit_pairs p ops_bits ops_comps"
  shows "all_valid_scalar_openings p ops_comps"
  using assms
proof (induct ops_bits arbitrary: ops_comps)
  case Nil
  then show ?case
    by (cases ops_comps) simp_all
next
  case (Cons op_bit ops_bits)
  then obtain op_comp ops_comps'
    where comps_eq: "ops_comps = op_comp # ops_comps'"
    by (cases ops_comps) auto
  have pair_ok: "bit_pair_relation p op_bit op_comp"
    using Cons.prems comps_eq by simp
  have head_comp: "valid_scalar_opening p op_comp"
    using pair_ok unfolding bit_pair_relation_def valid_bit_opening_def by simp
  have tail_comps: "all_valid_scalar_openings p ops_comps'"
    using Cons.hyps[of ops_comps'] Cons.prems comps_eq by simp
  show ?case
    using head_comp tail_comps comps_eq by simp
qed

lemma weighted_opening_msg_eq:
  assumes "all_valid_scalar_openings p ops"
  shows "open_msg (weighted_opening p B ops) = [recompose B (map amount_of_opening ops)]"
  using assms
proof (induct ops)
  case Nil
  then show ?case
    by (simp add: zero_opening_def)
next
  case (Cons op ops)
  have op_ok: "valid_scalar_opening p op"
    using Cons.prems by simp
  have op_msg: "open_msg op = [amount_of_opening op]"
    using amount_of_opening_eq_hd[OF op_ok] .
  have rest_msg:
    "open_msg (weighted_opening p B ops) = [recompose B (map amount_of_opening ops)]"
    using Cons.hyps Cons.prems by simp
  show ?case
    unfolding weighted_opening.simps opening_add_def opening_scale_def
    using op_msg rest_msg
    by (simp add: scalar_mult_def vec_add_def)
qed

lemma weighted_opening_rand_len:
  assumes params_ok: "valid_scalar_commit_params p"
      and ops_ok: "all_valid_scalar_openings p ops"
  shows "length (open_rand (weighted_opening p B ops)) = cp_n2 p"
  using ops_ok
proof (induct ops)
  case Nil
  then show ?case
    by (simp add: zero_opening_def)
next
  case (Cons op ops)
  have op_len: "length (open_rand op) = cp_n2 p"
    using Cons.prems by (auto intro: valid_scalar_opening_rand_len)
  have rest_len: "length (open_rand (weighted_opening p B ops)) = cp_n2 p"
    using Cons.hyps Cons.prems params_ok by simp
  show ?case
    unfolding weighted_opening.simps opening_add_def opening_scale_def
    using op_len rest_len
    by (simp add: scalar_mult_length vec_add_length)
qed

lemma rand_commit_zero:
  assumes params_ok: "valid_scalar_commit_params p"
      and key_ok: "valid_commit_key p ck"
  shows "rand_commit p ck (replicate (cp_n2 p) 0) = replicate (cp_m p) 0"
proof -
  have raw_zero:
    "mat_vec_mult (rand_commit_key p ck) (replicate (cp_n2 p) 0) =
      replicate (cp_m p) 0"
  proof (intro nth_equalityI)
    show "length (mat_vec_mult (rand_commit_key p ck) (replicate (cp_n2 p) 0)) =
          length (replicate (cp_m p) 0)"
      using rand_commit_key_dims(1)[OF key_ok]
      by (simp add: mat_vec_mult_length)
  next
    fix i
    assume i_lt: "i < length (mat_vec_mult (rand_commit_key p ck) (replicate (cp_n2 p) 0))"
    then have i_key: "i < length (rand_commit_key p ck)"
      by (simp add: mat_vec_mult_length)
    have row_len: "length (rand_commit_key p ck ! i) = cp_n2 p"
      using i_key rand_commit_key_dims(2)[OF key_ok]
      by (simp add: nth_mem)
    show "mat_vec_mult (rand_commit_key p ck) (replicate (cp_n2 p) 0) ! i =
          replicate (cp_m p) 0 ! i"
    proof -
      have "mat_vec_mult (rand_commit_key p ck) (replicate (cp_n2 p) 0) ! i =
            inner_prod (rand_commit_key p ck ! i) (replicate (cp_n2 p) 0)"
        using i_key by (simp add: mat_vec_mult_nth)
      also have "... = (\<Sum>j = 0 ..< cp_n2 p. rand_commit_key p ck ! i ! j * 0)"
        using row_len by (simp add: inner_prod_nth_min)
      also have "... = 0"
        by simp
      finally show ?thesis
        using i_key rand_commit_key_dims(1)[OF key_ok] by simp
    qed
  qed
  have "rand_commit p ck (replicate (cp_n2 p) 0) =
        vec_mod (mat_vec_mult (rand_commit_key p ck) (replicate (cp_n2 p) 0)) (cp_q p)"
    unfolding rand_commit_def by simp
  also have "... = vec_mod (replicate (cp_m p) 0) (cp_q p)"
    using raw_zero by simp
  also have "... = replicate (cp_m p) 0"
    using valid_scalar_commit_params_props(5)[OF params_ok]
    by (simp add: vec_mod_def)
  finally show ?thesis .
qed

lemma weighted_commitment_from_openings:
  assumes params_ok: "valid_scalar_commit_params p"
      and key_ok: "valid_commit_key p ck"
      and ops_ok: "all_valid_scalar_openings p ops"
  shows "weighted_commitment p ck B (map (\<lambda>op. commit ck op (cp_q p)) ops) =
    commit ck (weighted_opening p B ops) (cp_q p)"
  using ops_ok
proof (induct ops)
  case Nil
  have zero_valid: "valid_vec (replicate (cp_n2 p) 0) (cp_n2 p)"
    unfolding valid_vec_def by simp
  have "weighted_commitment p ck B [] = rand_commit p ck (replicate (cp_n2 p) 0)"
    by simp
  also have "... = commit ck (zero_opening (replicate (cp_n2 p) 0)) (cp_q p)"
    using commit_zero_opening_eq_rand_commit[OF params_ok key_ok zero_valid] by simp
  finally show ?case
    by simp
next
  case (Cons op ops)
  have op_ok: "valid_scalar_opening p op"
    using Cons.prems by simp
  have rest_ok: "all_valid_scalar_openings p ops"
    using Cons.prems by simp
  have q_pos: "cp_q p > 0"
    using valid_scalar_commit_params_props(5)[OF params_ok] by simp
  have ih:
    "weighted_commitment p ck B (map (\<lambda>op. commit ck op (cp_q p)) ops) =
      commit ck (weighted_opening p B ops) (cp_q p)"
    using Cons.hyps[OF rest_ok] .
  have commit_idemp:
    "vec_mod (commit ck op (cp_q p)) (cp_q p) = commit ck op (cp_q p)"
    using q_pos unfolding commit_def
    by (simp add: vec_mod_idemp)
  have msg_len:
    "length (open_msg op) = length (open_msg (opening_scale B (weighted_opening p B ops)))"
  proof -
    have n1_one: "cp_n1 p = 1"
      using valid_scalar_commit_params_props(2)[OF params_ok] .
    have "length (open_msg op) = cp_n1 p"
      using op_ok unfolding valid_scalar_opening_def by (auto dest: valid_opening_msg_len)
    moreover have "open_msg (weighted_opening p B ops) = [recompose B (map amount_of_opening ops)]"
      using weighted_opening_msg_eq[OF rest_ok] .
    ultimately show ?thesis
      using n1_one unfolding opening_scale_def by (simp add: scalar_mult_length)
  qed
  have rand_len:
    "length (open_rand op) = length (open_rand (opening_scale B (weighted_opening p B ops)))"
  proof -
    have "length (open_rand op) = cp_n2 p"
      using op_ok by (rule valid_scalar_opening_rand_len)
    moreover have "length (open_rand (weighted_opening p B ops)) = cp_n2 p"
      using weighted_opening_rand_len[OF params_ok rest_ok] .
    ultimately show ?thesis
      unfolding opening_scale_def by (simp add: scalar_mult_length)
  qed
  have step_add:
    "commit ck (weighted_opening p B (op # ops)) (cp_q p) =
      vec_mod
        (vec_add (commit ck op (cp_q p))
                 (commit ck (opening_scale B (weighted_opening p B ops)) (cp_q p)))
        (cp_q p)"
    unfolding weighted_opening.simps
    using commit_add_hom[OF msg_len rand_len q_pos] by simp
  have len_eq:
    "length (commit ck op (cp_q p)) =
     length (scalar_mult B (weighted_commitment p ck B (map (\<lambda>op. commit ck op (cp_q p)) ops)))"
  proof -
    have "length (weighted_commitment p ck B (map (\<lambda>op. commit ck op (cp_q p)) ops)) =
          length ck"
      using ih by (simp add: commit_length)
    then show ?thesis
      by (simp add: commit_length scalar_mult_length)
  qed
  show ?case
  proof -
    have "weighted_commitment p ck B (map (\<lambda>op. commit ck op (cp_q p)) (op # ops)) =
          vec_mod
            (vec_add (commit ck op (cp_q p))
                     (scalar_mult B
                       (weighted_commitment p ck B (map (\<lambda>op. commit ck op (cp_q p)) ops))))
            (cp_q p)"
      by simp
    also have "... =
          vec_mod
            (vec_add (vec_mod (commit ck op (cp_q p)) (cp_q p))
                     (vec_mod
                       (scalar_mult B
                         (weighted_commitment p ck B (map (\<lambda>op. commit ck op (cp_q p)) ops)))
                       (cp_q p)))
            (cp_q p)"
      using vec_mod_add_eq[OF len_eq q_pos] by simp
    also have "... =
          vec_mod
            (vec_add (commit ck op (cp_q p))
                     (vec_mod
                       (scalar_mult B
                         (weighted_commitment p ck B (map (\<lambda>op. commit ck op (cp_q p)) ops)))
                       (cp_q p)))
            (cp_q p)"
      using commit_idemp by simp
    also have "... =
          vec_mod
            (vec_add (commit ck op (cp_q p))
                     (commit ck (opening_scale B (weighted_opening p B ops)) (cp_q p)))
            (cp_q p)"
      using ih commit_scale_hom[OF q_pos, of ck B "weighted_opening p B ops"]
      by simp
    also have "... = commit ck (weighted_opening p B (op # ops)) (cp_q p)"
      using step_add by simp
    finally show ?thesis .
  qed
qed

lemma weighted_opening_rand_bounded_base2:
  assumes params_ok: "valid_scalar_commit_params p"
      and ops_ok: "all_valid_scalar_openings p ops"
  shows "all_bounded (open_rand (weighted_opening p 2 ops))
           ((2 ^ length ops - 1) * cp_beta p)"
  using ops_ok
proof (induct ops)
  case Nil
  then show ?case
    by (simp add: zero_opening_def all_bounded_def)
next
  case (Cons op ops)
  have op_ok: "valid_scalar_opening p op"
    using Cons.prems by simp
  have rest_ok: "all_valid_scalar_openings p ops"
    using Cons.prems by simp
  have b_head: "all_bounded (open_rand op) (cp_beta p)"
    using op_ok unfolding valid_scalar_opening_def valid_opening_def all_bounded_def
    by auto
  have b_rest:
    "all_bounded (open_rand (weighted_opening p 2 ops))
      ((2 ^ length ops - 1) * cp_beta p)"
    using Cons.hyps rest_ok by simp
  have rest_len:
    "length (open_rand (weighted_opening p 2 ops)) = cp_n2 p"
    using weighted_opening_rand_len[OF params_ok rest_ok] .
  have head_len: "length (open_rand op) = cp_n2 p"
    using op_ok by (rule valid_scalar_opening_rand_len)
  have scaled_rest:
    "all_bounded (scalar_mult 2 (open_rand (weighted_opening p 2 ops)))
      (2 * ((2 ^ length ops - 1) * cp_beta p))"
    using scalar_mult_bounded[OF b_rest, of 2] by simp
  have add_bound:
    "all_bounded
      (vec_add (open_rand op) (scalar_mult 2 (open_rand (weighted_opening p 2 ops))))
      (cp_beta p + 2 * ((2 ^ length ops - 1) * cp_beta p))"
    using vec_add_bounded[OF b_head scaled_rest]
    using head_len rest_len by (simp add: scalar_mult_length)
  have final_bound:
    "cp_beta p + 2 * ((2 ^ length ops - 1) * cp_beta p) =
      (2 ^ length (op # ops) - 1) * cp_beta p"
    by (simp add: algebra_simps)
  show ?case
    unfolding weighted_opening.simps opening_add_def opening_scale_def
    using add_bound final_bound
    by (simp add: scalar_mult_length)
qed

lemma range_amount_opening_zero_message:
  assumes rel: "range_relation p ck c_amount op_amount ops_bits ops_comps"
  shows "open_msg (range_amount_opening p op_amount ops_bits) = [0]"
proof -
  have params_ok: "valid_scalar_commit_params p"
    using rel unfolding range_relation_def by simp
  have amount_open_ok: "valid_opening p op_amount"
    using rel unfolding range_relation_def verify_opening_def by simp
  have amount_ok: "valid_scalar_opening p op_amount"
    using params_ok amount_open_ok
    unfolding valid_scalar_opening_def by simp
  have bits_ok: "all_valid_scalar_openings p ops_bits"
    using rel all_bit_pairs_scalar_bits unfolding range_relation_def by blast
  have amount_eq:
    "amount_of_opening op_amount = recompose 2 (map amount_of_opening ops_bits)"
    using rel unfolding range_relation_def by simp
  have amount_msg: "open_msg op_amount = [amount_of_opening op_amount]"
    using amount_of_opening_eq_hd[OF amount_ok] .
  have bits_msg:
    "open_msg (weighted_opening p 2 ops_bits) =
      [recompose 2 (map amount_of_opening ops_bits)]"
    using weighted_opening_msg_eq[OF bits_ok] .
  show ?thesis
    unfolding range_amount_opening_def opening_sub_def
    using amount_msg bits_msg amount_eq
    by (simp add: vec_sub_def)
qed

lemma range_amount_randomness_length:
  assumes rel: "range_relation p ck c_amount op_amount ops_bits ops_comps"
  shows "length (range_amount_randomness p op_amount ops_bits) = cp_n2 p"
proof -
  have params_ok: "valid_scalar_commit_params p"
    using rel unfolding range_relation_def by simp
  have amount_open_ok: "valid_opening p op_amount"
    using rel unfolding range_relation_def verify_opening_def by simp
  have amount_ok: "valid_scalar_opening p op_amount"
    using params_ok amount_open_ok
    unfolding valid_scalar_opening_def by simp
  have bits_ok: "all_valid_scalar_openings p ops_bits"
    using rel all_bit_pairs_scalar_bits unfolding range_relation_def by blast
  have amount_len: "length (open_rand op_amount) = cp_n2 p"
    using amount_ok by (rule valid_scalar_opening_rand_len)
  have bits_len: "length (open_rand (weighted_opening p 2 ops_bits)) = cp_n2 p"
    using weighted_opening_rand_len[OF params_ok bits_ok] .
  show ?thesis
    unfolding range_amount_randomness_def range_amount_opening_def
            opening_sub_def
    using amount_len bits_len by (simp add: vec_sub_length)
qed

lemma range_amount_randomness_bounded:
  assumes rel: "range_relation p ck c_amount op_amount ops_bits ops_comps"
  shows "all_bounded (range_amount_randomness p op_amount ops_bits)
           (range_amount_witness_bound p (length ops_bits))"
proof -
  have params_ok: "valid_scalar_commit_params p"
    using rel unfolding range_relation_def by simp
  have amount_open_ok: "valid_opening p op_amount"
    using rel unfolding range_relation_def verify_opening_def by simp
  have amount_ok: "valid_scalar_opening p op_amount"
    using params_ok amount_open_ok
    unfolding valid_scalar_opening_def by simp
  have bits_ok: "all_valid_scalar_openings p ops_bits"
    using rel all_bit_pairs_scalar_bits unfolding range_relation_def by blast
  have b_amount: "all_bounded (open_rand op_amount) (cp_beta p)"
    using amount_ok unfolding valid_scalar_opening_def valid_opening_def all_bounded_def
    by auto
  have b_bits:
    "all_bounded (open_rand (weighted_opening p 2 ops_bits))
      ((2 ^ length ops_bits - 1) * cp_beta p)"
    using weighted_opening_rand_bounded_base2[OF params_ok bits_ok] .
  have len_eq:
    "length (open_rand op_amount) = length (open_rand (weighted_opening p 2 ops_bits))"
    using amount_ok valid_scalar_opening_rand_len[OF amount_ok]
          weighted_opening_rand_len[OF params_ok bits_ok]
    by simp
  have sub_bound:
    "all_bounded
      (vec_sub (open_rand op_amount) (open_rand (weighted_opening p 2 ops_bits)))
      (cp_beta p + ((2 ^ length ops_bits - 1) * cp_beta p))"
    using vec_sub_bounded[OF b_amount b_bits] len_eq by simp
  have final_bound:
    "cp_beta p + ((2 ^ length ops_bits - 1) * cp_beta p) =
      range_amount_witness_bound p (length ops_bits)"
    unfolding range_amount_witness_bound_def by (simp add: algebra_simps)
  show ?thesis
    unfolding range_amount_randomness_def range_amount_opening_def opening_sub_def
    using sub_bound final_bound by simp
qed

lemma range_amount_commitment_from_relation:
  assumes rel: "range_relation p ck c_amount op_amount ops_bits ops_comps"
  shows "range_amount_commitment p ck c_amount
           (map (\<lambda>op. commit ck op (cp_q p)) ops_bits) =
         rand_commit p ck (range_amount_randomness p op_amount ops_bits)"
proof -
  have params_ok: "valid_scalar_commit_params p"
    using rel unfolding range_relation_def by simp
  have key_ok: "valid_commit_key p ck"
    using rel unfolding range_relation_def by simp
  have amount_verify: "verify_opening p ck c_amount op_amount"
    using rel unfolding range_relation_def by simp
  have amount_open_ok: "valid_opening p op_amount"
    using amount_verify unfolding verify_opening_def by simp
  have amount_ok: "valid_scalar_opening p op_amount"
    using params_ok amount_open_ok unfolding valid_scalar_opening_def by simp
  have bits_ok: "all_valid_scalar_openings p ops_bits"
    using rel all_bit_pairs_scalar_bits unfolding range_relation_def by blast
  have q_pos: "cp_q p > 0"
    using valid_scalar_commit_params_props(5)[OF params_ok] by simp
  have weighted_commit:
    "weighted_commitment p ck 2 (map (\<lambda>op. commit ck op (cp_q p)) ops_bits) =
      commit ck (weighted_opening p 2 ops_bits) (cp_q p)"
    using weighted_commitment_from_openings[OF params_ok key_ok bits_ok] .
  have n1_one: "cp_n1 p = 1"
    using valid_scalar_commit_params_props(2)[OF params_ok] .
  have msg_len:
    "length (open_msg op_amount) = length (open_msg (weighted_opening p 2 ops_bits))"
  proof -
    have "length (open_msg op_amount) = cp_n1 p"
      using amount_ok unfolding valid_scalar_opening_def by (auto dest: valid_opening_msg_len)
    moreover have "open_msg (weighted_opening p 2 ops_bits) =
      [recompose 2 (map amount_of_opening ops_bits)]"
      using weighted_opening_msg_eq[OF bits_ok] .
    ultimately show ?thesis
      using n1_one by simp
  qed
  have rand_len:
    "length (open_rand op_amount) = length (open_rand (weighted_opening p 2 ops_bits))"
  proof -
    have "length (open_rand op_amount) = cp_n2 p"
      using amount_ok by (rule valid_scalar_opening_rand_len)
    moreover have "length (open_rand (weighted_opening p 2 ops_bits)) = cp_n2 p"
      using weighted_opening_rand_len[OF params_ok bits_ok] .
    ultimately show ?thesis by simp
  qed
  have amount_commit:
    "commit ck (range_amount_opening p op_amount ops_bits) (cp_q p) =
      range_amount_commitment p ck c_amount
        (map (\<lambda>op. commit ck op (cp_q p)) ops_bits)"
    unfolding range_amount_opening_def range_amount_commitment_def
    using commit_sub_hom[OF msg_len rand_len q_pos]
          verify_opening_eq[OF amount_verify] weighted_commit
    by simp
  have zero_msg:
    "open_msg (range_amount_opening p op_amount ops_bits) = [0]"
    using range_amount_opening_zero_message[OF rel] .
  have rand_valid:
    "valid_vec (range_amount_randomness p op_amount ops_bits) (cp_n2 p)"
    using range_amount_randomness_length[OF rel]
    unfolding valid_vec_def by simp
  obtain msg rnd where amount_fields:
    "range_amount_opening p op_amount ops_bits =
      \<lparr> open_msg = msg, open_rand = rnd \<rparr>"
    by (cases "range_amount_opening p op_amount ops_bits") auto
  have msg_eq: "msg = [0]"
    using zero_msg amount_fields by simp
  have rnd_eq: "rnd = range_amount_randomness p op_amount ops_bits"
    using amount_fields by (simp add: range_amount_randomness_def)
  have amount_zero:
    "range_amount_opening p op_amount ops_bits =
      zero_opening (range_amount_randomness p op_amount ops_bits)"
    using amount_fields msg_eq rnd_eq
    by (simp add: zero_opening_def)
  have zero_commit:
    "commit ck (range_amount_opening p op_amount ops_bits) (cp_q p) =
      rand_commit p ck (range_amount_randomness p op_amount ops_bits)"
    using commit_zero_opening_eq_rand_commit[OF params_ok key_ok rand_valid]
          amount_zero
    by simp
  from amount_commit zero_commit show ?thesis
    by simp
qed

lemma range_amount_residual_relation_from_openings:
  assumes rel: "range_relation p ck c_amount op_amount ops_bits ops_comps"
  shows "range_amount_residual_relation p (length ops_bits) ck
           (range_amount_commitment p ck c_amount
             (map (\<lambda>op. commit ck op (cp_q p)) ops_bits))
           (range_amount_randomness p op_amount ops_bits)"
proof -
  have params_ok: "valid_scalar_commit_params p"
    using rel unfolding range_relation_def by simp
  have key_ok: "valid_commit_key p ck"
    using rel unfolding range_relation_def by simp
  have rand_len:
    "valid_vec (range_amount_randomness p op_amount ops_bits) (cp_n2 p)"
    using range_amount_randomness_length[OF rel] unfolding valid_vec_def by simp
  have rand_bound:
    "all_bounded (range_amount_randomness p op_amount ops_bits)
      (range_amount_witness_bound p (length ops_bits))"
    using range_amount_randomness_bounded[OF rel] .
  have relation_eq:
    "rand_commit p ck (range_amount_randomness p op_amount ops_bits) =
      range_amount_commitment p ck c_amount
        (map (\<lambda>op. commit ck op (cp_q p)) ops_bits)"
    using range_amount_commitment_from_relation[OF rel] by simp
  show ?thesis
    unfolding range_amount_residual_relation_def valid_range_amount_witness_def
    using params_ok key_ok rand_len rand_bound relation_eq
    by auto
qed

lemma one_opening_valid:
  assumes params_ok: "valid_scalar_commit_params p"
  shows "valid_scalar_opening p (one_opening p)"
proof -
  have beta_pos: "cp_beta p > 0"
    using valid_scalar_commit_params_props(6)[OF params_ok] .
  have beta_ge_one: "1 \<le> cp_beta p"
    using beta_pos by simp
  show ?thesis
    unfolding valid_scalar_opening_def one_opening_def valid_opening_def
    using params_ok valid_scalar_commit_params_props(2,3)[OF params_ok]
          beta_ge_one
    by (auto simp: valid_vec_def all_bounded_def)
qed

lemma valid_bit_opening_amount_bound:
  assumes "valid_bit_opening p op"
  shows "abs (amount_of_opening op) \<le> 1"
proof -
  have scalar_ok: "valid_scalar_opening p op"
    using assms unfolding valid_bit_opening_def by simp
  have msg_eq: "open_msg op = [amount_of_opening op]"
    using amount_of_opening_eq_hd[OF scalar_ok] .
  have msg_bound: "all_bounded (open_msg op) 1"
    using assms unfolding valid_bit_opening_def by simp
  show ?thesis
    using msg_eq msg_bound
    unfolding all_bounded_def
    by auto
qed

lemma bit_pair_relation_values:
  assumes "bit_pair_relation p op_bit op_comp"
  shows "amount_of_opening op_bit = 0 \<or> amount_of_opening op_bit = 1"
    and "amount_of_opening op_comp = 0 \<or> amount_of_opening op_comp = 1"
proof -
  have bit_bound: "abs (amount_of_opening op_bit) \<le> 1"
    using assms unfolding bit_pair_relation_def
    by (auto intro: valid_bit_opening_amount_bound)
  have comp_bound: "abs (amount_of_opening op_comp) \<le> 1"
    using assms unfolding bit_pair_relation_def
    by (auto intro: valid_bit_opening_amount_bound)
  have sum_one:
    "amount_of_opening op_bit + amount_of_opening op_comp = 1"
    using assms unfolding bit_pair_relation_def by simp
  show "amount_of_opening op_bit = 0 \<or> amount_of_opening op_bit = 1"
    using bit_bound comp_bound sum_one by linarith
  show "amount_of_opening op_comp = 0 \<or> amount_of_opening op_comp = 1"
    using bit_bound comp_bound sum_one by linarith
qed

lemma recompose_bits_nonneg:
  assumes bits: "\<forall>d \<in> set ds. d = 0 \<or> d = 1"
  shows "0 \<le> recompose 2 ds"
  using bits
proof (induct ds)
  case Nil
  then show ?case by simp
next
  case (Cons d ds)
  have d_bit: "d = 0 \<or> d = 1"
    using Cons.prems by auto
  have ds_bits: "\<forall>x \<in> set ds. x = 0 \<or> x = 1"
    using Cons.prems by simp
  have ih_nonneg: "0 \<le> recompose 2 ds"
    using Cons.hyps[OF ds_bits] .
  show ?case
    using d_bit ih_nonneg by auto
qed

lemma recompose_bits_upper:
  assumes bits: "\<forall>d \<in> set ds. d = 0 \<or> d = 1"
  shows "recompose 2 ds < 2 ^ length ds"
  using bits
proof (induct ds)
  case Nil
  then show ?case by simp
next
  case (Cons d ds)
  have d_bit: "d = 0 \<or> d = 1"
    using Cons.prems by auto
  have ds_bits: "\<forall>x \<in> set ds. x = 0 \<or> x = 1"
    using Cons.prems by simp
  have ih_upper: "recompose 2 ds < 2 ^ length ds"
    using Cons.hyps[OF ds_bits] .
  show ?case
    using d_bit ih_upper by auto
qed

lemma recompose_bits_range:
  assumes "\<forall>d \<in> set ds. d = 0 \<or> d = 1"
  shows "0 \<le> recompose 2 ds"
    and "recompose 2 ds < 2 ^ length ds"
  using recompose_bits_nonneg[OF assms] recompose_bits_upper[OF assms]
  by simp_all

lemma range_relation_in_range:
  assumes rel: "range_relation p ck c_amount op_amount ops_bits ops_comps"
  shows "0 \<le> amount_of_opening op_amount"
    and "amount_of_opening op_amount < 2 ^ length ops_bits"
proof -
  have pairs_ok: "all_bit_pairs p ops_bits ops_comps"
    using rel unfolding range_relation_def by simp
  have amount_eq:
    "amount_of_opening op_amount = recompose 2 (map amount_of_opening ops_bits)"
    using rel unfolding range_relation_def by simp
  have bits_are_bits:
    "\<forall>d \<in> set (map amount_of_opening ops_bits). d = 0 \<or> d = 1"
    using pairs_ok
  proof (induct ops_bits arbitrary: ops_comps)
    case Nil
    then show ?case by (cases ops_comps) simp_all
  next
    case (Cons op ops)
    then obtain op_comp ops_comps'
      where comps_eq: "ops_comps = op_comp # ops_comps'"
      by (cases ops_comps) auto
    have head_pair: "bit_pair_relation p op op_comp"
      using Cons.prems comps_eq by simp
    have tail_pairs: "all_bit_pairs p ops ops_comps'"
      using Cons.prems comps_eq by simp
    have head_bit:
      "amount_of_opening op = 0 \<or> amount_of_opening op = 1"
      using bit_pair_relation_values(1)[OF head_pair] .
    have tail_bits:
      "\<forall>d \<in> set (map amount_of_opening ops). d = 0 \<or> d = 1"
      using Cons.hyps[OF tail_pairs] .
    show ?case
      using head_bit tail_bits by simp
  qed
  have nonneg_bits:
    "0 \<le> recompose 2 (map amount_of_opening ops_bits)"
    using recompose_bits_range(1)[OF bits_are_bits] .
  have upper_bits:
    "recompose 2 (map amount_of_opening ops_bits) < 2 ^ length ops_bits"
    using recompose_bits_range(2)[OF bits_are_bits] by simp
  show "0 \<le> amount_of_opening op_amount"
    using amount_eq nonneg_bits by simp
  show "amount_of_opening op_amount < 2 ^ length ops_bits"
    using amount_eq upper_bits by simp
qed

lemma range_pair_opening_zero_message:
  assumes pair: "bit_pair_relation p op_bit op_comp"
  shows "open_msg (range_pair_opening p op_bit op_comp) = [0]"
proof -
  have bit_ok: "valid_scalar_opening p op_bit"
    using pair unfolding bit_pair_relation_def valid_bit_opening_def by simp
  have comp_ok: "valid_scalar_opening p op_comp"
    using pair unfolding bit_pair_relation_def valid_bit_opening_def by simp
  have sum_one:
    "amount_of_opening op_bit + amount_of_opening op_comp = 1"
    using pair unfolding bit_pair_relation_def by simp
  have bit_msg: "open_msg op_bit = [amount_of_opening op_bit]"
    using amount_of_opening_eq_hd[OF bit_ok] .
  have comp_msg: "open_msg op_comp = [amount_of_opening op_comp]"
    using amount_of_opening_eq_hd[OF comp_ok] .
  show ?thesis
    unfolding range_pair_opening_def opening_sub_def opening_add_def one_opening_def
    using bit_msg comp_msg sum_one
    by (simp add: vec_add_def vec_sub_def)
qed

lemma range_pair_randomness_length:
  assumes pair: "bit_pair_relation p op_bit op_comp"
  shows "length (range_pair_randomness p op_bit op_comp) = cp_n2 p"
proof -
  have bit_ok: "valid_scalar_opening p op_bit"
    using pair unfolding bit_pair_relation_def valid_bit_opening_def by simp
  have comp_ok: "valid_scalar_opening p op_comp"
    using pair unfolding bit_pair_relation_def valid_bit_opening_def by simp
  have bit_len: "length (open_rand op_bit) = cp_n2 p"
    using bit_ok by (rule valid_scalar_opening_rand_len)
  have comp_len: "length (open_rand op_comp) = cp_n2 p"
    using comp_ok by (rule valid_scalar_opening_rand_len)
  show ?thesis
    unfolding range_pair_randomness_def range_pair_opening_def opening_sub_def
              opening_add_def one_opening_def
    using bit_len comp_len
    by (simp add: vec_add_length vec_sub_length)
qed

lemma range_pair_randomness_bounded:
  assumes pair: "bit_pair_relation p op_bit op_comp"
  shows "all_bounded (range_pair_randomness p op_bit op_comp)
           (range_pair_witness_bound p)"
proof -
  have bit_ok: "valid_scalar_opening p op_bit"
    using pair unfolding bit_pair_relation_def valid_bit_opening_def by simp
  have comp_ok: "valid_scalar_opening p op_comp"
    using pair unfolding bit_pair_relation_def valid_bit_opening_def by simp
  have b_bit: "all_bounded (open_rand op_bit) (cp_beta p)"
    using bit_ok unfolding valid_scalar_opening_def valid_opening_def all_bounded_def
    by auto
  have b_comp: "all_bounded (open_rand op_comp) (cp_beta p)"
    using comp_ok unfolding valid_scalar_opening_def valid_opening_def all_bounded_def
    by auto
  have bit_len: "length (open_rand op_bit) = cp_n2 p"
    using bit_ok by (rule valid_scalar_opening_rand_len)
  have comp_len: "length (open_rand op_comp) = cp_n2 p"
    using comp_ok by (rule valid_scalar_opening_rand_len)
  have sum_bound:
    "all_bounded (vec_add (open_rand op_bit) (open_rand op_comp)) (2 * cp_beta p)"
    using vec_add_bounded[OF b_bit b_comp]
    using bit_len comp_len by simp
  have zero_bound: "all_bounded (replicate (cp_n2 p) 0) 0"
    unfolding all_bounded_def by simp
  have sub_bound:
    "all_bounded
      (vec_sub (vec_add (open_rand op_bit) (open_rand op_comp))
               (replicate (cp_n2 p) 0))
      (2 * cp_beta p)"
    using vec_sub_bounded[OF sum_bound zero_bound] by simp
  show ?thesis
    unfolding range_pair_randomness_def range_pair_opening_def opening_sub_def
              opening_add_def one_opening_def range_pair_witness_bound_def
    using sub_bound by simp
qed

lemma range_pair_commitment_from_relation:
  assumes key_ok: "valid_commit_key p ck"
      and pair: "bit_pair_relation p op_bit op_comp"
  shows "range_pair_commitment p ck
           (commit ck op_bit (cp_q p))
           (commit ck op_comp (cp_q p)) =
         rand_commit p ck (range_pair_randomness p op_bit op_comp)"
proof -
  have bit_ok: "valid_scalar_opening p op_bit"
    using pair unfolding bit_pair_relation_def valid_bit_opening_def by simp
  have comp_ok: "valid_scalar_opening p op_comp"
    using pair unfolding bit_pair_relation_def valid_bit_opening_def by simp
  have params_ok: "valid_scalar_commit_params p"
    using bit_ok unfolding valid_scalar_opening_def by simp
  have q_pos: "cp_q p > 0"
    using valid_scalar_commit_params_props(5)[OF params_ok] by simp
  have bit_msg_len: "length (open_msg op_bit) = cp_n1 p"
    using bit_ok unfolding valid_scalar_opening_def
    by (auto dest: valid_opening_msg_len)
  have comp_msg_len: "length (open_msg op_comp) = cp_n1 p"
    using comp_ok unfolding valid_scalar_opening_def
    by (auto dest: valid_opening_msg_len)
  have bit_rand_len: "length (open_rand op_bit) = cp_n2 p"
    using bit_ok by (rule valid_scalar_opening_rand_len)
  have comp_rand_len: "length (open_rand op_comp) = cp_n2 p"
    using comp_ok by (rule valid_scalar_opening_rand_len)
  have msg_len_eq: "length (open_msg op_bit) = length (open_msg op_comp)"
    using bit_msg_len comp_msg_len by simp
  have rand_len_eq: "length (open_rand op_bit) = length (open_rand op_comp)"
    using bit_rand_len comp_rand_len by simp
  have add_msg_len:
    "length (open_msg (opening_add op_bit op_comp)) = length (open_msg (one_opening p))"
    using bit_msg_len comp_msg_len valid_scalar_commit_params_props(2)[OF params_ok]
    unfolding opening_add_def one_opening_def
    by (simp add: vec_add_length)
  have add_rand_len:
    "length (open_rand (opening_add op_bit op_comp)) = length (open_rand (one_opening p))"
    using bit_rand_len comp_rand_len
    unfolding opening_add_def one_opening_def
    by (simp add: vec_add_length)
  have add_commit:
    "commit ck (opening_add op_bit op_comp) (cp_q p) =
      vec_mod
        (vec_add (commit ck op_bit (cp_q p)) (commit ck op_comp (cp_q p)))
        (cp_q p)"
    using commit_add_hom[OF msg_len_eq rand_len_eq q_pos] by simp
  have one_valid: "valid_scalar_opening p (one_opening p)"
    using one_opening_valid[OF params_ok] .
  have one_open_ok: "valid_opening p (one_opening p)"
    using one_valid unfolding valid_scalar_opening_def by simp
  have one_commit_valid: "valid_commitment p (one_commitment p ck)"
    unfolding one_commitment_def
    using commit_valid[OF valid_scalar_commit_params_props(1)[OF params_ok] key_ok]
          one_open_ok
    by simp
  have one_commit_idemp:
    "vec_mod (one_commitment p ck) (cp_q p) = one_commitment p ck"
    using q_pos
    unfolding one_commitment_def commit_def
    by (simp add: vec_mod_idemp)
  have len_eq:
    "length (vec_add (commit ck op_bit (cp_q p)) (commit ck op_comp (cp_q p))) =
      length (one_commitment p ck)"
    by (simp add: commit_length vec_add_length one_commitment_def)
  have pair_commit:
    "commit ck (range_pair_opening p op_bit op_comp) (cp_q p) =
      range_pair_commitment p ck
        (commit ck op_bit (cp_q p))
        (commit ck op_comp (cp_q p))"
  proof -
    have sub_commit:
      "commit ck (range_pair_opening p op_bit op_comp) (cp_q p) =
        vec_mod
          (vec_sub (commit ck (opening_add op_bit op_comp) (cp_q p))
                   (commit ck (one_opening p) (cp_q p)))
          (cp_q p)"
      unfolding range_pair_opening_def
      using commit_sub_hom[OF add_msg_len add_rand_len q_pos] by simp
    have rhs_mod:
      "vec_mod
        (vec_sub (commit ck (opening_add op_bit op_comp) (cp_q p))
                 (commit ck (one_opening p) (cp_q p)))
        (cp_q p) =
       vec_mod
        (vec_sub
          (vec_mod
            (vec_add (commit ck op_bit (cp_q p)) (commit ck op_comp (cp_q p)))
            (cp_q p))
          (one_commitment p ck))
        (cp_q p)"
      unfolding one_commitment_def
      using add_commit by simp
    have sub_mod_eq:
      "vec_mod
        (vec_sub
          (vec_add (commit ck op_bit (cp_q p)) (commit ck op_comp (cp_q p)))
          (one_commitment p ck))
        (cp_q p) =
       vec_mod
        (vec_sub
          (vec_mod
            (vec_add (commit ck op_bit (cp_q p)) (commit ck op_comp (cp_q p)))
            (cp_q p))
          (vec_mod (one_commitment p ck) (cp_q p)))
        (cp_q p)"
      by (rule vec_mod_sub_eq[OF len_eq q_pos])
    have final_mod:
      "vec_mod
        (vec_sub
          (vec_mod
            (vec_add (commit ck op_bit (cp_q p)) (commit ck op_comp (cp_q p)))
            (cp_q p))
          (one_commitment p ck))
        (cp_q p) =
       vec_mod
        (vec_sub
          (vec_add (commit ck op_bit (cp_q p)) (commit ck op_comp (cp_q p)))
          (one_commitment p ck))
        (cp_q p)"
      using sub_mod_eq one_commit_idemp
      by simp
    have "commit ck (range_pair_opening p op_bit op_comp) (cp_q p) =
          vec_mod
            (vec_sub (commit ck (opening_add op_bit op_comp) (cp_q p))
                     (commit ck (one_opening p) (cp_q p)))
            (cp_q p)"
      using sub_commit .
    also have "... =
          vec_mod
            (vec_sub
              (vec_mod
                (vec_add (commit ck op_bit (cp_q p)) (commit ck op_comp (cp_q p)))
                (cp_q p))
              (one_commitment p ck))
            (cp_q p)"
      using rhs_mod .
    also have "... =
          vec_mod
            (vec_sub
              (vec_add (commit ck op_bit (cp_q p)) (commit ck op_comp (cp_q p)))
              (one_commitment p ck))
            (cp_q p)"
      using final_mod .
    finally show ?thesis
      unfolding range_pair_commitment_def .
  qed
  have zero_msg:
    "open_msg (range_pair_opening p op_bit op_comp) = [0]"
    using range_pair_opening_zero_message[OF pair] .
  have rand_valid:
    "valid_vec (range_pair_randomness p op_bit op_comp) (cp_n2 p)"
    using range_pair_randomness_length[OF pair]
    unfolding valid_vec_def by simp
  obtain msg rnd where pair_fields:
    "range_pair_opening p op_bit op_comp =
      \<lparr> open_msg = msg, open_rand = rnd \<rparr>"
    by (cases "range_pair_opening p op_bit op_comp") auto
  have msg_eq: "msg = [0]"
    using zero_msg pair_fields by simp
  have rnd_eq: "rnd = range_pair_randomness p op_bit op_comp"
    using pair_fields by (simp add: range_pair_randomness_def)
  have pair_zero:
    "range_pair_opening p op_bit op_comp =
      zero_opening (range_pair_randomness p op_bit op_comp)"
    using pair_fields msg_eq rnd_eq
    by (simp add: zero_opening_def)
  have zero_commit:
    "commit ck (range_pair_opening p op_bit op_comp) (cp_q p) =
      rand_commit p ck (range_pair_randomness p op_bit op_comp)"
    using commit_zero_opening_eq_rand_commit[OF params_ok key_ok rand_valid]
          pair_zero
    by simp
  from pair_commit zero_commit show ?thesis
    by simp
qed

lemma range_pair_residual_relation_from_openings:
  assumes key_ok: "valid_commit_key p ck"
      and pair: "bit_pair_relation p op_bit op_comp"
  shows "range_pair_residual_relation p ck
           (range_pair_commitment p ck
             (commit ck op_bit (cp_q p))
             (commit ck op_comp (cp_q p)))
           (range_pair_randomness p op_bit op_comp)"
proof -
  have bit_ok: "valid_scalar_opening p op_bit"
    using pair unfolding bit_pair_relation_def valid_bit_opening_def by simp
  have params_ok: "valid_scalar_commit_params p"
    using bit_ok unfolding valid_scalar_opening_def by simp
  have rand_len:
    "valid_vec (range_pair_randomness p op_bit op_comp) (cp_n2 p)"
    using range_pair_randomness_length[OF pair]
    unfolding valid_vec_def by simp
  have rand_bound:
    "all_bounded (range_pair_randomness p op_bit op_comp)
      (range_pair_witness_bound p)"
    using range_pair_randomness_bounded[OF pair] .
  have relation_eq:
    "rand_commit p ck (range_pair_randomness p op_bit op_comp) =
      range_pair_commitment p ck
        (commit ck op_bit (cp_q p))
        (commit ck op_comp (cp_q p))"
    using range_pair_commitment_from_relation[OF key_ok pair] by simp
  show ?thesis
    unfolding range_pair_residual_relation_def valid_range_pair_witness_def
    using params_ok key_ok rand_len rand_bound relation_eq
    by auto
qed

lemma range_pair_randomnesses_length:
  assumes pairs_ok: "all_bit_pairs p ops_bits ops_comps"
  shows "length (range_pair_randomnesses p ops_bits ops_comps) = length ops_bits"
  using pairs_ok
proof (induct ops_bits arbitrary: ops_comps)
  case Nil
  then show ?case
    by (cases ops_comps) simp_all
next
  case (Cons op_bit ops_bits)
  then obtain op_comp ops_comps'
    where comps_eq: "ops_comps = op_comp # ops_comps'"
    by (cases ops_comps) auto
  have tail_pairs: "all_bit_pairs p ops_bits ops_comps'"
    using Cons.prems comps_eq by simp
  have tail_len:
    "length (range_pair_randomnesses p ops_bits ops_comps') = length ops_bits"
    using Cons.hyps[OF tail_pairs] .
  show ?case
    using comps_eq tail_len by simp
qed

lemma range_sigma_announcements_length:
  "length (range_sigma_announcements p ck ys) = length ys"
  by (induct ys) simp_all

lemma range_sigma_responses_length:
  assumes len_eq: "length rs = length ys"
  shows "length (range_sigma_responses rs ys e) = length ys"
  using len_eq
proof (induct rs arbitrary: ys)
  case Nil
  then show ?case
    by (cases ys) simp_all
next
  case (Cons r rs)
  then obtain y ys' where ys_eq: "ys = y # ys'"
    by (cases ys) auto
  have tail_len: "length rs = length ys'"
    using Cons.prems ys_eq by simp
  have ih: "length (range_sigma_responses rs ys' e) = length ys'"
    using Cons.hyps[OF tail_len] .
  show ?case
    using ys_eq ih by simp
qed

lemma range_fs_challenges_length:
  "length (range_fs_challenges p ck c_amount c_bits c_comps a_amounts a_pairss) = range_fs_rounds"
  unfolding range_fs_challenges_def range_fs_rounds_def balance_fs_rounds_def fixed_fs_rounds_def
  by simp

lemma range_fs_challenge_valid:
  assumes params_ok: "valid_scalar_commit_params p"
      and i_lt: "i < range_fs_rounds"
  shows "valid_range_challenge p
           ((range_fs_challenges p ck c_amount c_bits c_comps a_amounts a_pairss) ! i)"
proof -
  have bit:
    "(range_fs_challenges p ck c_amount c_bits c_comps a_amounts a_pairss) ! i = 0 \<or>
     (range_fs_challenges p ck c_amount c_bits c_comps a_amounts a_pairss) ! i = 1"
    using i_lt
    unfolding range_fs_challenges_def range_fs_rounds_def balance_fs_rounds_def fixed_fs_rounds_def
    by (rule bool_fs_challenges_bit)
  show ?thesis
    using params_ok bit
    unfolding valid_range_challenge_def valid_balance_challenge_def
    by auto
qed

lemma range_amount_sigma_announcements_length:
  "length (range_amount_sigma_announcements p ck y_amounts) = length y_amounts"
  unfolding range_amount_sigma_announcements_def
  by simp

lemma range_amount_sigma_responses_length:
  assumes len_eq: "length y_amounts = length es"
  shows "length (range_amount_sigma_responses r_amount y_amounts es) = length y_amounts"
  using len_eq
  unfolding range_amount_sigma_responses_def
  by (simp add: balance_sigma_responds_length)

lemma range_amount_sigma_responses_nth:
  assumes len_eq: "length y_amounts = length es"
      and i_lt: "i < length y_amounts"
  shows "(range_amount_sigma_responses r_amount y_amounts es) ! i =
           balance_sigma_respond r_amount (y_amounts ! i) (es ! i)"
  using assms
  unfolding range_amount_sigma_responses_def
  by (simp add: balance_sigma_responds_nth)

lemma range_pair_sigma_announcement_rounds_length:
  "length (range_pair_sigma_announcement_rounds p ck y_pairss) = length y_pairss"
  unfolding range_pair_sigma_announcement_rounds_def
  by simp

lemma range_pair_sigma_response_rounds_length:
  assumes len_eq: "length y_pairss = length es"
  shows "length (range_pair_sigma_response_rounds rs y_pairss es) = length y_pairss"
  using len_eq
  unfolding range_pair_sigma_response_rounds_def
  by (rule sigma_response_rounds_length)

lemma range_pair_sigma_response_rounds_nth:
  assumes len_eq: "length y_pairss = length es"
      and i_lt: "i < length y_pairss"
  shows "(range_pair_sigma_response_rounds rs y_pairss es) ! i =
           range_sigma_responses rs (y_pairss ! i) (es ! i)"
  using assms
  unfolding range_pair_sigma_response_rounds_def
  by (rule sigma_response_rounds_nth)

lemma range_amount_sigma_response_valid:
  assumes params_ok: "valid_scalar_commit_params p"
      and mask_ok: "valid_range_mask p gamma y"
      and challenge_ok: "valid_range_challenge p e"
      and witness_ok: "valid_range_amount_witness p k r"
  shows "valid_range_amount_response p gamma k e (balance_sigma_respond r y e)"
proof -
  have len_eq: "length y = length r"
    using mask_ok witness_ok
    unfolding valid_range_mask_def valid_range_amount_witness_def valid_vec_def by simp
  have scaled_bounded:
    "all_bounded (scalar_mult e r) (abs e * range_amount_witness_bound p k)"
    using witness_ok
    unfolding valid_range_amount_witness_def
    by (auto intro: scalar_mult_bounded)
  have bounded:
    "all_bounded (vec_add y (scalar_mult e r))
       (gamma + abs e * range_amount_witness_bound p k)"
    using vec_add_bounded[OF _ scaled_bounded]
          mask_ok len_eq
    unfolding valid_range_mask_def
    by (simp add: scalar_mult_length)
  have len_z: "valid_vec (vec_add y (scalar_mult e r)) (cp_n2 p)"
    using mask_ok witness_ok len_eq
    unfolding valid_range_mask_def valid_range_amount_witness_def valid_vec_def
    by (simp add: vec_add_length scalar_mult_length)
  show ?thesis
    using len_z bounded challenge_ok
    unfolding valid_range_amount_response_def range_amount_response_bound_def
              balance_sigma_respond_def
    by simp
qed

lemma range_pair_sigma_response_valid:
  assumes params_ok: "valid_scalar_commit_params p"
      and mask_ok: "valid_range_mask p gamma y"
      and challenge_ok: "valid_range_challenge p e"
      and witness_ok: "valid_range_pair_witness p r"
  shows "valid_range_pair_response p gamma e (balance_sigma_respond r y e)"
proof -
  have len_eq: "length y = length r"
    using mask_ok witness_ok
    unfolding valid_range_mask_def valid_range_pair_witness_def valid_vec_def by simp
  have scaled_bounded:
    "all_bounded (scalar_mult e r) (abs e * range_pair_witness_bound p)"
    using witness_ok
    unfolding valid_range_pair_witness_def
    by (auto intro: scalar_mult_bounded)
  have bounded:
    "all_bounded (vec_add y (scalar_mult e r))
       (gamma + abs e * range_pair_witness_bound p)"
    using vec_add_bounded[OF _ scaled_bounded]
          mask_ok len_eq
    unfolding valid_range_mask_def
    by (simp add: scalar_mult_length)
  have len_z: "valid_vec (vec_add y (scalar_mult e r)) (cp_n2 p)"
    using mask_ok witness_ok len_eq
    unfolding valid_range_mask_def valid_range_pair_witness_def valid_vec_def
    by (simp add: vec_add_length scalar_mult_length)
  show ?thesis
    using len_z bounded challenge_ok
    unfolding valid_range_pair_response_def range_pair_response_bound_def
              balance_sigma_respond_def
    by simp
qed

lemma range_amount_sigma_complete:
  assumes relation: "range_amount_residual_relation p k ck c r"
      and mask_ok: "valid_range_mask p gamma y"
      and challenge_ok: "valid_range_challenge p e"
      and a_def: "a = rand_commit p ck y"
      and z_def: "z = balance_sigma_respond r y e"
  shows "range_amount_sigma_verify p gamma k ck c a e z"
proof -
  obtain params_ok key_ok witness_ok c_eq where
      relation_props:
        "valid_scalar_commit_params p"
        "valid_commit_key p ck"
        "valid_range_amount_witness p k r"
        "rand_commit p ck r = c"
    using relation unfolding range_amount_residual_relation_def by blast
  have a_valid:
    "valid_commitment p a"
    using rand_commit_valid[OF valid_scalar_commit_params_props(1)[OF relation_props(1)] relation_props(2)]
          mask_ok a_def
    unfolding valid_range_mask_def by simp
  have c_valid:
    "valid_commitment p c"
  proof -
    have "valid_commitment p (rand_commit p ck r)"
      using rand_commit_valid[OF valid_scalar_commit_params_props(1)[OF relation_props(1)] relation_props(2)]
            relation_props(3)
      unfolding valid_range_amount_witness_def
      by simp
    then show ?thesis
      using relation_props(4) by simp
  qed
  have z_valid:
    "valid_range_amount_response p gamma k e z"
    using range_amount_sigma_response_valid[OF relation_props(1) mask_ok challenge_ok relation_props(3)]
          z_def by simp
  have verify_eq:
    "rand_commit p ck z = vec_mod (vec_add a (scalar_mult e c)) (cp_q p)"
  proof -
    have len_y: "length y = cp_n2 p"
      using mask_ok unfolding valid_range_mask_def valid_vec_def by simp
    have len_r: "length r = cp_n2 p"
      using relation_props(3)
      unfolding valid_range_amount_witness_def valid_vec_def by simp
    have q_pos: "cp_q p > 0"
      using valid_scalar_commit_params_props(5)[OF relation_props(1)] by linarith
    have len_a: "length a = cp_m p"
      using a_valid unfolding valid_commitment_def valid_vec_def by simp
    have len_c: "length c = cp_m p"
      using c_valid unfolding valid_commitment_def valid_vec_def by simp
    have a_mod: "vec_mod a (cp_q p) = a"
      using a_def q_pos unfolding rand_commit_def by (simp add: vec_mod_idemp)
    have "rand_commit p ck z = rand_commit p ck (vec_add y (scalar_mult e r))"
      using z_def by (simp add: balance_sigma_respond_def)
    also have "... = vec_mod (vec_add (rand_commit p ck y) (rand_commit p ck (scalar_mult e r))) (cp_q p)"
      using rand_commit_add_hom[OF relation_props(2) len_y, of "scalar_mult e r"]
            q_pos len_r
      by (simp add: scalar_mult_length)
    also have "... = vec_mod (vec_add a (rand_commit p ck (scalar_mult e r))) (cp_q p)"
      using a_def by simp
    also have "... = vec_mod (vec_add a (vec_mod (scalar_mult e c) (cp_q p))) (cp_q p)"
      using rand_commit_scalar_hom[OF relation_props(2) len_r q_pos]
            relation_props(4)
      by simp
    also have "... = vec_mod (vec_add a (scalar_mult e c)) (cp_q p)"
      using vec_mod_add_eq[OF _ q_pos, of a "scalar_mult e c"]
            len_a len_c a_mod
      by (simp add: scalar_mult_length)
    finally show ?thesis .
  qed
  show ?thesis
    unfolding range_amount_sigma_verify_def
    using relation_props a_valid challenge_ok z_valid verify_eq by auto
qed

lemma range_pair_sigma_complete:
  assumes relation: "range_pair_residual_relation p ck c r"
      and mask_ok: "valid_range_mask p gamma y"
      and challenge_ok: "valid_range_challenge p e"
      and a_def: "a = rand_commit p ck y"
      and z_def: "z = balance_sigma_respond r y e"
  shows "range_pair_sigma_verify p gamma ck c a e z"
proof -
  obtain params_ok key_ok witness_ok c_eq where
      relation_props:
        "valid_scalar_commit_params p"
        "valid_commit_key p ck"
        "valid_range_pair_witness p r"
        "rand_commit p ck r = c"
    using relation unfolding range_pair_residual_relation_def by blast
  have a_valid:
    "valid_commitment p a"
    using rand_commit_valid[OF valid_scalar_commit_params_props(1)[OF relation_props(1)] relation_props(2)]
          mask_ok a_def
    unfolding valid_range_mask_def by simp
  have c_valid:
    "valid_commitment p c"
  proof -
    have "valid_commitment p (rand_commit p ck r)"
      using rand_commit_valid[OF valid_scalar_commit_params_props(1)[OF relation_props(1)] relation_props(2)]
            relation_props(3)
      unfolding valid_range_pair_witness_def
      by simp
    then show ?thesis
      using relation_props(4) by simp
  qed
  have z_valid:
    "valid_range_pair_response p gamma e z"
    using range_pair_sigma_response_valid[OF relation_props(1) mask_ok challenge_ok relation_props(3)]
          z_def by simp
  have verify_eq:
    "rand_commit p ck z = vec_mod (vec_add a (scalar_mult e c)) (cp_q p)"
  proof -
    have len_y: "length y = cp_n2 p"
      using mask_ok unfolding valid_range_mask_def valid_vec_def by simp
    have len_r: "length r = cp_n2 p"
      using relation_props(3)
      unfolding valid_range_pair_witness_def valid_vec_def by simp
    have q_pos: "cp_q p > 0"
      using valid_scalar_commit_params_props(5)[OF relation_props(1)] by linarith
    have len_a: "length a = cp_m p"
      using a_valid unfolding valid_commitment_def valid_vec_def by simp
    have len_c: "length c = cp_m p"
      using c_valid unfolding valid_commitment_def valid_vec_def by simp
    have a_mod: "vec_mod a (cp_q p) = a"
      using a_def q_pos unfolding rand_commit_def by (simp add: vec_mod_idemp)
    have "rand_commit p ck z = rand_commit p ck (vec_add y (scalar_mult e r))"
      using z_def by (simp add: balance_sigma_respond_def)
    also have "... = vec_mod (vec_add (rand_commit p ck y) (rand_commit p ck (scalar_mult e r))) (cp_q p)"
      using rand_commit_add_hom[OF relation_props(2) len_y, of "scalar_mult e r"]
            q_pos len_r
      by (simp add: scalar_mult_length)
    also have "... = vec_mod (vec_add a (rand_commit p ck (scalar_mult e r))) (cp_q p)"
      using a_def by simp
    also have "... = vec_mod (vec_add a (vec_mod (scalar_mult e c) (cp_q p))) (cp_q p)"
      using rand_commit_scalar_hom[OF relation_props(2) len_r q_pos]
            relation_props(4)
      by simp
    also have "... = vec_mod (vec_add a (scalar_mult e c)) (cp_q p)"
      using vec_mod_add_eq[OF _ q_pos, of a "scalar_mult e c"]
            len_a len_c a_mod
      by (simp add: scalar_mult_length)
    finally show ?thesis .
  qed
  show ?thesis
    unfolding range_pair_sigma_verify_def
    using relation_props a_valid challenge_ok z_valid verify_eq by auto
qed

lemma range_sigma_verify_pairs_complete:
  assumes key_ok: "valid_commit_key p ck"
      and pairs_ok: "all_bit_pairs p ops_bits ops_comps"
      and masks_ok: "valid_range_masks p gamma y_pairs"
      and challenge_ok: "valid_range_challenge p e"
      and len_eq: "length y_pairs = length ops_bits"
  shows "range_sigma_verify_pairs p gamma ck
           (range_pair_commitments p ck
             (map (\<lambda>op. commit ck op (cp_q p)) ops_bits)
             (map (\<lambda>op. commit ck op (cp_q p)) ops_comps))
           (range_sigma_announcements p ck y_pairs)
           e
           (range_sigma_responses
             (range_pair_randomnesses p ops_bits ops_comps)
             y_pairs e)"
  using pairs_ok masks_ok len_eq
proof (induct ops_bits arbitrary: ops_comps y_pairs)
  case Nil
  then have comps_nil: "ops_comps = []"
    by (cases ops_comps) simp_all
  moreover have ys_nil: "y_pairs = []"
    using Nil.prems by (cases y_pairs) simp_all
  ultimately show ?case by simp
next
  case (Cons op_bit ops_bits)
  then obtain op_comp ops_comps'
    where comps_eq: "ops_comps = op_comp # ops_comps'"
    by (cases ops_comps) auto
  from Cons.prems obtain y y_pairs'
    where ys_eq: "y_pairs = y # y_pairs'"
    by (cases y_pairs) auto
  have head_pair: "bit_pair_relation p op_bit op_comp"
    using Cons.prems comps_eq by simp
  have tail_pairs: "all_bit_pairs p ops_bits ops_comps'"
    using Cons.prems comps_eq by simp
  have head_mask: "valid_range_mask p gamma y"
    using Cons.prems ys_eq by simp
  have tail_masks: "valid_range_masks p gamma y_pairs'"
    using Cons.prems ys_eq by simp
  have tail_len: "length y_pairs' = length ops_bits"
    using Cons.prems ys_eq by simp
  have head_rel:
    "range_pair_residual_relation p ck
      (range_pair_commitment p ck
        (commit ck op_bit (cp_q p))
        (commit ck op_comp (cp_q p)))
      (range_pair_randomness p op_bit op_comp)"
    using range_pair_residual_relation_from_openings[OF key_ok head_pair] .
  have head_verify:
    "range_pair_sigma_verify p gamma ck
      (range_pair_commitment p ck
        (commit ck op_bit (cp_q p))
        (commit ck op_comp (cp_q p)))
      (rand_commit p ck y)
      e
      (balance_sigma_respond (range_pair_randomness p op_bit op_comp) y e)"
    using range_pair_sigma_complete[OF head_rel head_mask challenge_ok refl refl] .
  have tail_verify:
    "range_sigma_verify_pairs p gamma ck
      (range_pair_commitments p ck
        (map (\<lambda>op. commit ck op (cp_q p)) ops_bits)
        (map (\<lambda>op. commit ck op (cp_q p)) ops_comps'))
      (range_sigma_announcements p ck y_pairs')
      e
      (range_sigma_responses
        (range_pair_randomnesses p ops_bits ops_comps')
        y_pairs' e)"
    using Cons.hyps[of ops_comps' y_pairs'] tail_pairs tail_masks tail_len challenge_ok
    by simp
  show ?case
    using head_verify tail_verify comps_eq ys_eq by simp
qed

lemma range_fs_complete:
  assumes proof_def:
    "range_fs_prove p gamma k ck c_amount op_amount ops_bits ops_comps y_amounts y_pairss = Some proof"
  shows "range_fs_verify p gamma k ck c_amount proof"
proof -
  obtain c_bits c_comps r_amount r_pairs a_amounts a_pairss es z_amounts z_pairss where
      c_bits_def: "c_bits = map (\<lambda>op. commit ck op (cp_q p)) ops_bits"
      and c_comps_def: "c_comps = map (\<lambda>op. commit ck op (cp_q p)) ops_comps"
      and r_amount_def: "r_amount = range_amount_randomness p op_amount ops_bits"
      and r_pairs_def: "r_pairs = range_pair_randomnesses p ops_bits ops_comps"
      and a_amounts_def: "a_amounts = range_amount_sigma_announcements p ck y_amounts"
      and a_pairss_def: "a_pairss = range_pair_sigma_announcement_rounds p ck y_pairss"
      and es_def: "es = range_fs_challenges p ck c_amount c_bits c_comps a_amounts a_pairss"
      and z_amounts_def: "z_amounts = range_amount_sigma_responses r_amount y_amounts es"
      and z_pairss_def: "z_pairss = range_pair_sigma_response_rounds r_pairs y_pairss es"
      and rel: "range_relation p ck c_amount op_amount ops_bits ops_comps"
      and len_bits: "length ops_bits = k"
      and len_comps: "length ops_comps = k"
      and y_amounts_len: "length y_amounts = range_fs_rounds"
      and y_pairss_len: "length y_pairss = range_fs_rounds"
      and masks_ok: "\<forall>i < range_fs_rounds. valid_range_mask p gamma (y_amounts ! i)"
      and pair_masks_ok:
        "\<forall>i < range_fs_rounds.
          length (y_pairss ! i) = k \<and> valid_range_masks p gamma (y_pairss ! i)"
      and proof_eq:
        "proof =
          \<lparr> range_bits = c_bits,
            range_comps = c_comps,
            range_amount_as = a_amounts,
            range_amount_zs = z_amounts,
            range_pair_ass = a_pairss,
            range_pair_zss = z_pairss \<rparr>"
    using proof_def
    unfolding range_fs_prove_def Let_def
    by (auto split: if_splits)
  have params_ok: "valid_scalar_commit_params p"
    using rel unfolding range_relation_def by simp
  have key_ok: "valid_commit_key p ck"
    using rel unfolding range_relation_def by simp
  have es_len: "length es = range_fs_rounds"
    using es_def by (simp add: range_fs_challenges_length)
  have a_amounts_len: "length a_amounts = range_fs_rounds"
    using y_amounts_len a_amounts_def
    by (simp add: range_amount_sigma_announcements_length)
  have a_pairss_len: "length a_pairss = range_fs_rounds"
    using y_pairss_len a_pairss_def
    by (simp add: range_pair_sigma_announcement_rounds_length)
  have z_amounts_len: "length z_amounts = range_fs_rounds"
    using y_amounts_len es_len z_amounts_def
    by (simp add: range_amount_sigma_responses_length)
  have z_pairss_len: "length z_pairss = range_fs_rounds"
    using y_pairss_len es_len z_pairss_def
    by (simp add: range_pair_sigma_response_rounds_length)
  have amount_verify: "verify_opening p ck c_amount op_amount"
    using rel unfolding range_relation_def by simp
  have amount_open_ok: "valid_opening p op_amount"
    using amount_verify unfolding verify_opening_def by simp
  have c_amount_valid: "valid_commitment p c_amount"
  proof -
    have "valid_commitment p (commit ck op_amount (cp_q p))"
      using commit_valid[OF valid_scalar_commit_params_props(1)[OF params_ok] key_ok amount_open_ok] .
    then show ?thesis
      using verify_opening_eq[OF amount_verify] by simp
  qed
  have pairs_ok: "all_bit_pairs p ops_bits ops_comps"
    using rel unfolding range_relation_def by simp
  have bits_comps_len: "length c_bits = length c_comps"
    using all_bit_pairs_length[OF pairs_ok] c_bits_def c_comps_def by simp
  have c_bits_len: "length c_bits = k"
    using c_bits_def len_bits by simp
  have c_comps_len: "length c_comps = k"
    using c_comps_def len_comps by simp
  have r_pairs_len: "length r_pairs = k"
    using range_pair_randomnesses_length[OF pairs_ok] r_pairs_def len_bits by simp
  have amount_rel:
    "range_amount_residual_relation p k ck
      (range_amount_commitment p ck c_amount c_bits) r_amount"
    using range_amount_residual_relation_from_openings[OF rel]
          c_bits_def r_amount_def len_bits by simp
  have amount_sigma_ok:
    "\<forall>i < range_fs_rounds.
      range_amount_sigma_verify p gamma k ck
        (range_amount_commitment p ck c_amount c_bits)
        (a_amounts ! i)
        (es ! i)
        (z_amounts ! i)"
  proof (intro allI impI)
    fix i
    assume i_lt: "i < range_fs_rounds"
    have i_lt_amounts: "i < length y_amounts"
      using i_lt y_amounts_len by simp
    have mask_ok_i: "valid_range_mask p gamma (y_amounts ! i)"
      using masks_ok i_lt by simp
    have challenge_ok_i: "valid_range_challenge p (es ! i)"
      using range_fs_challenge_valid[OF params_ok i_lt]
      unfolding es_def .
    have a_amount_i: "a_amounts ! i = rand_commit p ck (y_amounts ! i)"
      using i_lt y_amounts_len a_amounts_def
      unfolding range_amount_sigma_announcements_def
      by simp
    have z_amount_i:
      "z_amounts ! i = balance_sigma_respond r_amount (y_amounts ! i) (es ! i)"
      using range_amount_sigma_responses_nth[OF _ i_lt_amounts] z_amounts_def
            y_amounts_len es_len
      by simp
    show "range_amount_sigma_verify p gamma k ck
            (range_amount_commitment p ck c_amount c_bits)
            (a_amounts ! i)
            (es ! i)
            (z_amounts ! i)"
      using range_amount_sigma_complete[OF amount_rel mask_ok_i challenge_ok_i a_amount_i z_amount_i] .
  qed
  have pair_sigma_ok:
    "\<forall>i < range_fs_rounds.
      length (a_pairss ! i) = k \<and>
      length (z_pairss ! i) = k \<and>
      range_sigma_verify_pairs p gamma ck
        (range_pair_commitments p ck c_bits c_comps)
        (a_pairss ! i)
        (es ! i)
        (z_pairss ! i)"
  proof (intro allI impI)
    fix i
    assume i_lt: "i < range_fs_rounds"
    have i_lt_pairss: "i < length y_pairss"
      using i_lt y_pairss_len by simp
    have pair_mask_i: "length (y_pairss ! i) = k \<and> valid_range_masks p gamma (y_pairss ! i)"
      using pair_masks_ok i_lt by simp
    then have y_pairs_len_i: "length (y_pairss ! i) = k"
      by simp
    from pair_mask_i have masks_ok_i: "valid_range_masks p gamma (y_pairss ! i)"
      by simp
    have pairs_len_eq_i: "length (y_pairss ! i) = length ops_bits"
      using y_pairs_len_i len_bits by simp
    have challenge_ok_i: "valid_range_challenge p (es ! i)"
      using range_fs_challenge_valid[OF params_ok i_lt]
      unfolding es_def .
    have a_pairs_i:
      "a_pairss ! i = range_sigma_announcements p ck (y_pairss ! i)"
      using i_lt y_pairss_len a_pairss_def
      unfolding range_pair_sigma_announcement_rounds_def
      by simp
    have z_pairs_i:
      "z_pairss ! i = range_sigma_responses r_pairs (y_pairss ! i) (es ! i)"
      using range_pair_sigma_response_rounds_nth[OF _ i_lt_pairss] z_pairss_def
            y_pairss_len es_len
      by simp
    have a_pairs_len_i: "length (a_pairss ! i) = k"
      using a_pairs_i y_pairs_len_i
      by (simp add: range_sigma_announcements_length)
    have z_pairs_len_i: "length (z_pairss ! i) = k"
      using z_pairs_i y_pairs_len_i r_pairs_len
      by (simp add: range_sigma_responses_length)
    have pair_verify_base:
      "range_sigma_verify_pairs p gamma ck
        (range_pair_commitments p ck
          (map (\<lambda>op. commit ck op (cp_q p)) ops_bits)
          (map (\<lambda>op. commit ck op (cp_q p)) ops_comps))
        (range_sigma_announcements p ck (y_pairss ! i))
        (es ! i)
        (range_sigma_responses
          (range_pair_randomnesses p ops_bits ops_comps)
          (y_pairss ! i)
          (es ! i))"
      using range_sigma_verify_pairs_complete[OF key_ok pairs_ok masks_ok_i challenge_ok_i pairs_len_eq_i] .
    have pair_verify_i:
      "range_sigma_verify_pairs p gamma ck
        (range_pair_commitments p ck c_bits c_comps)
        (a_pairss ! i)
        (es ! i)
        (z_pairss ! i)"
      using pair_verify_base c_bits_def c_comps_def a_pairs_i z_pairs_i r_pairs_def
      by simp
    show "length (a_pairss ! i) = k \<and>
          length (z_pairss ! i) = k \<and>
          range_sigma_verify_pairs p gamma ck
            (range_pair_commitments p ck c_bits c_comps)
            (a_pairss ! i)
            (es ! i)
            (z_pairss ! i)"
      using a_pairs_len_i z_pairs_len_i pair_verify_i by simp
  qed
  show ?thesis
    unfolding range_fs_verify_def Let_def
    using c_amount_valid c_bits_len c_comps_len
          a_amounts_len a_pairss_len z_amounts_len z_pairss_len
          amount_sigma_ok pair_sigma_ok proof_eq es_def
    by simp
qed

export_code
  one_opening opening_scale
  valid_bit_opening bit_pair_relation
  weighted_opening weighted_commitment
  range_amount_opening range_amount_randomness
  range_pair_opening range_pair_randomness range_pair_randomnesses
  one_commitment range_amount_commitment range_pair_commitment range_pair_commitments
  range_relation
  range_amount_witness_bound range_pair_witness_bound
  valid_range_amount_witness valid_range_pair_witness
  valid_range_mask
  range_amount_response_bound range_pair_response_bound
  valid_range_challenge valid_range_amount_response valid_range_pair_response
  range_sigma_announcements range_sigma_responses
  range_fs_rounds
  range_fs_challenges
  range_amount_sigma_announcements range_amount_sigma_responses
  range_pair_sigma_announcement_rounds range_pair_sigma_response_rounds
  range_proof.make range_bits range_comps range_amount_as range_amount_zs range_pair_ass range_pair_zss
  canonical_range_challenge
  range_amount_sigma_verify range_pair_sigma_verify range_sigma_verify_pairs
  range_fs_prove range_fs_verify
  in Haskell module_name "Canon.ZK.Confidential_Range"

export_code
  one_opening opening_scale
  valid_bit_opening bit_pair_relation
  weighted_opening weighted_commitment
  range_amount_opening range_amount_randomness
  range_pair_opening range_pair_randomness range_pair_randomnesses
  one_commitment range_amount_commitment range_pair_commitment range_pair_commitments
  range_relation
  range_amount_witness_bound range_pair_witness_bound
  valid_range_amount_witness valid_range_pair_witness
  valid_range_mask
  range_amount_response_bound range_pair_response_bound
  valid_range_challenge valid_range_amount_response valid_range_pair_response
  range_sigma_announcements range_sigma_responses
  range_fs_rounds
  range_fs_challenges
  range_amount_sigma_announcements range_amount_sigma_responses
  range_pair_sigma_announcement_rounds range_pair_sigma_response_rounds
  range_proof.make range_bits range_comps range_amount_as range_amount_zs range_pair_ass range_pair_zss
  canonical_range_challenge
  range_amount_sigma_verify range_pair_sigma_verify range_sigma_verify_pairs
  range_fs_prove range_fs_verify
  in OCaml module_name Confidential_range

end
