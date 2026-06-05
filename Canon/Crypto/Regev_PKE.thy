theory Regev_PKE
  imports Canon_Base.Prelude Canon_Base.ListVec Canon_Base.Zq Canon_Base.Norms Canon_Hardness.LWE_Def
begin

(* === Step 1: Regev PKE Parameters === *)
text \<open>
  Regev PKE Parameters:
  - Inherits n, m, q, B_s, B_e from LWE
  - B_r: bound on encryption randomness coefficients

  The correctness condition is: m * B_e * B_r < q / 4
\<close>

record regev_params = lwe_params +
  regev_Br :: int

definition valid_regev_params :: "regev_params \<Rightarrow> bool" where
  "valid_regev_params p = (
    lwe_n p > 0 \<and>
    lwe_m p > 0 \<and>
    lwe_q p > 1 \<and>
    lwe_Bs p >= 0 \<and>
    lwe_Be p >= 0 \<and>
    regev_Br p >= 0)"

lemma valid_regev_params_lwe:
  assumes "valid_regev_params p"
  shows "valid_lwe_params (lwe_params.truncate p)"
  using assms unfolding valid_regev_params_def valid_lwe_params_def
  by (simp add: lwe_params.defs)

lemma valid_regev_params_Br:
  "valid_regev_params p \<Longrightarrow> regev_Br p >= 0"
  unfolding valid_regev_params_def by simp

(* === Step 2: Key Types === *)
text \<open>
  Key and Ciphertext Types:
  - Public key: (A, b) where b = As + e mod q
  - Secret key: s
  - Ciphertext: (c1, c2) where c1 = A^T r mod q, c2 = <b,r> + encode(m) mod q
\<close>

type_synonym regev_pk = "int_matrix \<times> int_vec"
type_synonym regev_sk = "int_vec"
type_synonym regev_ct = "int_vec \<times> int"

definition valid_pk :: "regev_params \<Rightarrow> regev_pk \<Rightarrow> bool" where
  "valid_pk p pk = (
    valid_matrix (fst pk) (lwe_m p) (lwe_n p) \<and>
    valid_vec (snd pk) (lwe_m p))"

definition valid_sk :: "regev_params \<Rightarrow> regev_sk \<Rightarrow> bool" where
  "valid_sk p sk = valid_vec sk (lwe_n p)"

definition valid_ct :: "regev_params \<Rightarrow> regev_ct \<Rightarrow> bool" where
  "valid_ct p ct = valid_vec (fst ct) (lwe_n p)"

(* === Step 3: Key Generation === *)
text \<open>
  Key Generation:
  - Input: matrix A, secret s, error e
  - Output: pk = (A, b), sk = s where b = As + e mod q
\<close>

definition regev_keygen :: "int_matrix \<Rightarrow> int_vec \<Rightarrow> int_vec \<Rightarrow> int \<Rightarrow> regev_pk \<times> regev_sk" where
  "regev_keygen A s e q = ((A, lwe_sample A s e q), s)"

lemma regev_keygen_pk:
  "fst (regev_keygen A s e q) = (A, lwe_sample A s e q)"
  unfolding regev_keygen_def by simp

lemma regev_keygen_sk:
  "snd (regev_keygen A s e q) = s"
  unfolding regev_keygen_def by simp

(* Validity lemma using truncate for type coercion *)
lemma regev_keygen_valid:
  assumes "valid_regev_params p"
  assumes "valid_matrix A (lwe_m p) (lwe_n p)"
  assumes "valid_secret (lwe_params.truncate p) s"
  assumes "valid_error (lwe_params.truncate p) e"
  shows "valid_pk p (fst (regev_keygen A s e (lwe_q p)))"
    and "valid_sk p (snd (regev_keygen A s e (lwe_q p)))"
proof -
  have A_len: "length A = lwe_m p"
    using assms(2) by (simp add: valid_matrix_def)
  have e_len: "length e = lwe_m p"
    using assms(4) by (simp add: valid_error_def valid_vec_def lwe_params.defs)
  have b_len: "length (lwe_sample A s e (lwe_q p)) = lwe_m p"
    using A_len e_len by (simp add: lwe_sample_length)
  show "valid_pk p (fst (regev_keygen A s e (lwe_q p)))"
    unfolding valid_pk_def regev_keygen_def
    using assms(2) b_len by (simp add: valid_vec_def)
  show "valid_sk p (snd (regev_keygen A s e (lwe_q p)))"
    unfolding valid_sk_def regev_keygen_def
    using assms(3) by (simp add: valid_secret_def lwe_params.defs)
qed

(* === Step 4: Encryption === *)
text \<open>
  Encryption:
  - Input: public key (A, b), randomness r, message bit m
  - Output: (c1, c2) where:
    - c1 = A^T r mod q
    - c2 = <b, r> + encode(m) mod q
\<close>

definition regev_encrypt :: "regev_pk \<Rightarrow> int_vec \<Rightarrow> bool \<Rightarrow> int \<Rightarrow> regev_ct" where
  "regev_encrypt pk r m q = (
    let A = fst pk in
    let b = snd pk in
    let c1 = vec_mod (mat_vec_mult (transpose A) r) q in
    let c2 = (inner_prod b r + encode_bit q m) mod q in
    (c1, c2))"

lemma regev_encrypt_c1:
  "fst (regev_encrypt pk r m q) = vec_mod (mat_vec_mult (transpose (fst pk)) r) q"
  unfolding regev_encrypt_def by (simp add: Let_def)

lemma regev_encrypt_c2:
  "snd (regev_encrypt pk r m q) = (inner_prod (snd pk) r + encode_bit q m) mod q"
  unfolding regev_encrypt_def by (simp add: Let_def)

lemma regev_encrypt_c1_length:
  assumes "valid_matrix A m n" and "m > 0"
  shows "length (fst (regev_encrypt (A, b) r msg q)) = n"
proof -
  have len_trans: "length (transpose A) = (if A = [] then 0 else length (hd A))"
    by (simp add: length_transpose)
  have A_len: "length A = m" using assms(1) by (simp add: valid_matrix_def)
  have "A \<noteq> []" using A_len assms(2) by auto
  then obtain a as where A_cons: "A = a # as" by (cases A) auto
  hence "hd A = a" by simp
  have "a \<in> set A" using A_cons by simp
  hence "length a = n" using assms(1) by (simp add: valid_matrix_def)
  hence "length (transpose A) = n" using len_trans `A \<noteq> []` `hd A = a` by simp
  hence "length (mat_vec_mult (transpose A) r) = n"
    by (simp add: mat_vec_mult_length)
  thus ?thesis
    unfolding regev_encrypt_def by (simp add: Let_def vec_mod_length)
qed

(* === Step 5: Decryption === *)
text \<open>
  Decryption:
  - Input: secret key s, ciphertext (c1, c2)
  - Output: decode(c2 - <s, c1> mod q)
\<close>

definition regev_decrypt :: "regev_sk \<Rightarrow> regev_ct \<Rightarrow> int \<Rightarrow> bool" where
  "regev_decrypt sk ct q = (
    let c1 = fst ct in
    let c2 = snd ct in
    let payload = (c2 - inner_prod sk c1) mod q in
    decode_bit q payload)"

definition decrypt_payload :: "regev_sk \<Rightarrow> regev_ct \<Rightarrow> int \<Rightarrow> int" where
  "decrypt_payload sk ct q = (snd ct - inner_prod sk (fst ct)) mod q"

lemma regev_decrypt_alt:
  "regev_decrypt sk ct q = decode_bit q (decrypt_payload sk ct q)"
  unfolding regev_decrypt_def decrypt_payload_def by (simp add: Let_def)

(* === Step 6: Encryption Randomness Validity === *)
definition valid_randomness :: "regev_params \<Rightarrow> int_vec \<Rightarrow> bool" where
  "valid_randomness p r = (
    valid_vec r (lwe_m p) \<and>
    all_bounded r (regev_Br p))"

lemma valid_randomness_length:
  "valid_randomness p r \<Longrightarrow> length r = lwe_m p"
  unfolding valid_randomness_def valid_vec_def by simp

lemma valid_randomness_bounded:
  "valid_randomness p r \<Longrightarrow> all_bounded r (regev_Br p)"
  unfolding valid_randomness_def by simp

(* === Step 7-9: Correctness infrastructure === *)
text \<open>
  Correctness reduces decryption to the LWE noise term \<langle>e, r\<rangle>.
  The key algebraic steps are:
  - removing the modular reduction inside inner products modulo q
  - distributing inner product over vector addition
  - using iprod_transpose to cancel the A-terms
\<close>

lemma decode_bit_mod [mod_simp]:
  assumes q_pos: "(q::int) > 0"
  shows "decode_bit q (x mod q) = decode_bit q x"
  unfolding decode_bit_def using dist0_mod[OF q_pos, of x] by simp

lemma inner_prod_vec_add_right_eq_len:
  assumes len_eq: "length v1 = length v2"
  shows "inner_prod u (vec_add v1 v2) = inner_prod u v1 + inner_prod u v2"
proof -
  let ?n = "min (length u) (length v1)"
  have len_add: "length (vec_add v1 v2) = length v1"
    using len_eq by (simp add: vec_add_length)
  have "inner_prod u (vec_add v1 v2) =
        (\<Sum>i = 0 ..< min (length u) (length (vec_add v1 v2)).
           u ! i * (vec_add v1 v2) ! i)"
    by (simp add: inner_prod_nth_min)
  also have "... = (\<Sum>i = 0 ..< ?n. u ! i * (vec_add v1 v2) ! i)"
    using len_add by simp
  also have "... = (\<Sum>i = 0 ..< ?n. u ! i * (v1 ! i + v2 ! i))"
  proof (rule sum.cong, simp)
    fix i assume i_mem: "i \<in> {0 ..< ?n}"
    hence i_lt_v1: "i < length v1" by simp
    moreover have i_lt_v2: "i < length v2"
      using i_mem len_eq by simp
    ultimately show "u ! i * (vec_add v1 v2) ! i = u ! i * (v1 ! i + v2 ! i)"
      by (simp add: vec_add_def)
  qed
  also have "... = (\<Sum>i = 0 ..< ?n. u ! i * v1 ! i + u ! i * v2 ! i)"
    by (simp add: algebra_simps)
  also have "... = (\<Sum>i = 0 ..< ?n. u ! i * v1 ! i) + (\<Sum>i = 0 ..< ?n. u ! i * v2 ! i)"
    by (simp add: sum.distrib)
  also have "... = inner_prod u v1 + inner_prod u v2"
    using len_eq by (simp add: inner_prod_nth_min)
  finally show ?thesis .
qed

lemma inner_prod_vec_mod_right:
  assumes q_pos: "(q::int) > 0"
  shows "inner_prod u (vec_mod v q) mod q = inner_prod u v mod q"
proof -
  let ?n = "min (length u) (length v)"
  have len_mod: "length (vec_mod v q) = length v"
    by (simp add: vec_mod_length)
  have "inner_prod u (vec_mod v q) mod q =
        (\<Sum>i = 0 ..< min (length u) (length (vec_mod v q)).
           u ! i * (vec_mod v q) ! i) mod q"
    by (simp add: inner_prod_nth_min)
  also have "... = (\<Sum>i = 0 ..< ?n. u ! i * (vec_mod v q) ! i) mod q"
    using len_mod by simp
  also have "... = (\<Sum>i = 0 ..< ?n. (u ! i * (vec_mod v q) ! i) mod q) mod q"
    by (simp add: mod_sum_eq)
  also have "... = (\<Sum>i = 0 ..< ?n. (u ! i * v ! i) mod q) mod q"
  proof (rule arg_cong[where f="\<lambda>x. x mod q"])
    show "(\<Sum>i = 0 ..< ?n. (u ! i * (vec_mod v q) ! i) mod q) =
          (\<Sum>i = 0 ..< ?n. (u ! i * v ! i) mod q)"
    proof (rule sum.cong, simp)
      fix i assume i_mem: "i \<in> {0 ..< ?n}"
      hence i_lt_v: "i < length v" by simp
      show "(u ! i * (vec_mod v q) ! i) mod q = (u ! i * v ! i) mod q"
        using i_lt_v by (simp add: vec_mod_nth mod_mult_right_eq)
    qed
  qed
  also have "... = (\<Sum>i = 0 ..< ?n. u ! i * v ! i) mod q"
    by (simp add: mod_sum_eq)
  also have "... = inner_prod u v mod q"
    by (simp add: inner_prod_nth_min)
  finally show ?thesis .
qed

lemma inner_prod_vec_mod_left:
  assumes q_pos: "(q::int) > 0"
  assumes len_eq: "length u = length v"
  shows "inner_prod (vec_mod u q) v mod q = inner_prod u v mod q"
proof -
  have "inner_prod (vec_mod u q) v mod q = inner_prod v (vec_mod u q) mod q"
    using len_eq by (simp add: inner_prod_comm vec_mod_length)
  also have "... = inner_prod v u mod q"
    using inner_prod_vec_mod_right[OF q_pos, of v u] by simp
  also have "... = inner_prod u v mod q"
    using len_eq by (simp add: inner_prod_comm)
  finally show ?thesis .
qed

lemma mod_add_left_mid_eq:
  "((a::int) + c - b) mod q = ((a mod q) + c - b) mod q"
proof -
  have step1: "((a + c - b)::int) mod q = (((a + c) mod q) - b) mod q"
    by (simp add: mod_diff_left_eq)
  have step2: "(a + c) mod q = ((a mod q) + c) mod q"
    by (simp add: mod_add_left_eq)
  have step3_fwd: "(((a mod q) + c) - b) mod q = ((((a mod q) + c) mod q) - b) mod q"
    by (simp add: mod_diff_left_eq)
  have step3: "((((a mod q) + c) mod q) - b) mod q = (((a mod q) + c) - b) mod q"
    using step3_fwd by simp
  show ?thesis
    using step1 step2 step3 by simp
qed

lemma mod_diff_add_left_eq:
  "((((x::int) mod q - y mod q) mod q) + z) mod q = (((x - y) mod q) + z) mod q"
proof -
  have eq: "((x mod q - y mod q) mod q) = (x - y) mod q"
    by (simp add: mod_diff_eq)
  show ?thesis using eq by simp
qed

(* Noise bound from parameters *)
lemma noise_bound_from_params:
  assumes e_ok: "valid_error (lwe_params.truncate p) e"
  assumes r_ok: "valid_randomness p r"
  assumes Be_pos: "lwe_Be p >= 0"
  assumes Br_pos: "regev_Br p >= 0"
  assumes param_cond: "int (lwe_m p) * lwe_Be p * regev_Br p < lwe_q p div 4"
  shows "abs (inner_prod e r) < lwe_q p div 4"
proof -
  have len_e: "length e = lwe_m p"
    using e_ok by (simp add: valid_error_def valid_vec_def lwe_params.defs)
  have len_r: "length r = lwe_m p"
    using r_ok by (simp add: valid_randomness_def valid_vec_def)
  have e_bounded: "all_bounded e (lwe_Be p)"
    using e_ok by (simp add: valid_error_def lwe_params.defs)
  have r_bounded: "all_bounded r (regev_Br p)"
    using r_ok by (simp add: valid_randomness_def)

  have "abs (inner_prod e r) <= int (length e) * lwe_Be p * regev_Br p"
    using inner_prod_bound[OF _ e_bounded r_bounded Be_pos Br_pos] len_e len_r
    by simp
  also have "... = int (lwe_m p) * lwe_Be p * regev_Br p"
    using len_e by simp
  also have "... < lwe_q p div 4"
    using param_cond .
  finally show ?thesis .
qed

lemma regev_encrypt_valid:
  assumes params_ok: "valid_regev_params p"
  assumes pk_ok: "valid_pk p pk"
  assumes r_ok: "valid_randomness p r"
  shows "valid_ct p (regev_encrypt pk r msg (lwe_q p))"
proof -
  have A_ok: "valid_matrix (fst pk) (lwe_m p) (lwe_n p)"
    using pk_ok unfolding valid_pk_def by simp
  have m_pos: "lwe_m p > 0"
    using params_ok unfolding valid_regev_params_def by simp
  have c1_len_pair:
    "length (fst (regev_encrypt (fst pk, snd pk) r msg (lwe_q p))) = lwe_n p"
    using regev_encrypt_c1_length[OF A_ok m_pos, of "snd pk" r msg "lwe_q p"] .
  have c1_len: "length (fst (regev_encrypt pk r msg (lwe_q p))) = lwe_n p"
    using c1_len_pair by (cases pk) simp
  show ?thesis
    unfolding valid_ct_def valid_vec_def
    using c1_len by simp
qed

lemma decrypt_payload_keygen_encrypt:
  assumes params_ok: "valid_regev_params p"
  assumes A_ok: "valid_matrix A (lwe_m p) (lwe_n p)"
  assumes s_ok: "valid_secret (lwe_params.truncate p) s"
  assumes e_ok: "valid_error (lwe_params.truncate p) e"
  assumes r_ok: "valid_randomness p r"
  shows "decrypt_payload s
           (regev_encrypt (fst (regev_keygen A s e (lwe_q p))) r msg (lwe_q p))
           (lwe_q p) =
         (inner_prod e r + encode_bit (lwe_q p) msg) mod lwe_q p"
proof -
  let ?q = "lwe_q p"
  let ?b = "lwe_sample A s e ?q"
  let ?As = "mat_vec_mult A s"
  let ?Atr = "mat_vec_mult (transpose A) r"

  have q_pos: "?q > 0"
    using params_ok unfolding valid_regev_params_def by simp
  have m_pos: "lwe_m p > 0"
    using params_ok unfolding valid_regev_params_def by simp
  have n_pos: "lwe_n p > 0"
    using params_ok unfolding valid_regev_params_def by simp
  have len_s: "length s = lwe_n p"
    using s_ok by (simp add: valid_secret_def valid_vec_def lwe_params.defs)
  have len_e: "length e = lwe_m p"
    using e_ok by (simp add: valid_error_def valid_vec_def lwe_params.defs)
  have len_r: "length r = lwe_m p"
    using r_ok by (simp add: valid_randomness_def valid_vec_def)
  have len_As: "length ?As = lwe_m p"
    using A_ok by (simp add: mat_vec_mult_length valid_matrix_def)
  have len_Atr: "length ?Atr = lwe_n p"
    using A_ok m_pos
    by (simp add: mat_vec_mult_length length_transpose_valid_matrix)
  have len_add_As_e: "length (vec_add ?As e) = lwe_m p"
    using len_As len_e by (simp add: vec_add_length)
  have len_add_As_e_r: "length (vec_add ?As e) = length r"
    using len_add_As_e len_r by simp
  interpret dims: lwe_dims A s r e "lwe_m p" "lwe_n p"
  proof
    show "valid_matrix A (lwe_m p) (lwe_n p)"
      by (rule A_ok)
    show "valid_vec s (lwe_n p)"
      using len_s by (simp add: valid_vec_def)
    show "valid_vec r (lwe_m p)"
      using len_r by (simp add: valid_vec_def)
    show "valid_vec e (lwe_m p)"
      using len_e by (simp add: valid_vec_def)
    show "lwe_m p > 0"
      by (rule m_pos)
    show "lwe_n p > 0"
      by (rule n_pos)
  qed
  have b_mod: "inner_prod ?b r mod ?q = inner_prod (vec_add ?As e) r mod ?q"
  proof -
    have "inner_prod ?b r mod ?q = inner_prod (vec_mod (vec_add ?As e) ?q) r mod ?q"
      unfolding lwe_sample_def by simp
    also have "... = inner_prod (vec_add ?As e) r mod ?q"
      by (rule inner_prod_vec_mod_left[OF q_pos len_add_As_e_r])
    finally show ?thesis .
  qed
  have b_expand: "inner_prod ?b r mod ?q = (inner_prod ?As r + inner_prod e r) mod ?q"
  proof -
    have "inner_prod ?b r mod ?q = inner_prod (vec_add ?As e) r mod ?q"
      using b_mod .
    also have "... = (inner_prod ?As r + inner_prod e r) mod ?q"
    proof -
      have "inner_prod (vec_add ?As e) r = inner_prod r (vec_add ?As e)"
        using len_add_As_e_r by (simp add: inner_prod_comm)
      also have "... = inner_prod r ?As + inner_prod r e"
        using len_e len_As by (simp add: inner_prod_vec_add_right_eq_len)
      also have "... = inner_prod ?As r + inner_prod e r"
        using len_e len_As len_r by (simp add: inner_prod_comm)
      finally show ?thesis by simp
    qed
    finally show ?thesis .
  qed
  have s_c1_mod: "inner_prod s (vec_mod ?Atr ?q) mod ?q = inner_prod ?As r mod ?q"
  proof -
    have "inner_prod s (vec_mod ?Atr ?q) mod ?q = inner_prod s ?Atr mod ?q"
      using inner_prod_vec_mod_right[OF q_pos, of s ?Atr] by simp
    also have "... = inner_prod s (mat_transpose_vec_mult A r) mod ?q"
      by (simp add: mat_transpose_vec_mult_def)
    also have "... = inner_prod ?As r mod ?q"
      using dims.iprod_transpose by simp
    finally show ?thesis .
  qed
  have payload_mod:
    "decrypt_payload s
       (regev_encrypt (fst (regev_keygen A s e ?q)) r msg ?q)
       ?q =
     ((inner_prod ?b r + encode_bit ?q msg) mod ?q -
      inner_prod s (vec_mod ?Atr ?q)) mod ?q"
    unfolding decrypt_payload_def regev_encrypt_def regev_keygen_def
    by (simp add: Let_def)
  also have "... =
        (inner_prod ?b r + encode_bit ?q msg -
         inner_prod s (vec_mod ?Atr ?q)) mod ?q"
    by (simp add: mod_diff_left_eq)
  also have "... =
        ((inner_prod ?b r mod ?q) + encode_bit ?q msg -
         inner_prod s (vec_mod ?Atr ?q)) mod ?q"
    by (rule mod_add_left_mid_eq)
  also have "... =
        ((inner_prod ?b r mod ?q) + encode_bit ?q msg -
         (inner_prod s (vec_mod ?Atr ?q) mod ?q)) mod ?q"
    by (simp add: mod_diff_right_eq)
  also have "... =
        ((inner_prod ?As r + inner_prod e r) mod ?q + encode_bit ?q msg -
         (inner_prod ?As r mod ?q)) mod ?q"
    using b_expand s_c1_mod by simp
  also have "... =
        (((inner_prod ?As r + inner_prod e r) mod ?q -
          (inner_prod ?As r mod ?q)) + encode_bit ?q msg) mod ?q"
    by (simp add: algebra_simps)
  also have "... =
        ((((inner_prod ?As r + inner_prod e r) mod ?q -
           (inner_prod ?As r mod ?q)) mod ?q) + encode_bit ?q msg) mod ?q"
    by (rule mod_add_left_eq [symmetric,
          of "((inner_prod ?As r + inner_prod e r) mod ?q -
               (inner_prod ?As r mod ?q))" "encode_bit ?q msg" ?q])
  also have "... =
        ((((inner_prod ?As r + inner_prod e r) - inner_prod ?As r) mod ?q) +
          encode_bit ?q msg) mod ?q"
    by (rule mod_diff_add_left_eq
          [of "inner_prod ?As r + inner_prod e r" ?q "inner_prod ?As r"
              "encode_bit ?q msg"])
  also have "... = ((inner_prod ?As r + inner_prod e r) - inner_prod ?As r +
                      encode_bit ?q msg) mod ?q"
    by (simp add: mod_add_left_eq)
  also have "... = (inner_prod e r + encode_bit ?q msg) mod ?q"
    by (simp add: algebra_simps)
  finally show ?thesis .
qed

theorem regev_decrypt_encrypt_correct:
  assumes params_ok: "valid_regev_params p"
  assumes q_div4: "lwe_q p mod 4 = 0"
  assumes A_ok: "valid_matrix A (lwe_m p) (lwe_n p)"
  assumes s_ok: "valid_secret (lwe_params.truncate p) s"
  assumes e_ok: "valid_error (lwe_params.truncate p) e"
  assumes r_ok: "valid_randomness p r"
  assumes noise_ok: "int (lwe_m p) * lwe_Be p * regev_Br p < lwe_q p div 4"
  shows "regev_decrypt s
           (regev_encrypt (fst (regev_keygen A s e (lwe_q p))) r msg (lwe_q p))
           (lwe_q p) = msg"
proof (cases msg)
  case False
  let ?q = "lwe_q p"
  have q_pos: "?q > 0"
    using params_ok unfolding valid_regev_params_def by simp
  have noise_small: "abs (inner_prod e r) < ?q div 4"
    using noise_bound_from_params[OF e_ok r_ok] params_ok noise_ok
    by (simp add: valid_regev_params_def)
  have payload_eq:
    "decrypt_payload s
       (regev_encrypt (fst (regev_keygen A s e ?q)) r False ?q)
       ?q = inner_prod e r mod ?q"
    using decrypt_payload_keygen_encrypt[OF params_ok A_ok s_ok e_ok r_ok, of False]
    by (simp add: encode_bit_False)
  have "regev_decrypt s
          (regev_encrypt (fst (regev_keygen A s e ?q)) r False ?q)
          ?q =
        decode_bit ?q (inner_prod e r mod ?q)"
    unfolding regev_decrypt_alt using payload_eq by simp
  also have "... = decode_bit ?q (inner_prod e r)"
    using decode_bit_mod[OF q_pos, of "inner_prod e r"] by simp
  also have "... = False"
    using decode_bit_small[OF q_pos noise_small] .
  finally show ?thesis
    using False by simp
next
  case True
  let ?q = "lwe_q p"
  have q_pos: "?q > 0"
    using params_ok unfolding valid_regev_params_def by simp
  have noise_small: "abs (inner_prod e r) < ?q div 4"
    using noise_bound_from_params[OF e_ok r_ok] params_ok noise_ok
    by (simp add: valid_regev_params_def)
  have payload_eq:
    "decrypt_payload s
       (regev_encrypt (fst (regev_keygen A s e ?q)) r True ?q)
       ?q = (inner_prod e r + ?q div 2) mod ?q"
    using decrypt_payload_keygen_encrypt[OF params_ok A_ok s_ok e_ok r_ok, of True]
    by (simp add: encode_bit_True)
  have "regev_decrypt s
          (regev_encrypt (fst (regev_keygen A s e ?q)) r True ?q)
          ?q =
        decode_bit ?q ((inner_prod e r + ?q div 2) mod ?q)"
    unfolding regev_decrypt_alt using payload_eq by simp
  also have "... = decode_bit ?q (inner_prod e r + ?q div 2)"
    using decode_bit_mod[OF q_pos, of "inner_prod e r + ?q div 2"] by simp
  also have "... = True"
    using decode_bit_half_shift[OF q_pos q_div4 noise_small] .
  finally show ?thesis
    using True by simp
qed

(* === Step 11: Code Export === *)
export_code
  regev_params.make valid_regev_params
  regev_Br
  valid_pk valid_sk valid_ct valid_randomness
  regev_keygen regev_encrypt regev_decrypt
  decrypt_payload
  in Haskell module_name "Canon.Crypto.Regev_PKE"

end
