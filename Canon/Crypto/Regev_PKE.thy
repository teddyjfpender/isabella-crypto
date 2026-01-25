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
  The full correctness proof requires iprod_transpose and additional helper lemmas.
  For now, we provide the key definitions and state the main theorem.
\<close>

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

(* === Step 11: Code Export === *)
export_code
  regev_params.make valid_regev_params
  regev_Br
  valid_pk valid_sk valid_ct valid_randomness
  regev_keygen regev_encrypt regev_decrypt
  decrypt_payload
  in Haskell module_name "Canon.Crypto.Regev_PKE"

end
