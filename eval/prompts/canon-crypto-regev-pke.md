# Prompt ID: canon-crypto-regev-pke

## Task

Create the Canon/Crypto/Regev_PKE.thy theory file - Regev's LWE-based public-key encryption scheme.

This is the **crown jewel** of the Canon library: a complete formalization of Regev's PKE with a machine-checked correctness proof. The proof uses `iprod_transpose` from ListVec and `inner_prod_bound` from Norms to show that decryption succeeds when the noise is small enough.

**Key insight**: The correctness proof hinges on the identity:
```
c2 - ⟨s, c1⟩ = ⟨e, r⟩ + encode(m)
```
When `|⟨e, r⟩| < q/4`, decoding recovers the original bit.

## Note on Theory Structure

The step-loop provides the theory header automatically. Your steps output content for inside `begin...end`.

**IMPORTANT**: These functions are already defined - do NOT redefine them:
- `inner_prod`, `mat_vec_mult`, `transpose`, `valid_vec`, `valid_matrix` - from ListVec.thy
- `vec_mod`, `vec_mod_centered`, `encode_bit`, `decode_bit` - from Zq.thy
- `all_bounded`, `inner_prod_bound`, `lwe_noise_small` - from Norms.thy
- `lwe_params`, `lwe_sample`, `valid_secret`, `valid_error`, `lwe_context` - from LWE_Def.thy

## Step-Loop Invocation

```bash
./ralph/step-loop.sh --prompt canon-crypto-regev-pke \
    --output-dir Canon \
    --theory-name Regev_PKE \
    --theory-path Crypto \
    --session Canon_Crypto \
    --imports 'Canon_Base.Prelude Canon_Base.ListVec Canon_Base.Zq Canon_Base.Norms Canon_Hardness.LWE_Def' \
    --parent-session Canon_Hardness \
    --session-dir Canon
```

**Prerequisites**: All of Canon_Base (Prelude, ListVec, Zq, Norms) and Canon_Hardness (LWE_Def) must be completed first.

## Proof Robustness Guidelines

**CRITICAL**: Follow these rules for robust proofs that work across Isabelle versions.

1. **If exact code is provided, USE IT EXACTLY** - do not simplify or "improve"
2. **Type annotations** are required for numeric lemmas - e.g., `(n::nat)`, `(q::int)`
3. **Explicit case splits** for conditionals - use `proof (cases "condition")`
4. **Use `arith` or `linarith`** for integer inequalities
5. **Name intermediate facts** for readability and debugging
6. **The `iprod_transpose` lemma** is the key to the correctness proof
7. **Witness approach** for existential goals - use `show "∃x. P x" by (intro exI) auto`

## Steps

### Step 1: Regev PKE Parameters

Define parameters specific to Regev PKE (extends LWE parameters with encryption randomness bound).

**USE THIS EXACT CODE**:
```isabelle
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
    valid_lwe_params p \<and>
    regev_Br p >= 0)"

lemma valid_regev_params_lwe:
  "valid_regev_params p \<Longrightarrow> valid_lwe_params p"
  unfolding valid_regev_params_def by simp

lemma valid_regev_params_Br:
  "valid_regev_params p \<Longrightarrow> regev_Br p >= 0"
  unfolding valid_regev_params_def by simp
```

### Step 2: Key Types

Define public key, secret key, and ciphertext types.

**USE THIS EXACT CODE**:
```isabelle
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
```

### Step 3: Key Generation

Key generation produces (pk, sk) from matrix A, secret s, and error e.

**USE THIS EXACT CODE**:
```isabelle
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

lemma regev_keygen_valid:
  assumes "valid_regev_params p"
  assumes "valid_matrix A (lwe_m p) (lwe_n p)"
  assumes "valid_secret p s"
  assumes "valid_error p e"
  shows "valid_pk p (fst (regev_keygen A s e (lwe_q p)))"
    and "valid_sk p (snd (regev_keygen A s e (lwe_q p)))"
proof -
  have b_len: "length (lwe_sample A s e (lwe_q p)) = lwe_m p"
    using assms(2) by (simp add: lwe_sample_length valid_matrix_def)
  show "valid_pk p (fst (regev_keygen A s e (lwe_q p)))"
    unfolding valid_pk_def regev_keygen_def
    using assms(2) b_len by (simp add: valid_vec_def)
  show "valid_sk p (snd (regev_keygen A s e (lwe_q p)))"
    unfolding valid_sk_def regev_keygen_def
    using assms(3) by (simp add: valid_secret_def)
qed
```

### Step 4: Encryption

Encryption computes c1 = A^T r mod q and c2 = <b, r> + encode(m) mod q.

**USE THIS EXACT CODE**:
```isabelle
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
  assumes "valid_matrix A m n"
  shows "length (fst (regev_encrypt (A, b) r msg q)) = n"
proof -
  have "length (transpose A) = n"
    using assms by (simp add: transpose_length valid_matrix_def)
  hence "length (mat_vec_mult (transpose A) r) = n"
    by (simp add: mat_vec_mult_length)
  thus ?thesis
    unfolding regev_encrypt_def by (simp add: Let_def vec_mod_length)
qed
```

### Step 5: Decryption

Decryption computes decode(c2 - <s, c1> mod q).

**USE THIS EXACT CODE**:
```isabelle
text \<open>
  Decryption:
  - Input: secret key s, ciphertext (c1, c2)
  - Output: decode(c2 - <s, c1> mod q)

  The decryption "payload" is c2 - <s, c1>, which equals <e, r> + encode(m)
  when the ciphertext is honestly generated.
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
```

### Step 6: Encryption Randomness Validity

Define what it means for encryption randomness to be valid.

**USE THIS EXACT CODE**:
```isabelle
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
```

### Step 7: The Core Correctness Lemma - Payload Identity

This is the heart of the correctness proof: showing that the decrypt payload equals <e, r> + encode(m).

**USE THIS EXACT CODE**:
```isabelle
text \<open>
  Core Correctness Identity:

  When ct = Encrypt(pk, r, m) with pk = (A, As + e):
    payload = c2 - <s, c1>
            = (<b, r> + encode(m)) - <s, A^T r>      (by encrypt definition)
            = (<As + e, r> + encode(m)) - <s, A^T r>  (since b = As + e)
            = <As, r> + <e, r> + encode(m) - <s, A^T r>  (bilinearity)
            = <e, r> + encode(m)                     (by iprod_transpose!)

  The iprod_transpose lemma gives us: <s, A^T r> = <As, r>
\<close>

lemma payload_identity_raw:
  assumes len_A: "length A = m"
  assumes rows_A: "\<forall>row \<in> set A. length row = n"
  assumes len_s: "length s = n"
  assumes len_e: "length e = m"
  assumes len_r: "length r = m"
  assumes q_pos: "(q::int) > 0"
  shows "((inner_prod (lwe_sample A s e q) r + encode_bit q msg) -
          inner_prod s (mat_vec_mult (transpose A) r)) mod q =
         (inner_prod e r + encode_bit q msg) mod q"
proof -
  let ?b = "lwe_sample A s e q"
  let ?As = "mat_vec_mult A s"

  have len_As: "length ?As = m"
    using len_A by (simp add: mat_vec_mult_length)

  have len_b: "length ?b = m"
    using len_A by (simp add: lwe_sample_length)

  text \<open>Key step: use iprod_transpose to show <s, A^T r> = <As, r>\<close>
  have transpose_identity: "inner_prod s (mat_vec_mult (transpose A) r) = inner_prod ?As r"
    using iprod_transpose[OF len_A rows_A len_s len_r] by simp

  text \<open>Expand b = As + e mod q, then use mod arithmetic\<close>
  have "inner_prod ?b r = inner_prod (vec_mod (vec_add ?As e) q) r"
    unfolding lwe_sample_def by simp

  text \<open>The payload calculation\<close>
  have "(inner_prod ?b r + encode_bit q msg - inner_prod s (mat_vec_mult (transpose A) r)) mod q =
        (inner_prod ?b r + encode_bit q msg - inner_prod ?As r) mod q"
    using transpose_identity by simp
  also have "... = (inner_prod ?b r - inner_prod ?As r + encode_bit q msg) mod q"
    by (simp add: algebra_simps)
  finally have step1: "(inner_prod ?b r + encode_bit q msg - inner_prod s (mat_vec_mult (transpose A) r)) mod q =
                       (inner_prod ?b r - inner_prod ?As r + encode_bit q msg) mod q" .

  text \<open>Now we need: inner_prod b r - inner_prod As r ≡ inner_prod e r (mod q)\<close>
  text \<open>Since b = (As + e) mod q, we have b_i ≡ As_i + e_i (mod q) for each i\<close>
  text \<open>So <b, r> ≡ <As + e, r> = <As, r> + <e, r> (mod q)\<close>

  have b_cong: "(inner_prod ?b r) mod q = (inner_prod (vec_add ?As e) r) mod q"
  proof -
    have "?b = vec_mod (vec_add ?As e) q"
      unfolding lwe_sample_def by simp
    have len_sum: "length (vec_add ?As e) = min m m"
      using len_As len_e by (simp add: vec_add_length)
    have len_b2: "length ?b = m"
      by (simp add: lwe_sample_length len_A)

    have "\<forall>i < m. ?b ! i mod q = (vec_add ?As e) ! i mod q"
    proof (intro allI impI)
      fix i assume "i < m"
      have "i < length (vec_add ?As e)"
        using `i < m` len_sum by simp
      hence "?b ! i = (vec_add ?As e) ! i mod q"
        unfolding lwe_sample_def using vec_mod_nth by simp
      thus "?b ! i mod q = (vec_add ?As e) ! i mod q"
        by simp
    qed

    thus ?thesis
      using inner_prod_mod_cong[of ?b "vec_add ?As e" r q] len_b len_sum len_e len_As
      by (simp add: min_def)
  qed

  have sum_split: "inner_prod (vec_add ?As e) r = inner_prod ?As r + inner_prod e r"
    using inner_prod_vec_add[OF len_As len_e len_r] by simp

  have "(inner_prod ?b r - inner_prod ?As r) mod q =
        (inner_prod (vec_add ?As e) r - inner_prod ?As r) mod q"
    using b_cong by (metis mod_diff_right_eq)
  also have "... = (inner_prod ?As r + inner_prod e r - inner_prod ?As r) mod q"
    using sum_split by simp
  also have "... = (inner_prod e r) mod q"
    by simp
  finally have diff_eq: "(inner_prod ?b r - inner_prod ?As r) mod q = (inner_prod e r) mod q" .

  have "(inner_prod ?b r - inner_prod ?As r + encode_bit q msg) mod q =
        ((inner_prod ?b r - inner_prod ?As r) mod q + encode_bit q msg) mod q"
    by (simp add: mod_add_left_eq)
  also have "... = ((inner_prod e r) mod q + encode_bit q msg) mod q"
    using diff_eq by simp
  also have "... = (inner_prod e r + encode_bit q msg) mod q"
    by (simp add: mod_add_left_eq)
  finally show ?thesis using step1 by simp
qed
```

### Step 8: Helper Lemmas for Correctness

Bridge lemmas connecting the raw identity to valid instances.

**USE THIS EXACT CODE**:
```isabelle
lemma inner_prod_mod_cong:
  assumes "length u = length v"
  assumes "\<forall>i < length u. u ! i mod q = v ! i mod q"
  shows "(inner_prod u w) mod q = (inner_prod v w) mod q"
proof -
  let ?n = "min (length u) (length w)"
  have "(inner_prod u w) mod q = (\\<Sum>i = 0 ..< ?n. u ! i * w ! i) mod q"
    by (simp add: inner_prod_nth_min)
  also have "... = (\\<Sum>i = 0 ..< ?n. (u ! i mod q) * w ! i) mod q"
    by (simp add: mod_sum_cong mult_mod_left)
  also have "... = (\\<Sum>i = 0 ..< ?n. (v ! i mod q) * w ! i) mod q"
  proof -
    have "\<forall>i < ?n. (u ! i mod q) * w ! i = (v ! i mod q) * w ! i"
      using assms by auto
    thus ?thesis by (simp add: sum.cong)
  qed
  also have "... = (\\<Sum>i = 0 ..< ?n. v ! i * w ! i) mod q"
    by (simp add: mod_sum_cong mult_mod_left)
  also have "... = (inner_prod v w) mod q"
    using assms(1) by (simp add: inner_prod_nth_min)
  finally show ?thesis .
qed

lemma inner_prod_vec_add:
  assumes "length u = n" and "length v = n" and "length w = n"
  shows "inner_prod (vec_add u v) w = inner_prod u w + inner_prod v w"
proof -
  have len_uv: "length (vec_add u v) = n"
    using assms by (simp add: vec_add_length)
  have "inner_prod (vec_add u v) w = (\\<Sum>i = 0 ..< n. (vec_add u v) ! i * w ! i)"
    using len_uv assms(3) by (simp add: inner_prod_nth_min)
  also have "... = (\\<Sum>i = 0 ..< n. (u ! i + v ! i) * w ! i)"
  proof (rule sum.cong)
    fix i assume "i \\<in> {0 ..< n}"
    hence "i < n" by simp
    thus "(vec_add u v) ! i * w ! i = (u ! i + v ! i) * w ! i"
      using assms by (simp add: vec_add_def)
  qed simp
  also have "... = (\\<Sum>i = 0 ..< n. u ! i * w ! i + v ! i * w ! i)"
    by (simp add: algebra_simps)
  also have "... = (\\<Sum>i = 0 ..< n. u ! i * w ! i) + (\\<Sum>i = 0 ..< n. v ! i * w ! i)"
    by (simp add: sum.distrib)
  also have "... = inner_prod u w + inner_prod v w"
    using assms by (simp add: inner_prod_nth_min)
  finally show ?thesis .
qed
```

### Step 9: Main Correctness Theorem

The final correctness theorem: decryption recovers the message when noise is small.

**USE THIS EXACT CODE**:
```isabelle
text \<open>
  Main Correctness Theorem:

  If the noise term |<e, r>| < q/4, then decryption correctly recovers the message.

  This follows from:
  1. payload = <e, r> + encode(m) (by payload_identity)
  2. |<e, r>| < q/4 (by noise assumption)
  3. decode(encode(m) + small_noise) = m (by decode_bit_half_shift)
\<close>

theorem regev_correctness:
  assumes params_ok: "valid_regev_params p"
  assumes A_ok: "valid_matrix A (lwe_m p) (lwe_n p)"
  assumes s_ok: "valid_secret p s"
  assumes e_ok: "valid_error p e"
  assumes r_ok: "valid_randomness p r"
  assumes q_pos: "lwe_q p > 1"
  assumes noise_small: "abs (inner_prod e r) < lwe_q p div 4"
  shows "regev_decrypt s (regev_encrypt (A, lwe_sample A s e (lwe_q p)) r m (lwe_q p)) (lwe_q p) = m"
proof -
  let ?q = "lwe_q p"
  let ?b = "lwe_sample A s e ?q"
  let ?pk = "(A, ?b)"
  let ?ct = "regev_encrypt ?pk r m ?q"
  let ?c1 = "fst ?ct"
  let ?c2 = "snd ?ct"

  have n_eq: "lwe_n p = length s"
    using s_ok by (simp add: valid_secret_def valid_vec_def)
  have m_eq: "lwe_m p = length A"
    using A_ok by (simp add: valid_matrix_def)
  have len_e: "length e = lwe_m p"
    using e_ok by (simp add: valid_error_def valid_vec_def)
  have len_r: "length r = lwe_m p"
    using r_ok by (simp add: valid_randomness_def valid_vec_def)
  have rows_A: "\<forall>row \<in> set A. length row = lwe_n p"
    using A_ok by (simp add: valid_matrix_def)

  text \<open>Step 1: The payload equals <e, r> + encode(m) mod q\<close>
  have payload_eq: "decrypt_payload s ?ct ?q = (inner_prod e r + encode_bit ?q m) mod ?q"
  proof -
    have "decrypt_payload s ?ct ?q = (?c2 - inner_prod s ?c1) mod ?q"
      unfolding decrypt_payload_def by simp
    also have "?c2 = (inner_prod ?b r + encode_bit ?q m) mod ?q"
      by (simp add: regev_encrypt_c2)
    also have "?c1 = vec_mod (mat_vec_mult (transpose A) r) ?q"
      by (simp add: regev_encrypt_c1)
    finally have "decrypt_payload s ?ct ?q =
      ((inner_prod ?b r + encode_bit ?q m) mod ?q -
       inner_prod s (vec_mod (mat_vec_mult (transpose A) r) ?q)) mod ?q"
      by simp
    text \<open>Use that inner_prod s (vec_mod v q) ≡ inner_prod s v (mod q)\<close>
    also have "... = ((inner_prod ?b r + encode_bit ?q m) -
                      inner_prod s (mat_vec_mult (transpose A) r)) mod ?q"
      by (smt (verit) mod_diff_left_eq mod_diff_right_eq mod_mod_trivial)
    also have "... = (inner_prod e r + encode_bit ?q m) mod ?q"
      using payload_identity_raw[OF m_eq rows_A n_eq len_e len_r] q_pos
      by simp
    finally show ?thesis .
  qed

  text \<open>Step 2: Apply decode_bit_half_shift to recover m\<close>
  have "regev_decrypt s ?ct ?q = decode_bit ?q (decrypt_payload s ?ct ?q)"
    by (simp add: regev_decrypt_alt)
  also have "... = decode_bit ?q ((inner_prod e r + encode_bit ?q m) mod ?q)"
    using payload_eq by simp
  also have "... = m"
  proof -
    have "?q > 1" using q_pos .
    moreover have "abs (inner_prod e r) < ?q div 4" using noise_small .
    ultimately show "decode_bit ?q ((inner_prod e r + encode_bit ?q m) mod ?q) = m"
      using decode_bit_half_shift[of ?q "inner_prod e r" m] by simp
  qed
  finally show ?thesis .
qed
```

### Step 10: Noise Bound from Parameters

Show that the noise condition follows from parameter bounds.

**USE THIS EXACT CODE**:
```isabelle
text \<open>
  When parameters satisfy m * B_e * B_r < q/4, the noise bound holds.
\<close>

lemma noise_bound_from_params:
  assumes e_ok: "valid_error p e"
  assumes r_ok: "valid_randomness p r"
  assumes Be_pos: "lwe_Be p >= 0"
  assumes Br_pos: "regev_Br p >= 0"
  assumes param_cond: "int (lwe_m p) * lwe_Be p * regev_Br p < lwe_q p div 4"
  shows "abs (inner_prod e r) < lwe_q p div 4"
proof -
  have len_e: "length e = lwe_m p"
    using e_ok by (simp add: valid_error_def valid_vec_def)
  have len_r: "length r = lwe_m p"
    using r_ok by (simp add: valid_randomness_def valid_vec_def)
  have e_bounded: "all_bounded e (lwe_Be p)"
    using e_ok by (simp add: valid_error_def)
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

corollary regev_correctness_from_params:
  assumes "valid_regev_params p"
  assumes "valid_matrix A (lwe_m p) (lwe_n p)"
  assumes "valid_secret p s"
  assumes "valid_error p e"
  assumes "valid_randomness p r"
  assumes "lwe_q p > 1"
  assumes "lwe_Be p >= 0"
  assumes "regev_Br p >= 0"
  assumes "int (lwe_m p) * lwe_Be p * regev_Br p < lwe_q p div 4"
  shows "regev_decrypt s (regev_encrypt (A, lwe_sample A s e (lwe_q p)) r m (lwe_q p)) (lwe_q p) = m"
  using regev_correctness[OF assms(1-6)] noise_bound_from_params[OF assms(4,5,7,8,9)]
  by simp
```

### Step 11: Code Export

**USE THIS EXACT CODE**:
```isabelle
export_code
  regev_params.make valid_regev_params
  regev_Br
  valid_pk valid_sk valid_ct valid_randomness
  regev_keygen regev_encrypt regev_decrypt
  decrypt_payload
  in Haskell module_name "Canon.Crypto.Regev_PKE"
```

## Constraints

- Theory name: `Regev_PKE`
- Session: `Canon_Crypto` (depends on `Canon_Hardness` which depends on `Canon_Base`)
- Imports: Prelude, ListVec, Zq, Norms, LWE_Def
- No sorry/oops - all proofs must be complete
- The `iprod_transpose` and `decode_bit_half_shift` lemmas are critical
- Record extension syntax: `record foo = bar + ...`

## Proof Strategy Reference

| Goal Type | Recommended Tactic |
|-----------|-------------------|
| Record field access | `by simp` |
| Validity unfolding | `unfolding valid_foo_def by simp` |
| Modular arithmetic | `by (simp add: mod_add_left_eq)` |
| Using iprod_transpose | `using iprod_transpose[OF len_A rows_A len_s len_r]` |
| Sum manipulation | `by (simp add: algebra_simps)` |
| Chained mod equalities | `by (metis mod_diff_right_eq)` |

## Key Insights

1. **iprod_transpose is the key**: `<s, A^T r> = <As, r>` makes the cancellation work
2. **decode_bit_half_shift**: handles the actual decoding when noise < q/4
3. **Payload identity**: c2 - <s, c1> = <e, r> + encode(m) mod q
4. **Parameter condition**: m * B_e * B_r < q/4 guarantees correctness
5. **Record extension**: regev_params extends lwe_params with B_r

## Deliverable

A working Regev_PKE.thy that:
1. Compiles as part of Canon_Crypto session
2. Defines regev_keygen, regev_encrypt, regev_decrypt
3. Has the payload_identity lemma showing the cancellation
4. Has regev_correctness theorem with noise assumption
5. Has regev_correctness_from_params using parameter bounds
6. Exports to Haskell
