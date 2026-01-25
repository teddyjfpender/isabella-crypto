# Prompt ID: canon-crypto-kyber

## Task

Create the Canon/Crypto/Kyber.thy theory file - CRYSTALS-Kyber (ML-KEM) key encapsulation mechanism.

Kyber is a lattice-based KEM standardized by NIST (FIPS 203). It achieves IND-CCA2 security from the Module-LWE assumption using the Fujisaki-Okamoto transform.

**Key insight**: Kyber = Module-LWE PKE + FO Transform + Compression

## Note on Theory Structure

The step-loop provides the theory header automatically. Your steps output content for inside `begin...end`.

**IMPORTANT**: These functions are already defined - do NOT redefine them:
- `poly`, `ring_mult`, `ring_add`, `ring_sub`, `poly_mod` - from PolyMod.thy
- `mod_elem`, `mod_inner_prod`, `mod_mat_vec_mult`, `mod_add` - from ModuleLWE.thy
- `mlwe_params`, `valid_mlwe_params`, `mlwe_sample` - from ModuleLWE.thy
- `ntt_naive`, `intt_naive`, `ntt_pointwise_mult` - from NTT.thy

## Step-Loop Invocation

```bash
./ralph/step-loop-v2.sh --prompt canon-crypto-kyber \
    --output-dir Canon \
    --theory-name Kyber \
    --theory-path Crypto \
    --session Canon_Crypto \
    --imports 'Canon_Base.Prelude Canon_Base.ListVec Canon_Base.Zq Canon_Base.Norms Canon_Rings.PolyMod Canon_Rings.ModuleLWE Canon_Rings.NTT' \
    --parent-session Canon_Rings \
    --session-dir Canon
```

**Prerequisites**: Prelude, ListVec, Zq, Norms, PolyMod, ModuleLWE, and NTT must be completed first.

## Proof Robustness Guidelines

**CRITICAL**: Follow these rules for robust proofs that work across Isabelle versions.

1. **If exact code is provided, USE IT EXACTLY** - do not simplify or "improve"
2. **Type annotations** are required for numeric lemmas - e.g., `(k::nat)`, `(q::int)`
3. **Explicit case splits** for conditionals - use `proof (cases "condition")`
4. **Use `arith` or `linarith`** for integer inequalities
5. **Record types**: use `\<lparr> field1 = v1, field2 = v2 \<rparr>` syntax
6. **Name intermediate facts** for readability and debugging

## Steps

### Step 1: Kyber Parameters

Define the Kyber parameter sets for different security levels.

**USE THIS EXACT CODE**:
```isabelle
text \<open>
  CRYSTALS-Kyber Parameters (FIPS 203 / ML-KEM):

  All variants use:
  - n = 256 (polynomial degree)
  - q = 3329 (modulus)

  Security levels differ by k (module rank):
  - Kyber512 (ML-KEM-512): k = 2, η₁ = 3, η₂ = 2
  - Kyber768 (ML-KEM-768): k = 3, η₁ = 2, η₂ = 2
  - Kyber1024 (ML-KEM-1024): k = 4, η₁ = 2, η₂ = 2

  Additional parameters:
  - du, dv: compression parameters for ciphertext
  - dt: compression parameter for public key
\<close>

record kyber_params =
  kyber_n :: nat      \<comment> \<open>polynomial degree (always 256)\<close>
  kyber_q :: int      \<comment> \<open>modulus (always 3329)\<close>
  kyber_k :: nat      \<comment> \<open>module rank (2, 3, or 4)\<close>
  kyber_eta1 :: nat   \<comment> \<open>secret/error distribution parameter\<close>
  kyber_eta2 :: nat   \<comment> \<open>encryption error parameter\<close>
  kyber_du :: nat     \<comment> \<open>ciphertext u compression bits\<close>
  kyber_dv :: nat     \<comment> \<open>ciphertext v compression bits\<close>

definition valid_kyber_params :: "kyber_params \<Rightarrow> bool" where
  "valid_kyber_params p = (
    kyber_n p = 256 \<and>
    kyber_q p = 3329 \<and>
    kyber_k p \<in> {2, 3, 4} \<and>
    kyber_eta1 p > 0 \<and>
    kyber_eta2 p > 0 \<and>
    kyber_du p > 0 \<and> kyber_du p \<le> 12 \<and>
    kyber_dv p > 0 \<and> kyber_dv p \<le> 12)"

definition kyber512_params :: kyber_params where
  "kyber512_params = \<lparr>
    kyber_n = 256, kyber_q = 3329, kyber_k = 2,
    kyber_eta1 = 3, kyber_eta2 = 2,
    kyber_du = 10, kyber_dv = 4
  \<rparr>"

definition kyber768_params :: kyber_params where
  "kyber768_params = \<lparr>
    kyber_n = 256, kyber_q = 3329, kyber_k = 3,
    kyber_eta1 = 2, kyber_eta2 = 2,
    kyber_du = 10, kyber_dv = 4
  \<rparr>"

definition kyber1024_params :: kyber_params where
  "kyber1024_params = \<lparr>
    kyber_n = 256, kyber_q = 3329, kyber_k = 4,
    kyber_eta1 = 2, kyber_eta2 = 2,
    kyber_du = 11, kyber_dv = 5
  \<rparr>"

lemma kyber512_valid: "valid_kyber_params kyber512_params"
  unfolding valid_kyber_params_def kyber512_params_def by simp

lemma kyber768_valid: "valid_kyber_params kyber768_params"
  unfolding valid_kyber_params_def kyber768_params_def by simp

lemma kyber1024_valid: "valid_kyber_params kyber1024_params"
  unfolding valid_kyber_params_def kyber1024_params_def by simp
```

### Step 2: Key Types

Define the public key, secret key, and ciphertext types.

**USE THIS EXACT CODE**:
```isabelle
text \<open>
  Kyber Key Types:

  Public key: (ρ, t̂) where
  - ρ: seed for generating matrix A
  - t̂ = NTT(As + e): public vector in NTT domain

  Secret key: ŝ = NTT(s)
  - s: secret vector with small coefficients

  For simplicity, we represent keys without compression initially.
\<close>

type_synonym kyber_poly = poly
type_synonym kyber_vec = "kyber_poly list"
type_synonym kyber_matrix = "kyber_vec list"

record kyber_pk =
  pk_A :: kyber_matrix    \<comment> \<open>public matrix (derived from seed in practice)\<close>
  pk_t :: kyber_vec       \<comment> \<open>t = As + e (in NTT domain)\<close>

record kyber_sk =
  sk_s :: kyber_vec       \<comment> \<open>secret vector (in NTT domain)\<close>
  sk_pk :: kyber_pk       \<comment> \<open>copy of public key for CCA security\<close>

record kyber_ciphertext =
  ct_u :: kyber_vec       \<comment> \<open>u = A^T r + e1\<close>
  ct_v :: kyber_poly      \<comment> \<open>v = t^T r + e2 + encode(m)\<close>

definition valid_kyber_vec :: "kyber_vec \<Rightarrow> kyber_params \<Rightarrow> bool" where
  "valid_kyber_vec v p = (
    length v = kyber_k p \<and>
    (\<forall>poly \<in> set v. length poly = kyber_n p))"

definition valid_kyber_matrix :: "kyber_matrix \<Rightarrow> kyber_params \<Rightarrow> bool" where
  "valid_kyber_matrix M p = (
    length M = kyber_k p \<and>
    (\<forall>row \<in> set M. valid_kyber_vec row p))"

definition valid_kyber_pk :: "kyber_pk \<Rightarrow> kyber_params \<Rightarrow> bool" where
  "valid_kyber_pk pk p = (
    valid_kyber_matrix (pk_A pk) p \<and>
    valid_kyber_vec (pk_t pk) p)"

definition valid_kyber_sk :: "kyber_sk \<Rightarrow> kyber_params \<Rightarrow> bool" where
  "valid_kyber_sk sk p = (
    valid_kyber_vec (sk_s sk) p \<and>
    valid_kyber_pk (sk_pk sk) p)"
```

### Step 3: Polynomial Operations with NTT

Define NTT-accelerated operations for Kyber.

**USE THIS EXACT CODE**:
```isabelle
text \<open>
  NTT-accelerated polynomial operations using the fast Cooley-Tukey algorithm.

  In Kyber, most operations happen in NTT domain:
  - Multiplication: NTT(a) ⊙ NTT(b)
  - Matrix-vector products: row-wise NTT multiplications

  We use ntt_fast (O(n log n)) instead of ntt_naive (O(n^2)).
\<close>

definition kyber_ntt :: "kyber_poly \<Rightarrow> kyber_poly" where
  "kyber_ntt a = ntt_fast a 17 3329 256"

definition kyber_intt :: "kyber_poly \<Rightarrow> kyber_poly" where
  "kyber_intt a_hat = intt_fast a_hat 17 3329 256"

definition kyber_poly_mult_ntt :: "kyber_poly \<Rightarrow> kyber_poly \<Rightarrow> kyber_poly" where
  "kyber_poly_mult_ntt a_hat b_hat = ntt_pointwise_mult a_hat b_hat 3329"

definition kyber_poly_add :: "kyber_poly \<Rightarrow> kyber_poly \<Rightarrow> kyber_poly" where
  "kyber_poly_add a b = poly_mod (poly_add a b) 3329"

definition kyber_poly_sub :: "kyber_poly \<Rightarrow> kyber_poly \<Rightarrow> kyber_poly" where
  "kyber_poly_sub a b = poly_mod (poly_sub a b) 3329"

text \<open>
  Vector operations (component-wise).
\<close>

definition kyber_vec_add :: "kyber_vec \<Rightarrow> kyber_vec \<Rightarrow> kyber_vec" where
  "kyber_vec_add v w = map2 kyber_poly_add v w"

definition kyber_vec_ntt :: "kyber_vec \<Rightarrow> kyber_vec" where
  "kyber_vec_ntt v = map kyber_ntt v"

definition kyber_vec_intt :: "kyber_vec \<Rightarrow> kyber_vec" where
  "kyber_vec_intt v = map kyber_intt v"

text \<open>Helper lemmas for length preservation.\<close>

lemma kyber_poly_mult_ntt_length:
  "length (kyber_poly_mult_ntt a b) = min (length a) (length b)"
  unfolding kyber_poly_mult_ntt_def ntt_pointwise_mult_def by simp

lemma kyber_poly_add_length:
  "length (kyber_poly_add a b) = max (length a) (length b)"
  unfolding kyber_poly_add_def by (simp add: poly_add_length)

lemma kyber_poly_sub_length:
  "length (kyber_poly_sub a b) = max (length a) (length b)"
  unfolding kyber_poly_sub_def by (simp add: poly_sub_length)

lemma kyber_intt_length [simp]:
  assumes "length a = 256"
  shows "length (kyber_intt a) = 256"
  using assms unfolding kyber_intt_def intt_fast_def Let_def
  by (simp add: ntt_iter_aux_length)

lemma kyber_vec_add_length:
  "length (kyber_vec_add v w) = min (length v) (length w)"
  unfolding kyber_vec_add_def by simp

lemma kyber_vec_ntt_length:
  "length (kyber_vec_ntt v) = length v"
  unfolding kyber_vec_ntt_def by simp

lemma kyber_vec_intt_length:
  "length (kyber_vec_intt v) = length v"
  unfolding kyber_vec_intt_def by simp

text \<open>
  Inner product in NTT domain: <v̂, ŵ> = Σ v̂_i ⊙ ŵ_i

  Key insight: we accumulate results that preserve length 256 when inputs
  have length 256.
\<close>

primrec kyber_inner_prod_ntt :: "kyber_vec \<Rightarrow> kyber_vec \<Rightarrow> kyber_poly" where
  "kyber_inner_prod_ntt [] w = replicate 256 0"
| "kyber_inner_prod_ntt (p # ps) w = (
    case w of
      [] \<Rightarrow> replicate 256 0
    | (r # rs) \<Rightarrow> kyber_poly_add (kyber_poly_mult_ntt p r) (kyber_inner_prod_ntt ps rs))"

lemma kyber_inner_prod_ntt_length_aux:
  "length v = length w \<longrightarrow>
   (\<forall>p \<in> set v. length p = 256) \<longrightarrow>
   (\<forall>r \<in> set w. length r = 256) \<longrightarrow>
   length (kyber_inner_prod_ntt v w) = 256"
proof (induct v arbitrary: w)
  case Nil then show ?case by simp
next
  case (Cons p ps)
  show ?case
  proof (intro impI)
    assume len_eq: "length (p # ps) = length w"
    assume v_256: "\<forall>x \<in> set (p # ps). length x = 256"
    assume w_256: "\<forall>r \<in> set w. length r = 256"
    from len_eq obtain r rs where w_eq: "w = r # rs" by (cases w) auto
    from v_256 have "length p = 256" by simp
    from w_256 w_eq have "length r = 256" by simp
    have mult_len: "length (kyber_poly_mult_ntt p r) = 256"
      using \<open>length p = 256\<close> \<open>length r = 256\<close> kyber_poly_mult_ntt_length by simp
    from len_eq w_eq have "length ps = length rs" by simp
    from v_256 have ps_256: "\<forall>x \<in> set ps. length x = 256" by simp
    from w_256 w_eq have rs_256: "\<forall>x \<in> set rs. length x = 256" by simp
    from Cons.hyps \<open>length ps = length rs\<close> ps_256 rs_256
    have rec_len: "length (kyber_inner_prod_ntt ps rs) = 256" by simp
    have add_len: "length (kyber_poly_add (kyber_poly_mult_ntt p r)
                                           (kyber_inner_prod_ntt ps rs)) = 256"
      using mult_len rec_len kyber_poly_add_length by simp
    show "length (kyber_inner_prod_ntt (p # ps) w) = 256"
      using w_eq add_len by simp
  qed
qed

lemma kyber_inner_prod_ntt_length:
  assumes "length v = length w"
  assumes "\<forall>p \<in> set v. length p = 256"
  assumes "\<forall>r \<in> set w. length r = 256"
  shows "length (kyber_inner_prod_ntt v w) = 256"
  using assms kyber_inner_prod_ntt_length_aux by blast
```

### Step 4: Matrix-Vector Multiplication

**USE THIS EXACT CODE**:
```isabelle
text \<open>
  Matrix-vector multiplication in NTT domain.

  For matrix Â (in NTT domain) and vector v̂ (in NTT domain):
    (Â · v̂)_i = <Â_i, v̂> = Σ_j Â_{i,j} ⊙ v̂_j
\<close>

definition kyber_mat_vec_mult_ntt :: "kyber_matrix \<Rightarrow> kyber_vec \<Rightarrow> kyber_vec" where
  "kyber_mat_vec_mult_ntt A v = map (\<lambda>row. kyber_inner_prod_ntt row v) A"

lemma kyber_mat_vec_mult_ntt_length:
  "length (kyber_mat_vec_mult_ntt A v) = length A"
  unfolding kyber_mat_vec_mult_ntt_def by simp

text \<open>
  Transpose multiplication: A^T · v
  For Kyber encryption, we need A^T · r.
\<close>

definition kyber_transpose :: "kyber_matrix \<Rightarrow> kyber_matrix" where
  "kyber_transpose A = (
    let k = length A in
    if k = 0 then []
    else map (\<lambda>j. map (\<lambda>i. (A ! i) ! j) [0..<k]) [0..<k])"

definition kyber_mat_transpose_vec_mult_ntt :: "kyber_matrix \<Rightarrow> kyber_vec \<Rightarrow> kyber_vec" where
  "kyber_mat_transpose_vec_mult_ntt A v = kyber_mat_vec_mult_ntt (kyber_transpose A) v"
```

### Step 5: Message Encoding

Encode a single bit into a polynomial.

**USE THIS EXACT CODE**:
```isabelle
text \<open>
  Message encoding for Kyber:

  Each bit m ∈ {0, 1} is encoded as m · ⌈q/2⌋ = m · 1665.
  This places 0 at 0 and 1 at q/2, maximizing the decision boundary.

  For a 256-bit message, we encode each bit into one coefficient.
\<close>

definition kyber_encode_coeff :: "nat \<Rightarrow> int" where
  "kyber_encode_coeff m = (if m = 1 then 1665 else 0)"

definition kyber_decode_coeff :: "int \<Rightarrow> nat" where
  "kyber_decode_coeff c = (
    let c' = c mod 3329 in
    let c'' = (if c' < 0 then c' + 3329 else c') in
    if abs (c'' - 1665) < abs c'' then 1 else 0)"

definition kyber_encode_msg :: "nat list \<Rightarrow> kyber_poly" where
  "kyber_encode_msg msg = map kyber_encode_coeff (take 256 (msg @ replicate 256 0))"

definition kyber_decode_msg :: "kyber_poly \<Rightarrow> nat list" where
  "kyber_decode_msg v = map kyber_decode_coeff v"

lemma kyber_encode_msg_length:
  "length (kyber_encode_msg msg) = 256"
  unfolding kyber_encode_msg_def by simp

lemma kyber_decode_msg_length:
  "length (kyber_decode_msg v) = length v"
  unfolding kyber_decode_msg_def by simp

lemma kyber_encode_decode_correct_coeff:
  assumes "m \<in> {0, 1}"
  shows "kyber_decode_coeff (kyber_encode_coeff m) = m"
proof (cases "m = 1")
  case True
  then show ?thesis unfolding kyber_encode_coeff_def kyber_decode_coeff_def by simp
next
  case False
  hence "m = 0" using assms by auto
  then show ?thesis unfolding kyber_encode_coeff_def kyber_decode_coeff_def by simp
qed
```

### Step 6: Key Generation

**USE THIS EXACT CODE**:
```isabelle
text \<open>
  Kyber.KeyGen():
  1. Sample random matrix A ∈ R_q^{k×k}
  2. Sample secret s with small coefficients (CBD_η1)
  3. Sample error e with small coefficients (CBD_η1)
  4. Compute t = As + e
  5. Return pk = (A, NTT(t)), sk = NTT(s)

  Note: In practice, A is derived from a seed ρ for compactness.
  We model it as an explicit matrix for clarity.
\<close>

definition kyber_keygen :: "kyber_matrix \<Rightarrow> kyber_vec \<Rightarrow> kyber_vec \<Rightarrow> kyber_pk \<times> kyber_sk" where
  "kyber_keygen A s e = (
    let s_hat = kyber_vec_ntt s in
    let e_hat = kyber_vec_ntt e in
    let As_hat = kyber_mat_vec_mult_ntt A s_hat in
    let t_hat = kyber_vec_add As_hat e_hat in
    let pk = \<lparr> pk_A = A, pk_t = t_hat \<rparr> in
    let sk = \<lparr> sk_s = s_hat, sk_pk = pk \<rparr> in
    (pk, sk))"

lemma kyber_keygen_pk_t_length:
  assumes "valid_kyber_matrix A p"
  assumes "valid_kyber_vec s p" and "valid_kyber_vec e p"
  shows "length (pk_t (fst (kyber_keygen A s e))) = kyber_k p"
  using assms unfolding kyber_keygen_def valid_kyber_matrix_def
  by (simp add: kyber_mat_vec_mult_ntt_length)
```

### Step 7: Encryption (PKE)

**USE THIS EXACT CODE**:
```isabelle
text \<open>
  Kyber.Encrypt(pk, m, r, e1, e2):
  1. Parse pk = (A, t̂)
  2. Sample r with small coefficients (randomness)
  3. Sample e1, e2 with small coefficients (CBD_η2)
  4. Compute u = A^T r + e1
  5. Compute v = <t̂, r̂> + e2 + encode(m)
  6. Return ct = (NTT(u), v)

  For deterministic encryption (needed for FO transform), r is derived from m.
\<close>

definition kyber_encrypt :: "kyber_pk \<Rightarrow> nat list \<Rightarrow> kyber_vec \<Rightarrow> kyber_vec \<Rightarrow> kyber_poly \<Rightarrow> kyber_ciphertext" where
  "kyber_encrypt pk msg r e1 e2 = (
    let A = pk_A pk in
    let t_hat = pk_t pk in
    let r_hat = kyber_vec_ntt r in
    let e1_hat = kyber_vec_ntt e1 in
    \<comment> \<open>u = A^T r + e1 in NTT domain\<close>
    let ATr_hat = kyber_mat_transpose_vec_mult_ntt A r_hat in
    let u_hat = kyber_vec_add ATr_hat e1_hat in
    \<comment> \<open>v = <t, r> + e2 + encode(m)\<close>
    let tr_hat = kyber_inner_prod_ntt t_hat r_hat in
    let tr = kyber_intt tr_hat in
    let m_encoded = kyber_encode_msg msg in
    let v = kyber_poly_add (kyber_poly_add tr e2) m_encoded in
    \<lparr> ct_u = u_hat, ct_v = v \<rparr>)"

lemma kyber_encrypt_u_length:
  assumes "valid_kyber_pk pk p"
  shows "length (ct_u (kyber_encrypt pk msg r e1 e2)) = kyber_k p"
  using assms unfolding kyber_encrypt_def valid_kyber_pk_def valid_kyber_matrix_def
  by (simp add: kyber_mat_vec_mult_ntt_length)
```

### Step 8: Decryption (PKE)

**USE THIS EXACT CODE**:
```isabelle
text \<open>
  Kyber.Decrypt(sk, ct):
  1. Parse ct = (û, v)
  2. Parse sk = ŝ
  3. Compute m' = v - <ŝ, û>
  4. Return decode(m')

  The noise term is: e2 + <e, r> - <s, e1>
  Decryption succeeds if this noise is small enough (< q/4).
\<close>

definition kyber_decrypt :: "kyber_sk \<Rightarrow> kyber_ciphertext \<Rightarrow> nat list" where
  "kyber_decrypt sk ct = (
    let s_hat = sk_s sk in
    let u_hat = ct_u ct in
    let v = ct_v ct in
    \<comment> \<open>Compute <s, u> in NTT domain, then INTT\<close>
    let su_hat = kyber_inner_prod_ntt s_hat u_hat in
    let su = kyber_intt su_hat in
    \<comment> \<open>m' = v - <s, u>\<close>
    let m_noisy = kyber_poly_sub v su in
    kyber_decode_msg m_noisy)"

lemma kyber_decrypt_length:
  "length (kyber_decrypt sk ct) = length (ct_v ct)"
  unfolding kyber_decrypt_def by (simp add: kyber_decode_msg_length)
```

### Step 9: Correctness Theorem

**USE THIS EXACT CODE**:
```isabelle
text \<open>
  Kyber Correctness:

  If the noise is bounded, decryption recovers the original message.

  Noise term: δ = e2 + <e, r> - <s, e1>

  Condition: For each coefficient i, |δ_i| < ⌈q/4⌉ = 833

  Under this condition: Decrypt(sk, Encrypt(pk, m)) = m

  We state this as a locale assumption, making it a verified interface contract.
  The locale parameter captures the correctness property that concrete
  instantiations must satisfy.
\<close>

definition kyber_noise_poly :: "kyber_vec \<Rightarrow> kyber_vec \<Rightarrow> kyber_vec \<Rightarrow> kyber_vec \<Rightarrow> kyber_poly \<Rightarrow> kyber_poly" where
  "kyber_noise_poly e r s e1 e2 = (
    \<comment> \<open>δ = e2 + <e, r> - <s, e1> (all in normal domain)\<close>
    let er = kyber_intt (kyber_inner_prod_ntt (kyber_vec_ntt e) (kyber_vec_ntt r)) in
    let se1 = kyber_intt (kyber_inner_prod_ntt (kyber_vec_ntt s) (kyber_vec_ntt e1)) in
    kyber_poly_sub (kyber_poly_add e2 er) se1)"

definition kyber_noise_bounded :: "kyber_poly \<Rightarrow> bool" where
  "kyber_noise_bounded delta = (\<forall>c \<in> set delta.
    let c' = (if c > 1664 then c - 3329 else c) in
    abs c' < 833)"

locale kyber_correct =
  fixes A :: kyber_matrix and s e r e1 :: kyber_vec and e2 :: kyber_poly and msg :: "nat list"
  assumes valid_msg: "length msg = 256" "\<forall>m \<in> set msg. m \<in> {0, 1}"
  assumes noise_ok: "kyber_noise_bounded (kyber_noise_poly e r s e1 e2)"
  assumes correctness: "\<And>pk sk ct.
    (pk, sk) = kyber_keygen A s e \<Longrightarrow>
    ct = kyber_encrypt pk msg r e1 e2 \<Longrightarrow>
    kyber_decrypt sk ct = msg"
begin

text \<open>Within this locale, correctness is assumed and KEM correctness follows.\<close>

end

text \<open>
  Noise bound analysis:

  Using CBD_η distribution, each coefficient of s, e, r, e1, e2 is bounded by η.

  |<e, r>| ≤ k · n · η² (sum of products)
  |<s, e1>| ≤ k · n · η²
  |e2| ≤ η

  Total: |δ| ≤ 2 · k · n · η² + η

  For Kyber768 (k=3, η=2): |δ| ≤ 2 · 3 · 256 · 4 + 2 = 6146
  This exceeds 833! So we need compression to reduce noise impact.

  In practice, Kyber uses carefully chosen parameters and compression
  to ensure correctness with overwhelming probability.
\<close>
```

### Step 10: KEM Interface

**USE THIS EXACT CODE**:
```isabelle
text \<open>
  Kyber KEM (Key Encapsulation Mechanism):

  The KEM wraps the PKE using implicit rejection (FO transform).

  KEM.Encaps(pk):
    1. Generate random message m
    2. (K, r) = G(m || pk)  -- derive key and randomness from hash
    3. ct = Encrypt(pk, m; r)
    4. Return (ct, K)

  KEM.Decaps(sk, ct):
    1. m' = Decrypt(sk, ct)
    2. (K', r') = G(m' || pk)
    3. ct' = Encrypt(pk, m'; r')
    4. If ct = ct' then return K' else return H(z || ct)  -- implicit rejection

  We model this abstractly without the hash functions.
\<close>

record kyber_kem_ct =
  kem_ct :: kyber_ciphertext
  kem_shared :: "int list"   \<comment> \<open>derived shared secret (simplified)\<close>

definition kyber_encaps_simple :: "kyber_pk \<Rightarrow> nat list \<Rightarrow> kyber_vec \<Rightarrow> kyber_vec \<Rightarrow> kyber_poly \<Rightarrow> kyber_kem_ct" where
  "kyber_encaps_simple pk msg r e1 e2 = (
    let ct = kyber_encrypt pk msg r e1 e2 in
    \<comment> \<open>In practice, shared secret K = H(m || ct)\<close>
    let K = msg in  \<comment> \<open>Simplified: use message directly\<close>
    \<lparr> kem_ct = ct, kem_shared = map int K \<rparr>)"

definition kyber_decaps_simple :: "kyber_sk \<Rightarrow> kyber_ciphertext \<Rightarrow> int list" where
  "kyber_decaps_simple sk ct = map int (kyber_decrypt sk ct)"

text \<open>
  KEM correctness follows from PKE correctness within the locale.
\<close>

context kyber_correct
begin

theorem kem_correctness:
  assumes "(pk, sk) = kyber_keygen A s e"
  assumes "kem = kyber_encaps_simple pk msg r e1 e2"
  shows "kyber_decaps_simple sk (kem_ct kem) = kem_shared kem"
  using correctness[OF assms(1)] assms(2)
  unfolding kyber_encaps_simple_def kyber_decaps_simple_def
  by simp

end
```

### Step 11: Code Export

**USE THIS EXACT CODE**:
```isabelle
export_code
  kyber_params.make valid_kyber_params
  kyber_n kyber_q kyber_k kyber_eta1 kyber_eta2 kyber_du kyber_dv
  kyber512_params kyber768_params kyber1024_params
  kyber_pk.make kyber_sk.make kyber_ciphertext.make
  pk_A pk_t sk_s sk_pk ct_u ct_v
  kyber_ntt kyber_intt kyber_poly_mult_ntt
  kyber_poly_add kyber_poly_sub
  kyber_vec_add kyber_vec_ntt kyber_vec_intt
  kyber_inner_prod_ntt
  kyber_mat_vec_mult_ntt kyber_transpose
  kyber_encode_msg kyber_decode_msg
  kyber_keygen kyber_encrypt kyber_decrypt
  kyber_encaps_simple kyber_decaps_simple
  in Haskell module_name "Canon.Crypto.Kyber"
```

## Constraints

- Theory name: `Kyber`
- Session: `Canon_Crypto` (depends on `Canon_Rings`)
- Imports: Prelude, ListVec, Zq, Norms, PolyMod, ModuleLWE, NTT
- Focus on correctness over efficiency optimizations
- Skip compression for MVP (add in future)
- Use sorry for main correctness theorem (algebraically involved)

## Proof Strategy Reference

| Goal Type | Recommended Tactic |
|-----------|-------------------|
| Record field access | `by simp` |
| Length preservation | `by (simp add: kyber_mat_vec_mult_ntt_length)` |
| Parameter validity | `unfolding valid_kyber_params_def by simp` |
| Message encoding | `unfolding kyber_encode_coeff_def by simp` |
| Case on bit | `proof (cases "m = 1")` |

## Key Insights

1. **NTT everywhere**: Most operations happen in NTT domain for efficiency
2. **Noise budget**: Correctness requires noise < q/4 ≈ 833
3. **CBD sampling**: Centered binomial distribution for secrets/errors
4. **Compression**: Real Kyber uses compression (omitted for MVP clarity)
5. **FO transform**: Provides CCA security from CPA-secure PKE
6. **k determines security**: k=2,3,4 for 512,768,1024 bit security

## Deliverable

A working Kyber.thy that:
1. Compiles as part of Canon_Crypto session
2. Defines Kyber parameter sets (512, 768, 1024)
3. Has NTT-accelerated polynomial operations
4. Implements KeyGen, Encrypt, Decrypt
5. States correctness theorem
6. Has simplified KEM interface
7. Exports to Haskell for NIST vector testing

## Testing Strategy (Post-Export)

After Haskell export, test against NIST KAT vectors:
1. Load NIST test vectors for Kyber512/768/1024
2. Verify KeyGen produces expected (pk, sk) pairs
3. Verify Encrypt produces expected ciphertext
4. Verify Decrypt recovers original message
5. Verify KEM encaps/decaps produce matching shared secrets
