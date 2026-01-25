(*
  Theory: LWE
  Author: Auto-generated

  Learning With Errors (LWE) problem definitions and cryptographic operations.
  Provides the foundation for LWE-based encryption schemes.
*)

theory LWE
  imports
    Main
    "HOL-Library.Code_Target_Numeral"
    "HOL-Library.Code_Target_Int"
    Lattice_Basics
    Polynomial_Ring
begin

section \<open>LWE Parameters\<close>

text \<open>
  LWE Parameters:
  - n: dimension of secret vector
  - m: number of samples
  - q: modulus
  - error bound B: errors sampled from [-B, B]
\<close>

record lwe_params =
  lwe_n :: nat
  lwe_m :: nat
  lwe_q :: int
  lwe_bound :: int

text \<open>Check if parameters are valid\<close>
definition valid_params :: "lwe_params \<Rightarrow> bool" where
  "valid_params p = (lwe_n p > 0 \<and> lwe_m p > 0 \<and> lwe_q p > 1 \<and> lwe_bound p > 0 \<and> lwe_bound p < lwe_q p div 4)"

text \<open>Standard parameter sets for different security levels\<close>
definition params_128 :: lwe_params where
  "params_128 = \<lparr> lwe_n = 512, lwe_m = 1024, lwe_q = 12289, lwe_bound = 3 \<rparr>"

definition params_256 :: lwe_params where
  "params_256 = \<lparr> lwe_n = 1024, lwe_m = 2048, lwe_q = 12289, lwe_bound = 3 \<rparr>"

section \<open>LWE Key Types\<close>

text \<open>Public key: matrix A and vector b = As + e\<close>
record lwe_public_key =
  pk_matrix :: matrix
  pk_vector :: vec

text \<open>Secret key: secret vector s\<close>
record lwe_secret_key =
  sk_vector :: vec

text \<open>Ciphertext: (u, v) where u = A^T r + e1, v = b^T r + e2 + encode(m)\<close>
record lwe_ciphertext =
  ct_vector :: vec
  ct_scalar :: int

section \<open>LWE Problem Definitions\<close>

text \<open>
  The LWE problem: Given (A, b) where b = As + e for small e,
  find s (search-LWE) or distinguish from random (decision-LWE).
\<close>

text \<open>Compute b = As + e mod q\<close>
definition lwe_sample :: "matrix \<Rightarrow> vec \<Rightarrow> vec \<Rightarrow> int \<Rightarrow> vec" where
  "lwe_sample A s e q = vec_mod (vec_add (mat_vec_mult A s) e) q"

text \<open>Check if a vector could be a valid error (small norm)\<close>
definition is_valid_error :: "vec \<Rightarrow> int \<Rightarrow> bool" where
  "is_valid_error e B = list_all (\<lambda>x. \<bar>x\<bar> \<le> B) e"

section \<open>Message Encoding\<close>

text \<open>Encode a bit as element of Z_q: 0 -> 0, 1 -> q/2\<close>
definition encode_bit :: "int \<Rightarrow> bool \<Rightarrow> int" where
  "encode_bit q b = (if b then q div 2 else 0)"

text \<open>Decode element of Z_q to bit: closer to 0 -> False, closer to q/2 -> True\<close>
definition decode_bit :: "int \<Rightarrow> int \<Rightarrow> bool" where
  "decode_bit q x = (let x' = x mod q in \<bar>x' - q div 2\<bar> < \<bar>x'\<bar>)"

text \<open>Alternative decoding using centered representation\<close>
definition decode_bit_centered :: "int \<Rightarrow> int \<Rightarrow> bool" where
  "decode_bit_centered q x = (let x' = mod_centered x q in x' > q div 4 \<or> x' < -(q div 4))"

section \<open>Encryption Operations (Functional Specifications)\<close>

text \<open>
  Key generation produces:
  - A: random m x n matrix over Z_q
  - s: secret vector of dimension n (small coefficients)
  - e: error vector of dimension m (small coefficients)
  - b: public vector b = As + e mod q

  Public key: (A, b)
  Secret key: s
\<close>

text \<open>Construct public key from components\<close>
definition make_public_key :: "matrix \<Rightarrow> vec \<Rightarrow> vec \<Rightarrow> int \<Rightarrow> lwe_public_key" where
  "make_public_key A s e q = \<lparr> pk_matrix = A, pk_vector = lwe_sample A s e q \<rparr>"

text \<open>Construct secret key\<close>
definition make_secret_key :: "vec \<Rightarrow> lwe_secret_key" where
  "make_secret_key s = \<lparr> sk_vector = s \<rparr>"

text \<open>
  Encryption of bit m:
  - Sample random vector r of dimension m (binary or small)
  - Sample error vectors e1 (dim n), e2 (scalar)
  - u = A^T r + e1 mod q
  - v = <b, r> + e2 + encode(m) mod q

  Ciphertext: (u, v)
\<close>

text \<open>Matrix transpose\<close>
definition transpose :: "matrix \<Rightarrow> matrix" where
  "transpose A = (
    let m = length A;
        n = (if m = 0 then 0 else length (hd A))
    in map (\<lambda>j. map (\<lambda>i. (A ! i) ! j) [0..<m]) [0..<n])"

text \<open>Encrypt a single bit\<close>
definition lwe_encrypt_bit :: "lwe_public_key \<Rightarrow> int \<Rightarrow> vec \<Rightarrow> vec \<Rightarrow> int \<Rightarrow> bool \<Rightarrow> lwe_ciphertext" where
  "lwe_encrypt_bit pk q r e1 e2 m = (
    let A = pk_matrix pk;
        b = pk_vector pk;
        At = transpose A;
        u = vec_mod (vec_add (mat_vec_mult At r) e1) q;
        v = (inner_product b r + e2 + encode_bit q m) mod q
    in \<lparr> ct_vector = u, ct_scalar = v \<rparr>)"

text \<open>
  Decryption:
  - Compute v - <s, u> mod q
  - Decode to bit
\<close>

text \<open>Decrypt ciphertext\<close>
definition lwe_decrypt :: "lwe_secret_key \<Rightarrow> int \<Rightarrow> lwe_ciphertext \<Rightarrow> bool" where
  "lwe_decrypt sk q ct = (
    let s = sk_vector sk;
        u = ct_vector ct;
        v = ct_scalar ct;
        diff = (v - inner_product s u) mod q
    in decode_bit q diff)"

text \<open>Alternative decryption with centered decoding\<close>
definition lwe_decrypt_centered :: "lwe_secret_key \<Rightarrow> int \<Rightarrow> lwe_ciphertext \<Rightarrow> bool" where
  "lwe_decrypt_centered sk q ct = (
    let s = sk_vector sk;
        u = ct_vector ct;
        v = ct_scalar ct;
        diff = v - inner_product s u
    in decode_bit_centered q diff)"

section \<open>Correctness Condition\<close>

text \<open>
  For correct decryption, the total error must be small enough:
  |<e, r> + e2 - <e1, s>| < q/4
\<close>

definition decryption_error :: "vec \<Rightarrow> vec \<Rightarrow> vec \<Rightarrow> vec \<Rightarrow> int \<Rightarrow> int" where
  "decryption_error e r e1 s e2 = inner_product e r + e2 - inner_product e1 s"

definition correct_decryption_condition :: "int \<Rightarrow> int \<Rightarrow> bool" where
  "correct_decryption_condition q error_term = (\<bar>mod_centered error_term q\<bar> < q div 4)"

section \<open>Ring-LWE Variants\<close>

text \<open>Ring-LWE uses polynomial rings instead of vectors\<close>

record rlwe_params =
  rlwe_n :: nat    \<comment> \<open>Ring dimension (degree of cyclotomic polynomial)\<close>
  rlwe_q :: int    \<comment> \<open>Modulus\<close>
  rlwe_bound :: int \<comment> \<open>Error bound\<close>

record rlwe_public_key =
  rlwe_pk_a :: poly
  rlwe_pk_b :: poly

record rlwe_secret_key =
  rlwe_sk :: poly

record rlwe_ciphertext =
  rlwe_ct_u :: poly
  rlwe_ct_v :: poly

text \<open>Ring-LWE sample: b = a*s + e in R_q\<close>
definition rlwe_sample :: "nat \<Rightarrow> int \<Rightarrow> poly \<Rightarrow> poly \<Rightarrow> poly \<Rightarrow> poly" where
  "rlwe_sample n q a s e = ring_add q (ring_mult n q a s) e"

section \<open>Haskell Code Export\<close>

export_code
  \<comment> \<open>Parameters\<close>
  lwe_params.make valid_params params_128 params_256
  lwe_n lwe_m lwe_q lwe_bound
  \<comment> \<open>Key types\<close>
  lwe_public_key.make lwe_secret_key.make lwe_ciphertext.make
  pk_matrix pk_vector sk_vector ct_vector ct_scalar
  \<comment> \<open>LWE operations\<close>
  lwe_sample is_valid_error
  encode_bit decode_bit decode_bit_centered
  make_public_key make_secret_key transpose
  lwe_encrypt_bit lwe_decrypt lwe_decrypt_centered
  decryption_error correct_decryption_condition
  \<comment> \<open>Ring-LWE\<close>
  rlwe_params.make rlwe_n rlwe_q rlwe_bound
  rlwe_public_key.make rlwe_secret_key.make rlwe_ciphertext.make
  rlwe_pk_a rlwe_pk_b rlwe_sk rlwe_ct_u rlwe_ct_v
  rlwe_sample
  in Haskell
  module_name LWE
  file_prefix LWE

end
