theory LatticeCrypto
  imports Main "HOL-Library.Code_Target_Numeral"
begin

type_synonym int_vec = "int list"
type_synonym int_matrix = "int list list"

record lwe_params =
  lwe_n :: nat
  lwe_q :: int
  lwe_num_samples :: nat

record lwe_public_key =
  pk_A :: int_matrix
  pk_b :: int_vec

record lwe_secret_key =
  sk_s :: int_vec

record lwe_ciphertext =
  ct_u :: int_vec
  ct_v :: int

definition vec_add :: "int_vec => int_vec => int_vec" where
  "vec_add xs ys = map2 (+) xs ys"

definition vec_mod :: "int_vec => int => int_vec" where
  "vec_mod v q = map (%x. x mod q) v"

definition inner_prod :: "int_vec => int_vec => int" where
  "inner_prod u v = sum_list (map2 (*) u v)"

definition mat_vec_mult :: "int_matrix => int_vec => int_vec" where
  "mat_vec_mult A x = map (%row. inner_prod row x) A"

definition mat_transpose_vec_mult :: "int_matrix => int_vec => int_vec" where
  "mat_transpose_vec_mult A r = mat_vec_mult (transpose A) r"

lemma inner_prod_vec_add:
  assumes len_xy: "length x = length y"
    and len_xr: "length x = length r"
  shows "inner_prod (vec_add x y) r = inner_prod x r + inner_prod y r"
using len_xy len_xr
proof (induct x y arbitrary: r rule: list_induct2)
  case Nil
  then show ?case
    by (simp add: vec_add_def inner_prod_def)
next
  case (Cons a xs b ys)
  then obtain c rs where r: "r = c # rs"
    by (cases r) auto
  with Cons show ?case
    by (simp add: vec_add_def inner_prod_def algebra_simps)
qed

definition encode_bit :: "int => bool => int" where
  "encode_bit q b = (if b then q div 2 else 0)"

definition decode_bit :: "int => int => bool" where
  "decode_bit q d = (d >= q div 2)"

lemma div2_pos:
  fixes q :: int
  assumes "q > 2"
  shows "q div 2 > 0"
proof -
  have "2 <= q" using assms by arith
  have "0 < q div 2"
    using pos_imp_zdiv_pos_iff[of 2 q] `2 <= q` by simp
  then show ?thesis by simp
qed

lemma encode_decode_inverse:
  fixes q :: int
  assumes "q > 2"
  shows "decode_bit q (encode_bit q b) = b"
proof (cases b)
  case True
  then show ?thesis
    by (simp add: decode_bit_def encode_bit_def)
next
  case False
  have "q div 2 > 0" using div2_pos[OF assms] .
  then show ?thesis
    using False by (simp add: decode_bit_def encode_bit_def)
qed

definition lwe_encrypt :: "lwe_public_key => int => int_vec => bool => lwe_ciphertext" where
  "lwe_encrypt pk q r m =
     (let u = vec_mod (mat_transpose_vec_mult (pk_A pk) r) q;
          v = (inner_prod (pk_b pk) r + encode_bit q m) mod q
      in (| ct_u = u, ct_v = v |))"

definition lwe_decrypt :: "lwe_secret_key => int => lwe_ciphertext => bool" where
  "lwe_decrypt sk q ct =
     (let d = (ct_v ct - inner_prod (sk_s sk) (ct_u ct)) mod q
      in decode_bit q d)"

lemma decryption_error_term:
  fixes q :: int
  assumes b_def: "pk_b pk = vec_add (mat_vec_mult (pk_A pk) (sk_s sk)) e"
    and len_e: "length (mat_vec_mult (pk_A pk) (sk_s sk)) = length e"
    and len_r: "length r = length (mat_vec_mult (pk_A pk) (sk_s sk))"
    and u_bound: "vec_mod (mat_transpose_vec_mult (pk_A pk) r) q =
                  mat_transpose_vec_mult (pk_A pk) r"
    and v_bound: "(inner_prod (pk_b pk) r + encode_bit q m) mod q =
                  inner_prod (pk_b pk) r + encode_bit q m"
    and iprod: "inner_prod (sk_s sk) (mat_transpose_vec_mult (pk_A pk) r) =
                inner_prod (mat_vec_mult (pk_A pk) (sk_s sk)) r"
  shows "(ct_v (lwe_encrypt pk q r m) -
          inner_prod (sk_s sk) (ct_u (lwe_encrypt pk q r m))) mod q =
         (inner_prod e r + encode_bit q m) mod q"
proof -
  have b_iprod:
    "inner_prod (pk_b pk) r =
     inner_prod (mat_vec_mult (pk_A pk) (sk_s sk)) r + inner_prod e r"
  proof -
    have "inner_prod (pk_b pk) r =
          inner_prod (vec_add (mat_vec_mult (pk_A pk) (sk_s sk)) e) r"
      using b_def by simp
    also have "... =
          inner_prod (mat_vec_mult (pk_A pk) (sk_s sk)) r + inner_prod e r"
      using len_e len_r by (simp add: inner_prod_vec_add)
    finally show ?thesis .
  qed
  have u_ct:
    "ct_u (lwe_encrypt pk q r m) = mat_transpose_vec_mult (pk_A pk) r"
    using u_bound by (simp add: lwe_encrypt_def)
  have v_ct:
    "ct_v (lwe_encrypt pk q r m) = inner_prod (pk_b pk) r + encode_bit q m"
    using v_bound by (simp add: lwe_encrypt_def)
  show ?thesis
    using b_iprod u_ct v_ct iprod
    by (simp add: algebra_simps)
qed

lemma correctness_condition:
  fixes q :: int
  assumes q_gt: "q > 2"
    and b_def: "pk_b pk = vec_add (mat_vec_mult (pk_A pk) (sk_s sk)) e"
    and len_e: "length (mat_vec_mult (pk_A pk) (sk_s sk)) = length e"
    and len_r: "length r = length (mat_vec_mult (pk_A pk) (sk_s sk))"
    and u_bound: "vec_mod (mat_transpose_vec_mult (pk_A pk) r) q =
                  mat_transpose_vec_mult (pk_A pk) r"
    and v_bound: "(inner_prod (pk_b pk) r + encode_bit q m) mod q =
                  inner_prod (pk_b pk) r + encode_bit q m"
    and iprod: "inner_prod (sk_s sk) (mat_transpose_vec_mult (pk_A pk) r) =
                inner_prod (mat_vec_mult (pk_A pk) (sk_s sk)) r"
    and noise_mod: "(inner_prod e r + encode_bit q m) mod q =
                    inner_prod e r + encode_bit q m"
    and noise_abs: "abs (inner_prod e r) < q div 4"
    and noise_nonneg: "0 <= inner_prod e r"
  shows "lwe_decrypt sk q (lwe_encrypt pk q r m) = m"
proof (cases m)
  case False
  have d_eq:
    "lwe_decrypt sk q (lwe_encrypt pk q r m) =
      decode_bit q ((inner_prod e r + encode_bit q m) mod q)"
    using decryption_error_term[OF b_def len_e len_r u_bound v_bound iprod]
    by (simp add: lwe_decrypt_def)
  have d_eq2:
    "decode_bit q ((inner_prod e r + encode_bit q m) mod q) =
     decode_bit q (inner_prod e r)"
    using False noise_mod by (simp add: encode_bit_def)
  have q_nonneg: "0 <= q" using q_gt by arith
  have div4_le: "q div 4 <= q div 2"
    using zdiv_mono2[of q 4 2] q_nonneg by simp
  have noise_lt4: "inner_prod e r < q div 4"
    using noise_abs noise_nonneg by simp
  have noise_lt2: "inner_prod e r < q div 2"
    using noise_lt4 div4_le by arith
  have "decode_bit q (inner_prod e r) = False"
    using noise_lt2 by (simp add: decode_bit_def)
  then show ?thesis
    using d_eq d_eq2 False by simp
next
  case True
  have d_eq:
    "lwe_decrypt sk q (lwe_encrypt pk q r m) =
      decode_bit q ((inner_prod e r + encode_bit q m) mod q)"
    using decryption_error_term[OF b_def len_e len_r u_bound v_bound iprod]
    by (simp add: lwe_decrypt_def)
  have d_eq2:
    "decode_bit q ((inner_prod e r + encode_bit q m) mod q) =
     decode_bit q (inner_prod e r + q div 2)"
    using True noise_mod by (simp add: encode_bit_def)
  have "decode_bit q (inner_prod e r + q div 2) = True"
    using noise_nonneg by (simp add: decode_bit_def)
  then show ?thesis
    using d_eq d_eq2 True by simp
qed

export_code
  vec_add vec_mod inner_prod
  mat_vec_mult transpose mat_transpose_vec_mult
  encode_bit decode_bit
  lwe_encrypt lwe_decrypt
  in Haskell module_name "Lattice.LWE_Regev"

end
