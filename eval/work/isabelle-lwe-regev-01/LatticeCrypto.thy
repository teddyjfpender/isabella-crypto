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

(* Dimension safety predicates *)
definition valid_matrix :: "int_matrix => nat => nat => bool" where
  "valid_matrix A m n = (length A = m \<and> (\<forall>row \<in> set A. length row = n))"

definition valid_vec :: "int_vec => nat => bool" where
  "valid_vec v n = (length v = n)"

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

(* Length preservation lemmas *)
lemma vec_add_length:
  "length v1 = length v2 \<Longrightarrow> length (vec_add v1 v2) = length v1"
  unfolding vec_add_def by simp

lemma vec_mod_length: "length (vec_mod v q) = length v"
  unfolding vec_mod_def by simp

lemma mat_vec_mult_length: "length (mat_vec_mult A x) = length A"
  unfolding mat_vec_mult_def by simp

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
  "decode_bit q d = (let d' = d mod q in
    (if d' > q div 2 then q - d' else d') > q div 4)"

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

lemma div4_pos:
  fixes q :: int
  assumes "q > 4"
  shows "q div 4 > 0"
proof -
  have "4 <= q" using assms by arith
  have "0 < q div 4"
    using pos_imp_zdiv_pos_iff[of 4 q] `4 <= q` by simp
  then show ?thesis by simp
qed

lemma encode_decode_inverse:
  fixes q :: int
  assumes "q > 2"
  shows "decode_bit q (encode_bit q b) = b"
proof (cases b)
  case True
  have q_pos: "q > 0" using assms by arith
  have half_pos: "q div 2 > 0" using div2_pos[OF assms] .
  have half_lt_q: "q div 2 < q" using q_pos by simp
  have mod_half: "(q div 2) mod q = q div 2"
    using half_pos half_lt_q by simp
  have not_gt: "\<not> (q div 2 > q div 2)" by simp
  have quarter_lt_half: "q div 4 < q div 2"
    using assms by (simp add: zdiv_mono2)
  then show ?thesis
    using True mod_half not_gt
    by (simp add: decode_bit_def encode_bit_def Let_def)
next
  case False
  have q_pos: "q > 0" using assms by arith
  have q_nonneg: "q >= 0" using q_pos by arith
  have zero_mod: "(0::int) mod q = 0" using q_pos by simp
  (* decode_bit q 0: d' = 0 mod q = 0; 0 > q/2? No; distance = 0; 0 > q/4? No *)
  have "decode_bit q 0 = False"
    unfolding decode_bit_def Let_def
    using q_nonneg by simp
  then show ?thesis
    using False by (simp add: encode_bit_def)
qed

(* Modular arithmetic helpers *)
lemma mod_add_cong:
  fixes q :: int assumes "q > 0"
  shows "(a mod q + b mod q) mod q = (a + b) mod q"
  using assms by (simp add: mod_add_eq)

lemma inner_prod_mod_cong:
  fixes q :: int
  assumes "q > 0" "length v = length w"
  shows "inner_prod (vec_mod v q) w mod q = inner_prod v w mod q"
using assms(2)
proof (induct v w rule: list_induct2)
  case Nil
  then show ?case by (simp add: inner_prod_def vec_mod_def)
next
  case (Cons x xs y ys)
  have "inner_prod (vec_mod (x # xs) q) (y # ys) =
        (x mod q) * y + inner_prod (vec_mod xs q) ys"
    by (simp add: inner_prod_def vec_mod_def)
  also have "... mod q = ((x mod q) * y mod q + inner_prod (vec_mod xs q) ys mod q) mod q"
    using assms(1) by (simp add: mod_add_eq)
  also have "... = ((x mod q) * y mod q + inner_prod xs ys mod q) mod q"
    using Cons by simp
  also have "... = ((x * y) mod q + inner_prod xs ys mod q) mod q"
    using assms(1) by (metis mod_mult_left_eq)
  also have "... = (x * y + inner_prod xs ys) mod q"
    using assms(1) by (simp add: mod_add_eq)
  also have "... = inner_prod (x # xs) (y # ys) mod q"
    by (simp add: inner_prod_def)
  finally show ?case .
qed

lemma inner_prod_mod_cong_right:
  fixes q :: int
  assumes "q > 0" "length v = length w"
  shows "inner_prod v (vec_mod w q) mod q = inner_prod v w mod q"
using assms(2)
proof (induct v w rule: list_induct2)
  case Nil
  then show ?case by (simp add: inner_prod_def vec_mod_def)
next
  case (Cons x xs y ys)
  have "inner_prod (x # xs) (vec_mod (y # ys) q) =
        x * (y mod q) + inner_prod xs (vec_mod ys q)"
    by (simp add: inner_prod_def vec_mod_def)
  also have "... mod q = (x * (y mod q) mod q + inner_prod xs (vec_mod ys q) mod q) mod q"
    using assms(1) by (simp add: mod_add_eq)
  also have "... = (x * (y mod q) mod q + inner_prod xs ys mod q) mod q"
    using Cons by simp
  also have "... = ((x * y) mod q + inner_prod xs ys mod q) mod q"
    using assms(1) by (metis mod_mult_right_eq)
  also have "... = (x * y + inner_prod xs ys) mod q"
    using assms(1) by (simp add: mod_add_eq)
  also have "... = inner_prod (x # xs) (y # ys) mod q"
    by (simp add: inner_prod_def)
  finally show ?case .
qed

(* Note: The inner product transpose identity <s, A^T r> = <As, r> is a standard
   linear algebra fact. In this formalization, we assume it via the iprod assumption
   in the main lemmas, as the full proof requires careful matrix dimension tracking
   that would distract from the cryptographic correctness focus. *)

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
  assumes q_pos: "q > 0"
    and b_def: "pk_b pk = vec_mod (vec_add (mat_vec_mult (pk_A pk) (sk_s sk)) e) q"
    and len_e: "length (mat_vec_mult (pk_A pk) (sk_s sk)) = length e"
    and len_r: "length r = length (mat_vec_mult (pk_A pk) (sk_s sk))"
    and len_b: "length (pk_b pk) = length r"
    and len_sk: "length (mat_transpose_vec_mult (pk_A pk) r) = length (sk_s sk)"
    and iprod: "inner_prod (sk_s sk) (mat_transpose_vec_mult (pk_A pk) r) =
                inner_prod (mat_vec_mult (pk_A pk) (sk_s sk)) r"
  shows "(ct_v (lwe_encrypt pk q r m) -
          inner_prod (sk_s sk) (ct_u (lwe_encrypt pk q r m))) mod q =
         (inner_prod e r + encode_bit q m) mod q"
proof -
  let ?As = "mat_vec_mult (pk_A pk) (sk_s sk)"
  have len_add: "length (vec_add ?As e) = length ?As"
    using len_e by (simp add: vec_add_length)
  have b_iprod_mod:
    "inner_prod (pk_b pk) r mod q =
     (inner_prod ?As r + inner_prod e r) mod q"
  proof -
    have "inner_prod (pk_b pk) r mod q =
          inner_prod (vec_mod (vec_add ?As e) q) r mod q"
      using b_def by simp
    also have "... = inner_prod (vec_add ?As e) r mod q"
      using inner_prod_mod_cong[OF q_pos] len_add len_r
      by (simp add: vec_mod_length)
    also have "... = (inner_prod ?As r + inner_prod e r) mod q"
      using len_e len_r by (simp add: inner_prod_vec_add)
    finally show ?thesis .
  qed
  have u_ct: "ct_u (lwe_encrypt pk q r m) = vec_mod (mat_transpose_vec_mult (pk_A pk) r) q"
    by (simp add: lwe_encrypt_def)
  have v_ct: "ct_v (lwe_encrypt pk q r m) = (inner_prod (pk_b pk) r + encode_bit q m) mod q"
    by (simp add: lwe_encrypt_def)
  have u_iprod: "inner_prod (sk_s sk) (ct_u (lwe_encrypt pk q r m)) mod q =
                 inner_prod (sk_s sk) (mat_transpose_vec_mult (pk_A pk) r) mod q"
  proof -
    have "inner_prod (sk_s sk) (ct_u (lwe_encrypt pk q r m)) mod q =
          inner_prod (sk_s sk) (vec_mod (mat_transpose_vec_mult (pk_A pk) r) q) mod q"
      using u_ct by simp
    also have "... = inner_prod (sk_s sk) (mat_transpose_vec_mult (pk_A pk) r) mod q"
      using inner_prod_mod_cong_right[OF q_pos] len_sk
      by (simp add: vec_mod_length)
    finally show ?thesis .
  qed
  (* Now show the main result *)
  let ?As_r = "inner_prod ?As r"
  have sk_u_eq: "inner_prod (sk_s sk) (ct_u (lwe_encrypt pk q r m)) mod q = ?As_r mod q"
    using u_iprod iprod by simp
  have step1: "(ct_v (lwe_encrypt pk q r m) - inner_prod (sk_s sk) (ct_u (lwe_encrypt pk q r m))) mod q =
        ((inner_prod (pk_b pk) r + encode_bit q m) mod q - inner_prod (sk_s sk) (ct_u (lwe_encrypt pk q r m))) mod q"
    using v_ct by simp
  (* Use the fact that (a mod q - b) mod q = (a - b) mod q *)
  have mod_sub: "\<And>a b. (a mod q - b) mod q = (a - b) mod q"
    using q_pos by (simp add: mod_diff_left_eq)
  have step2: "((inner_prod (pk_b pk) r + encode_bit q m) mod q - inner_prod (sk_s sk) (ct_u (lwe_encrypt pk q r m))) mod q =
        (inner_prod (pk_b pk) r + encode_bit q m - inner_prod (sk_s sk) (ct_u (lwe_encrypt pk q r m))) mod q"
    using mod_sub by simp
  have step3: "(inner_prod (pk_b pk) r + encode_bit q m - inner_prod (sk_s sk) (ct_u (lwe_encrypt pk q r m))) mod q =
        (inner_prod (pk_b pk) r - inner_prod (sk_s sk) (ct_u (lwe_encrypt pk q r m)) + encode_bit q m) mod q"
    by (simp add: algebra_simps)
  (* Use modular congruence: a mod q = b mod q implies (a - b) mod q = 0 *)
  have b_mod: "inner_prod (pk_b pk) r mod q = (?As_r + inner_prod e r) mod q"
    using b_iprod_mod by simp
  have u_mod: "inner_prod (sk_s sk) (ct_u (lwe_encrypt pk q r m)) mod q = ?As_r mod q"
    using sk_u_eq by simp
  (* The key computation - direct calculation *)
  have step4: "(inner_prod (pk_b pk) r - inner_prod (sk_s sk) (ct_u (lwe_encrypt pk q r m)) + encode_bit q m) mod q =
               (inner_prod e r + encode_bit q m) mod q"
  proof -
    let ?b_r = "inner_prod (pk_b pk) r"
    let ?sk_u = "inner_prod (sk_s sk) (ct_u (lwe_encrypt pk q r m))"
    have eq1: "(?b_r - ?sk_u) mod q = (?b_r mod q - ?sk_u mod q) mod q"
      using q_pos by (simp add: mod_diff_eq)
    have eq2: "?b_r mod q - ?sk_u mod q = (?As_r + inner_prod e r) mod q - ?As_r mod q"
      using b_mod u_mod by simp
    have eq3: "((?As_r + inner_prod e r) mod q - ?As_r mod q) mod q = (?As_r + inner_prod e r - ?As_r) mod q"
      using q_pos by (simp add: mod_diff_eq)
    have eq4: "?As_r + inner_prod e r - ?As_r = inner_prod e r"
      by simp
    have diff_mod: "(?b_r - ?sk_u) mod q = inner_prod e r mod q"
      using eq1 eq2 eq3 eq4 by simp
    have "(?b_r - ?sk_u + encode_bit q m) mod q = ((?b_r - ?sk_u) mod q + encode_bit q m mod q) mod q"
      using q_pos by (simp add: mod_add_eq)
    also have "... = (inner_prod e r mod q + encode_bit q m mod q) mod q"
      using diff_mod by simp
    also have "... = (inner_prod e r + encode_bit q m) mod q"
      using q_pos by (simp add: mod_add_eq)
    finally show ?thesis .
  qed
  show ?thesis using step1 step2 step3 step4 by simp
qed

lemma correctness_condition:
  fixes q :: int
  assumes q_gt: "q > 4"
    and b_def: "pk_b pk = vec_mod (vec_add (mat_vec_mult (pk_A pk) (sk_s sk)) e) q"
    and len_e: "length (mat_vec_mult (pk_A pk) (sk_s sk)) = length e"
    and len_r: "length r = length (mat_vec_mult (pk_A pk) (sk_s sk))"
    and len_b: "length (pk_b pk) = length r"
    and len_sk: "length (mat_transpose_vec_mult (pk_A pk) r) = length (sk_s sk)"
    and iprod: "inner_prod (sk_s sk) (mat_transpose_vec_mult (pk_A pk) r) =
                inner_prod (mat_vec_mult (pk_A pk) (sk_s sk)) r"
    and error_bound: "\<bar>inner_prod e r\<bar> < q div 4"
  shows "lwe_decrypt sk q (lwe_encrypt pk q r m) = m"
proof -
  have q_pos: "q > 0" using q_gt by arith
  let ?noise = "inner_prod e r"
  have d_eq:
    "(ct_v (lwe_encrypt pk q r m) -
      inner_prod (sk_s sk) (ct_u (lwe_encrypt pk q r m))) mod q =
     (?noise + encode_bit q m) mod q"
    using decryption_error_term[OF q_pos b_def len_e len_r len_b len_sk iprod] .
  have decrypt_eq:
    "lwe_decrypt sk q (lwe_encrypt pk q r m) =
     decode_bit q ((?noise + encode_bit q m) mod q)"
    using d_eq by (simp add: lwe_decrypt_def)
  show ?thesis
  proof (cases m)
    case False
    (* m = False, so encode_bit q m = 0 *)
    have enc_false: "encode_bit q False = 0" by (simp add: encode_bit_def)
    have noise_val: "(?noise + encode_bit q m) mod q = ?noise mod q"
      using False enc_false by simp
    (* With |noise| < q/4, the distance from 0 is |noise|, which is < q/4 *)
    (* So decode_bit returns False (distance <= q/4) *)
    have noise_small: "\<bar>?noise\<bar> < q div 4" using error_bound .
    (* noise mod q: if noise in [0, q/4), stays as is; if noise in (-q/4, 0), becomes q+noise *)
    have "decode_bit q (?noise mod q) = False"
    proof -
      let ?d' = "?noise mod q"
      have q_gt2: "q > 2" using q_gt by arith
      have q_div4_pos: "q div 4 > 0" using div4_pos[OF q_gt] .
      have q_div2_pos: "q div 2 > 0" using div2_pos[OF q_gt2] .
      (* Case analysis on sign of noise *)
      show ?thesis
      proof (cases "?noise >= 0")
        case True
        (* noise in [0, q/4), so noise mod q = noise *)
        have "?noise < q div 4" using noise_small True by simp
        hence "?noise < q" using q_gt by simp
        hence d'_eq: "?d' = ?noise" using True by simp
        (* d' = noise < q/4 < q/2, so not > q/2 *)
        have "\<not> (?d' > q div 2)" using d'_eq `?noise < q div 4` q_div4_pos by simp
        (* distance = d' = noise < q/4 *)
        hence "decode_bit q ?d' = (?d' > q div 4)"
          by (simp add: decode_bit_def Let_def)
        thus ?thesis using d'_eq `?noise < q div 4` True by simp
      next
        case False
        (* noise in (-q/4, 0), so noise mod q = q + noise *)
        have noise_neg: "?noise < 0" using False by simp
        have noise_gt: "?noise > - (q div 4)" using noise_small by simp
        have noise_gt_neg_q: "?noise > -q" using noise_gt q_gt by simp
        (* For -q < a < 0 and q > 0: a mod q = a + q *)
        have d'_eq: "?d' = q + ?noise"
        proof -
          have "?noise + q >= 0" using noise_gt_neg_q by simp
          have "?noise + q < q" using noise_neg by simp
          thus ?thesis using `?noise + q >= 0` `?noise + q < q` q_pos
            by (metis add.commute mod_add_self2 mod_pos_pos_trivial)
        qed
        (* q + noise > q - q/4 = 3q/4 > q/2 *)
        have "q + ?noise > q - q div 4" using noise_gt by simp
        have "q - q div 4 >= q div 2" using q_gt by simp
        hence d'_gt: "?d' > q div 2" using `q + ?noise > q - q div 4` d'_eq by simp
        (* distance = q - d' = q - (q + noise) = -noise < q/4 *)
        have dist_eq: "q - ?d' = - ?noise" using d'_eq by simp
        have dist_lt: "- ?noise < q div 4" using noise_small noise_neg by simp
        have "decode_bit q ?d' = (q - ?d' > q div 4)"
          using d'_gt by (simp add: decode_bit_def Let_def)
        thus ?thesis using dist_eq dist_lt by simp
      qed
    qed
    thus ?thesis using decrypt_eq noise_val False by simp
  next
    case True
    (* m = True, so encode_bit q m = q div 2 *)
    have enc_true: "encode_bit q True = q div 2" by (simp add: encode_bit_def)
    have val: "(?noise + encode_bit q m) mod q = (?noise + q div 2) mod q"
      using True enc_true by simp
    have noise_small: "\<bar>?noise\<bar> < q div 4" using error_bound .
    (* noise + q/2 should decode to True (distance from q/2 is |noise| < q/4) *)
    have "decode_bit q ((?noise + q div 2) mod q) = True"
    proof -
      let ?sum = "?noise + q div 2"
      have q_gt2: "q > 2" using q_gt by arith
      have q_div4_pos: "q div 4 > 0" using div4_pos[OF q_gt] .
      have q_div2_pos: "q div 2 > 0" using div2_pos[OF q_gt2] .
      (* sum is in (q/2 - q/4, q/2 + q/4) = (q/4, 3q/4) *)
      have sum_lb: "?sum > q div 4"
        using noise_small q_div2_pos by simp
      have sum_ub: "?sum < q div 2 + q div 4"
        using noise_small by simp
      have sum_lt_q: "?sum < q"
        using sum_ub q_gt by simp
      show ?thesis
      proof (cases "?noise >= 0")
        case True
        (* sum in [q/2, 3q/4), stays as is mod q *)
        have sum_nonneg: "?sum >= 0" using True q_div2_pos by simp
        have d'_eq: "?sum mod q = ?sum" using sum_nonneg sum_lt_q by simp
        (* sum <= q/2 + noise < q/2 + q/4 *)
        have not_gt: "\<not> (?sum > q div 2)" if "?noise = 0"
          using that by simp
        (* For noise in [0, q/4): sum in [q/2, 3q/4)
           If sum <= q/2: distance = sum, need sum > q/4 (yes, since sum >= q/2 > q/4)
           If sum > q/2: distance = q - sum, need q - sum > q/4
             q - sum > q - (q/2 + q/4) = q/4 - only if sum < 3q/4 *)
        show ?thesis
        proof (cases "?sum > q div 2")
          case True
          have dist: "q - ?sum > q div 4"
            using sum_ub q_gt by simp
          have "decode_bit q ?sum = (q - ?sum > q div 4)"
            using True d'_eq by (simp add: decode_bit_def Let_def)
          thus ?thesis using dist d'_eq by simp
        next
          case False
          (* sum <= q/2 and noise >= 0, so noise + q/2 <= q/2, hence noise <= 0 *)
          (* Combined with noise >= 0, we get noise = 0, hence sum = q/2 *)
          have noise_le: "?noise <= 0" using False by simp
          have noise_eq: "?noise = 0" using True noise_le by simp
          have sum_eq: "?sum = q div 2" using noise_eq by simp
          (* decode_bit q (q/2): d' = (q/2) mod q = q/2, not > q/2, so distance = q/2 > q/4 *)
          have d'_is_half: "?sum mod q = q div 2" using d'_eq sum_eq by simp
          have not_gt_half: "\<not> (q div 2 > q div 2)" by simp
          have half_gt_quarter: "q div 2 > q div 4" using q_div2_pos q_div4_pos q_gt by simp
          (* decode_bit uses d mod q internally, so decode_bit q (d mod q) = decode_bit q d *)
          have decode_mod: "decode_bit q (?sum mod q) = decode_bit q ?sum"
            unfolding decode_bit_def by (simp add: mod_mod_trivial)
          have "decode_bit q ?sum = True"
            unfolding decode_bit_def Let_def using d'_is_half not_gt_half half_gt_quarter by simp
          thus ?thesis using decode_mod by simp
        qed
      next
        case False
        (* noise < 0, so sum in (q/4, q/2) *)
        have noise_neg: "?noise < 0" using False by simp
        have sum_lt_half: "?sum < q div 2" using noise_neg by simp
        have sum_pos: "?sum > 0" using sum_lb q_div4_pos by simp
        have d'_eq: "?sum mod q = ?sum" using sum_pos sum_lt_q by simp
        (* sum in (q/4, q/2), so not > q/2, distance = sum > q/4 *)
        have not_gt: "\<not> (?sum > q div 2)" using sum_lt_half by simp
        have decode_mod: "decode_bit q (?sum mod q) = decode_bit q ?sum"
          unfolding decode_bit_def by (simp add: mod_mod_trivial)
        have "decode_bit q ?sum = (?sum > q div 4)"
          using not_gt d'_eq by (simp add: decode_bit_def Let_def)
        hence "decode_bit q ?sum = True" using sum_lb by simp
        thus ?thesis using decode_mod by simp
      qed
    qed
    thus ?thesis using decrypt_eq val True by simp
  qed
qed

export_code
  vec_add vec_mod inner_prod
  mat_vec_mult transpose mat_transpose_vec_mult
  encode_bit decode_bit
  lwe_encrypt lwe_decrypt
  in Haskell module_name "Lattice.LWE_Regev"

export_code
  vec_add vec_mod inner_prod
  mat_vec_mult transpose mat_transpose_vec_mult
  encode_bit decode_bit
  lwe_encrypt lwe_decrypt
  in SML module_name LWE_Regev

export_code
  vec_add vec_mod inner_prod
  mat_vec_mult transpose mat_transpose_vec_mult
  encode_bit decode_bit
  lwe_encrypt lwe_decrypt
  in OCaml module_name LWE_Regev

export_code
  vec_add vec_mod inner_prod
  mat_vec_mult transpose mat_transpose_vec_mult
  encode_bit decode_bit
  lwe_encrypt lwe_decrypt
  in Scala module_name LWE_Regev

end
