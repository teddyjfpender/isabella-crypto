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

lemma inner_prod_nth_min:
  "inner_prod u v = (\<Sum>i = 0 ..< min (length u) (length v). u ! i * v ! i)"
proof -
  have "inner_prod u v = sum_list (map2 (*) u v)"
    by (simp add: inner_prod_def)
  also have "... = (\<Sum>i = 0 ..< length (map2 (*) u v). (map2 (*) u v) ! i)"
    by (simp add: sum_list_sum_nth)
  also have "... = (\<Sum>i = 0 ..< min (length u) (length v). u ! i * v ! i)"
  proof (intro sum.cong refl)
    fix i assume i_lt: "i < min (length u) (length v)"
    then have iu: "i < length u" and iv: "i < length v"
      by simp_all
    show "(map2 (*) u v) ! i = u ! i * v ! i"
      using iu iv by (simp add: nth_zip)
  qed
  finally show ?thesis .
qed

lemma foldr_max_const:
  assumes "xs \<noteq> []" "\<forall>x \<in> set xs. length x = n"
  shows "foldr (\<lambda>x. max (length x)) xs 0 = n"
using assms
proof (induct xs)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  have len_x: "length x = n" using Cons.prems by simp
  have rows_xs: "\<forall>x \<in> set xs. length x = n" using Cons.prems by simp
  have ih: "xs \<noteq> [] \<Longrightarrow> foldr (\<lambda>x. max (length x)) xs 0 = n"
    using Cons.hyps rows_xs by simp
  show ?case
  proof (cases xs)
    case Nil
    then show ?thesis using len_x by simp
  next
    case Cons_xs: (Cons y ys)
    have ih': "foldr (\<lambda>x. max (length x)) xs 0 = n"
      using ih Cons_xs by simp
    show ?thesis using len_x ih' by simp
  qed
qed

lemma length_transpose_valid_matrix:
  fixes A :: "int_matrix"
  assumes A_ok: "valid_matrix A m n" and m_pos: "m > 0"
  shows "length (transpose A) = n"
proof -
  have len_A: "length A = m" and rows: "\<forall>row \<in> set A. length row = n"
    using A_ok by (simp_all add: valid_matrix_def)
  have A_ne: "A \<noteq> []"
  proof
    assume "A = []"
    hence "length A = 0" by simp
    with len_A have "m = 0" by simp
    with m_pos show False by simp
  qed
  have "length (transpose A) = foldr (\<lambda>xs. max (length xs)) A 0"
    by (simp add: length_transpose)
  also have "... = n" using foldr_max_const[OF A_ne rows] .
  finally show ?thesis .
qed

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

locale lwe_dims =
  fixes A :: int_matrix and s r e :: int_vec and m n :: nat
  assumes A_ok: "valid_matrix A m n"
    and s_ok: "valid_vec s n"
    and r_ok: "valid_vec r m"
    and e_ok: "valid_vec e m"
    and m_pos: "m > 0"
begin

lemma len_A: "length A = m"
  using A_ok by (simp add: valid_matrix_def)

lemma len_s: "length s = n"
  using s_ok by (simp add: valid_vec_def)

lemma len_r: "length r = m"
  using r_ok by (simp add: valid_vec_def)

lemma len_e: "length e = m"
  using e_ok by (simp add: valid_vec_def)

lemma len_rows: "row \<in> set A \<Longrightarrow> length row = n"
  using A_ok by (simp add: valid_matrix_def)

lemma len_As: "length (mat_vec_mult A s) = m"
  using len_A by (simp add: mat_vec_mult_length)

lemma len_At: "length (mat_transpose_vec_mult A r) = n"
  using length_transpose_valid_matrix[OF A_ok m_pos]
  by (simp add: mat_transpose_vec_mult_def mat_vec_mult_length)

lemma transpose_nth:
  assumes j_lt: "j < n"
  shows "transpose A ! j = map (\<lambda>row. row ! j) A"
proof -
  have len_T: "length (transpose A) = n"
    using length_transpose_valid_matrix[OF A_ok m_pos] .
  have j_T: "j < length (transpose A)" using j_lt len_T by simp
  have all_rows: "\<forall>row \<in> set A. j < length row"
    using len_rows j_lt by auto
  have filt: "filter (\<lambda>ys. j < length ys) A = A"
    using all_rows by (simp add: filter_True)
  show ?thesis using nth_transpose[OF j_T]
    by (simp add: filt)
qed

lemma inner_prod_col:
  assumes j_lt: "j < n"
  shows "inner_prod (map (\<lambda>row. row ! j) A) r =
         (\<Sum>i = 0 ..< m. (A ! i) ! j * r ! i)"
proof -
  have len_map: "length (map (\<lambda>row. row ! j) A) = m"
    using len_A by simp
  have "inner_prod (map (\<lambda>row. row ! j) A) r =
        (\<Sum>i = 0 ..< min (length (map (\<lambda>row. row ! j) A)) (length r).
           (map (\<lambda>row. row ! j) A) ! i * r ! i)"
    by (simp add: inner_prod_nth_min)
  also have "... = (\<Sum>i = 0 ..< m. (map (\<lambda>row. row ! j) A) ! i * r ! i)"
    using len_map len_r by (intro sum.cong refl) simp
  also have "... = (\<Sum>i = 0 ..< m. (A ! i) ! j * r ! i)"
    using len_A by (intro sum.cong refl) simp
  finally show ?thesis .
qed

lemma inner_prod_row:
  assumes i_lt: "i < m"
  shows "inner_prod (A ! i) s =
         (\<Sum>j = 0 ..< n. (A ! i) ! j * s ! j)"
proof -
  have i_ltA: "i < length A" using i_lt len_A by simp
  have row_mem: "A ! i \<in> set A" using i_ltA by (simp add: nth_mem)
  have row_len: "length (A ! i) = n"
    using len_rows row_mem by simp
  have "inner_prod (A ! i) s =
        (\<Sum>j = 0 ..< min (length (A ! i)) (length s). (A ! i) ! j * s ! j)"
    by (simp add: inner_prod_nth_min)
  also have "... = (\<Sum>j = 0 ..< n. (A ! i) ! j * s ! j)"
    using row_len len_s by (simp add: min_def)
  finally show ?thesis .
qed

lemma iprod_transpose:
  "inner_prod s (mat_transpose_vec_mult A r) =
   inner_prod (mat_vec_mult A s) r"
proof -
  have lhs:
    "inner_prod s (mat_transpose_vec_mult A r) =
     (\<Sum>j = 0 ..< n. s ! j * (\<Sum>i = 0 ..< m. (A ! i) ! j * r ! i))"
  proof -
    have "inner_prod s (mat_transpose_vec_mult A r) =
          (\<Sum>j = 0 ..< min (length s) (length (mat_transpose_vec_mult A r)).
             s ! j * (mat_transpose_vec_mult A r) ! j)"
      by (simp add: inner_prod_nth_min)
    also have "... = (\<Sum>j = 0 ..< n. s ! j * (mat_transpose_vec_mult A r) ! j)"
      using len_s len_At by simp
    also have "... = (\<Sum>j = 0 ..< n. s ! j * inner_prod (transpose A ! j) r)"
      using len_At by (intro sum.cong refl) (simp add: mat_transpose_vec_mult_def mat_vec_mult_def)
    also have "... = (\<Sum>j = 0 ..< n. s ! j * inner_prod (map (\<lambda>row. row ! j) A) r)"
      using transpose_nth by (intro sum.cong refl) simp
    also have "... = (\<Sum>j = 0 ..< n. s ! j * (\<Sum>i = 0 ..< m. (A ! i) ! j * r ! i))"
      using inner_prod_col by (intro sum.cong refl) simp
    finally show ?thesis .
  qed
  have rhs:
    "inner_prod (mat_vec_mult A s) r =
     (\<Sum>i = 0 ..< m. r ! i * (\<Sum>j = 0 ..< n. (A ! i) ! j * s ! j))"
  proof -
    have "inner_prod (mat_vec_mult A s) r =
          (\<Sum>i = 0 ..< min (length (mat_vec_mult A s)) (length r).
             (mat_vec_mult A s) ! i * r ! i)"
      by (simp add: inner_prod_nth_min)
    also have "... = (\<Sum>i = 0 ..< m. (mat_vec_mult A s) ! i * r ! i)"
      using len_As len_r by simp
    also have "... = (\<Sum>i = 0 ..< m. inner_prod (A ! i) s * r ! i)"
      using len_As by (intro sum.cong refl) (simp add: mat_vec_mult_def)
    also have "... = (\<Sum>i = 0 ..< m. r ! i * inner_prod (A ! i) s)"
      by (intro sum.cong refl) (simp add: algebra_simps)
    also have "... = (\<Sum>i = 0 ..< m. r ! i * (\<Sum>j = 0 ..< n. (A ! i) ! j * s ! j))"
      using inner_prod_row by (intro sum.cong refl) simp
    finally show ?thesis .
  qed
  have swap:
    "(\<Sum>j = 0 ..< n. s ! j * (\<Sum>i = 0 ..< m. (A ! i) ! j * r ! i)) =
     (\<Sum>i = 0 ..< m. r ! i * (\<Sum>j = 0 ..< n. (A ! i) ! j * s ! j))"
  proof -
    have step1:
      "(\<Sum>j = 0 ..< n. s ! j * (\<Sum>i = 0 ..< m. (A ! i) ! j * r ! i)) =
       (\<Sum>j = 0 ..< n. \<Sum>i = 0 ..< m. s ! j * ((A ! i) ! j * r ! i))"
      by (simp add: sum_distrib_left[symmetric])
    have step2:
      "... = (\<Sum>i = 0 ..< m. \<Sum>j = 0 ..< n. s ! j * ((A ! i) ! j * r ! i))"
      by (simp add: sum.swap)
    have step3:
      "... = (\<Sum>i = 0 ..< m. \<Sum>j = 0 ..< n. r ! i * ((A ! i) ! j * s ! j))"
      by (simp add: algebra_simps)
    have step4:
      "... = (\<Sum>i = 0 ..< m. r ! i * (\<Sum>j = 0 ..< n. (A ! i) ! j * s ! j))"
      by (simp add: sum_distrib_left)
    show ?thesis using step1 step2 step3 step4 by simp
  qed
  show ?thesis using lhs rhs swap by simp
qed

end

(* ========== Encoding/Decoding ========== *)

definition encode_bit :: "int => bool => int" where
  "encode_bit q b = (if b then q div 2 else 0)"

(* Distance from 0 in Z_q (centered representation).
   This computes min(d mod q, q - (d mod q)), i.e., the distance to the nearest
   representative of 0 in the centered range (-q/2, q/2]. *)
definition dist0 :: "int => int => int" where
  "dist0 q d = (let d' = d mod q in if d' > q div 2 then q - d' else d')"

(* Decodes a ciphertext value to a bit based on distance from 0 vs q/2.
   Returns True if closer to q/2 (distance > q/4). *)
definition decode_bit :: "int => int => bool" where
  "decode_bit q d = (dist0 q d > q div 4)"

lemma dist0_alt: "dist0 q d = (let d' = d mod q in if d' > q div 2 then q - d' else d')"
  by (simp add: dist0_def)

lemma decode_bit_alt: "decode_bit q d =
  (let d' = d mod q in (if d' > q div 2 then q - d' else d') > q div 4)"
  unfolding decode_bit_def dist0_def Let_def by simp

lemma dist0_mod: "dist0 q (d mod q) = dist0 q d"
  unfolding dist0_def Let_def by (simp add: mod_mod_trivial)

lemma decode_bit_mod: "decode_bit q (d mod q) = decode_bit q d"
  unfolding decode_bit_def using dist0_mod by simp

lemma div4_le_div2:
  fixes q :: int
  assumes "q >= 0"
  shows "q div 4 <= q div 2"
  using zdiv_mono2[of q 4 2] assms by simp

lemma even_div2_add:
  fixes q :: int
  assumes "q mod 2 = 0"
  shows "q div 2 + q div 2 = q"
proof -
  have "q div 2 * 2 + q mod 2 = q"
    by (simp add: div_mult_mod_eq)
  hence "q div 2 * 2 = q" using assms by simp
  thus ?thesis by (simp add: algebra_simps)
qed

lemma even_div2_sub:
  fixes q :: int
  assumes "q mod 2 = 0"
  shows "q - q div 2 = q div 2"
  using even_div2_add[OF assms] by simp

lemma mod2_from_mod4:
  fixes q :: int
  assumes "q mod 4 = 0"
  shows "q mod 2 = 0"
proof -
  have "4 dvd q" using assms by (simp add: mod_eq_0_iff_dvd)
  hence "2 dvd q" using dvd_trans[of 2 4 q] by simp
  thus ?thesis by (simp add: mod_eq_0_iff_dvd)
qed

lemma div2_eq_double_div4:
  fixes q :: int
  assumes "q mod 4 = 0"
  shows "q div 2 = 2 * (q div 4)"
proof -
  obtain k where k_def: "q = 4 * k"
    using assms by (auto simp: mod_eq_0_iff_dvd dvd_def)
  have "q div 2 = (4 * k) div 2" using k_def by simp
  also have "... = 2 * k" by simp
  also have "... = 2 * (q div 4)" using k_def by simp
  finally show ?thesis .
qed

lemma dist0_small:
  fixes q x :: int
  assumes q_pos: "q > 0"
    and bound: "\<bar>x\<bar> < q div 4"
  shows "dist0 q x = \<bar>x\<bar>"
proof (cases "x >= 0")
  case True
  have x_lt: "x < q div 4" using bound True by simp
  have x_lt_q: "x < q"
    using x_lt q_pos by simp
  have mod_x: "x mod q = x"
    using True x_lt_q by simp
  have x_lt_half: "x < q div 2"
  proof -
    have "q div 4 <= q div 2" using div4_le_div2[of q] q_pos by simp
    with x_lt show ?thesis by linarith
  qed
  have not_gt: "\<not> (x mod q > q div 2)"
    using mod_x x_lt_half by simp
  show ?thesis
    unfolding dist0_def Let_def using mod_x not_gt True by simp
next
  case False
  have x_neg: "x < 0" using False by simp
  have x_gt: "x > - (q div 4)" using bound by simp
  have x_gt_neg_q: "x > - q" using x_gt q_pos by simp
  have sum_nonneg: "x + q >= 0" using x_gt_neg_q by simp
  have sum_lt_q: "x + q < q" using x_neg by simp
  have mod_x: "x mod q = x + q"
    using sum_nonneg sum_lt_q q_pos
    by (metis add.commute mod_add_self2 mod_pos_pos_trivial)
  have d'_gt: "x + q > q div 2"
  proof -
    have "q - q div 4 >= q div 2" using q_pos by simp
    moreover have "x + q > q - q div 4" using x_gt by simp
    ultimately show ?thesis by simp
  qed
  have "dist0 q x = q - (x + q)"
    unfolding dist0_def Let_def using mod_x d'_gt by simp
  also have "... = -x" by simp
  finally show ?thesis using x_neg by simp
qed

lemma dist0_small_lt:
  fixes q x :: int
  assumes q_pos: "q > 0"
    and bound: "\<bar>x\<bar> < q div 4"
  shows "dist0 q x < q div 4"
  using dist0_small[OF q_pos bound] bound by simp

lemma dist0_half_shift:
  fixes q x :: int
  assumes q_pos: "q > 0"
    and q_even: "q mod 2 = 0"
    and bound: "\<bar>x\<bar> < q div 4"
  shows "dist0 q (x + q div 2) = q div 2 - \<bar>x\<bar>"
proof (cases "x >= 0")
  case True
  have x_lt: "x < q div 4" using bound True by simp
  have div4_le_half: "q div 4 <= q div 2"
    using div4_le_div2[of q] q_pos by simp
  have sum_pos: "0 <= x + q div 2"
    using True by simp
  have sum_lt_q: "x + q div 2 < q"
  proof -
    have "x + q div 2 < q div 2 + q div 2"
      using x_lt div4_le_half by linarith
    also have "... = q" using even_div2_add[OF q_even] by simp
    finally show ?thesis .
  qed
  have mod_sum: "(x + q div 2) mod q = x + q div 2"
    using sum_pos sum_lt_q by simp
  have "dist0 q (x + q div 2) =
        (if x > 0 then q - (x + q div 2) else x + q div 2)"
    unfolding dist0_def Let_def using mod_sum by simp
  then show ?thesis
  proof (cases "x > 0")
    case True
    have "dist0 q (x + q div 2) = q - (x + q div 2)"
      using True by simp
    also have "... = q div 2 - x"
      using even_div2_sub[OF q_even] by (simp add: algebra_simps)
    finally show ?thesis using True by simp
  next
    case False
    have x_eq: "x = 0" using True False by simp
    have "dist0 q (x + q div 2) = x + q div 2"
      using False by simp
    also have "... = q div 2 - \<bar>x\<bar>" using x_eq by simp
    finally show ?thesis .
  qed
next
  case False
  have x_neg: "x < 0" using False by simp
  have x_gt: "x > - (q div 4)" using bound by simp
  have div4_le_half: "q div 4 <= q div 2"
    using div4_le_div2[of q] q_pos by simp
  have sum_pos: "0 <= x + q div 2"
  proof -
    have "x + q div 2 > - (q div 4) + q div 2" using x_gt by simp
    also have "... >= 0" using div4_le_half by simp
    finally show ?thesis by simp
  qed
  have sum_lt_half: "x + q div 2 < q div 2" using x_neg by simp
  have sum_lt_q: "x + q div 2 < q" using sum_lt_half q_pos by simp
  have mod_sum: "(x + q div 2) mod q = x + q div 2"
    using sum_pos sum_lt_q by simp
  have "dist0 q (x + q div 2) = x + q div 2"
    unfolding dist0_def Let_def using mod_sum sum_lt_half by simp
  also have "... = q div 2 - \<bar>x\<bar>"
    using x_neg by simp
  finally show ?thesis .
qed

lemma decode_bit_small:
  fixes q x :: int
  assumes q_pos: "q > 0"
    and bound: "\<bar>x\<bar> < q div 4"
  shows "decode_bit q x = False"
  using dist0_small_lt[OF q_pos bound] by (simp add: decode_bit_def)

lemma decode_bit_half_shift:
  fixes q x :: int
  assumes q_pos: "q > 0"
    and q_mod4: "q mod 4 = 0"
    and bound: "\<bar>x\<bar> < q div 4"
  shows "decode_bit q (x + q div 2) = True"
proof -
  have q_even: "q mod 2 = 0" using mod2_from_mod4[OF q_mod4] .
  have dist_eq: "dist0 q (x + q div 2) = q div 2 - \<bar>x\<bar>"
    using dist0_half_shift[OF q_pos q_even bound] .
  have "dist0 q (x + q div 2) > q div 4"
    using dist_eq div2_eq_double_div4[OF q_mod4] bound by linarith
  thus ?thesis by (simp add: decode_bit_def)
qed

lemma dist0_zero:
  fixes q :: int
  assumes "q > 0"
  shows "dist0 q 0 = 0"
  unfolding dist0_def using assms by simp

lemma dist0_half:
  fixes q :: int
  assumes "q > 0"
  shows "dist0 q (q div 2) = q div 2"
proof -
  have half_pos: "q div 2 >= 0" using assms by simp
  have half_lt_q: "q div 2 < q" using assms by simp
  have mod_half: "(q div 2) mod q = q div 2"
    using half_pos half_lt_q by simp
  have not_gt: "\<not> (q div 2 > q div 2)" by simp
  show ?thesis unfolding dist0_def Let_def using mod_half not_gt by simp
qed

lemma encode_decode_inverse:
  fixes q :: int
  assumes "q > 2"
  shows "decode_bit q (encode_bit q b) = b"
proof (cases b)
  case True
  have q_pos: "q > 0" using assms by arith
  have quarter_lt_half: "q div 4 < q div 2"
    using assms by (simp add: zdiv_mono2)
  have "dist0 q (q div 2) = q div 2"
    using dist0_half[OF q_pos] .
  then have "decode_bit q (q div 2) = (q div 2 > q div 4)"
    unfolding decode_bit_def by simp
  then show ?thesis
    using True quarter_lt_half by (simp add: encode_bit_def)
next
  case False
  have q_pos: "q > 0" using assms by arith
  have "dist0 q 0 = 0" using dist0_zero[OF q_pos] .
  then have "decode_bit q 0 = False"
    unfolding decode_bit_def using q_pos by simp
  then show ?thesis
    using False by (simp add: encode_bit_def)
qed

(* Modular arithmetic helpers *)
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

(* ========== Transpose Identity ========== *)
(* The inner product transpose identity <s, A^T r> = <As, r> is proved in locale
   lwe_dims using nth_transpose and sum.swap, with explicit dimension constraints
   coming from valid_matrix / valid_vec. *)

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
    and A_ok: "valid_matrix (pk_A pk) m_dim n"
    and s_ok: "valid_vec (sk_s sk) n"
    and r_ok: "valid_vec r m_dim"
    and e_ok: "valid_vec e m_dim"
    and m_pos: "m_dim > 0"
    and b_def: "pk_b pk = vec_mod (vec_add (mat_vec_mult (pk_A pk) (sk_s sk)) e) q"
  shows "(ct_v (lwe_encrypt pk q r m) -
          inner_prod (sk_s sk) (ct_u (lwe_encrypt pk q r m))) mod q =
         (inner_prod e r + encode_bit q m) mod q"
proof -
  interpret dims: lwe_dims "pk_A pk" "sk_s sk" r e m_dim n
    by (unfold_locales) (simp add: A_ok s_ok r_ok e_ok m_pos)
  let ?As = "mat_vec_mult (pk_A pk) (sk_s sk)"
  have len_e: "length ?As = length e"
    using dims.len_As dims.len_e by simp
  have len_r: "length r = length ?As"
    using dims.len_r dims.len_As by simp
  have len_b: "length (pk_b pk) = length r"
    using b_def dims.len_As dims.len_e dims.len_r
    by (simp add: vec_add_length vec_mod_length)
  have len_sk: "length (mat_transpose_vec_mult (pk_A pk) r) = length (sk_s sk)"
    using dims.len_At dims.len_s by simp
  have iprod: "inner_prod (sk_s sk) (mat_transpose_vec_mult (pk_A pk) r) =
               inner_prod (mat_vec_mult (pk_A pk) (sk_s sk)) r"
    using dims.iprod_transpose by simp
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
  assumes q_pos: "q > 0"
    and q_mod4: "q mod 4 = 0"
    and A_ok: "valid_matrix (pk_A pk) m_dim n"
    and s_ok: "valid_vec (sk_s sk) n"
    and r_ok: "valid_vec r m_dim"
    and e_ok: "valid_vec e m_dim"
    and m_pos: "m_dim > 0"
    and b_def: "pk_b pk = vec_mod (vec_add (mat_vec_mult (pk_A pk) (sk_s sk)) e) q"
    and error_bound: "\<bar>inner_prod e r\<bar> < q div 4"
  shows "lwe_decrypt sk q (lwe_encrypt pk q r m) = m"
proof -
  let ?noise = "inner_prod e r"
  have d_eq:
    "(ct_v (lwe_encrypt pk q r m) -
      inner_prod (sk_s sk) (ct_u (lwe_encrypt pk q r m))) mod q =
     (?noise + encode_bit q m) mod q"
    using decryption_error_term[OF q_pos A_ok s_ok r_ok e_ok m_pos b_def] .
  have decrypt_eq:
    "lwe_decrypt sk q (lwe_encrypt pk q r m) =
     decode_bit q ((?noise + encode_bit q m) mod q)"
    using d_eq by (simp add: lwe_decrypt_def)
  show ?thesis
  proof (cases m)
    case False
    have enc_false: "encode_bit q False = 0" by (simp add: encode_bit_def)
    have "decode_bit q ((?noise + encode_bit q m) mod q) = decode_bit q ?noise"
      using False enc_false by (simp add: decode_bit_mod)
    also have "... = False"
      using decode_bit_small[OF q_pos error_bound] by simp
    finally show ?thesis using decrypt_eq False by simp
  next
    case True
    have enc_true: "encode_bit q True = q div 2" by (simp add: encode_bit_def)
    have "decode_bit q ((?noise + encode_bit q m) mod q) =
          decode_bit q (?noise + q div 2)"
      using True enc_true by (simp add: decode_bit_mod)
    also have "... = True"
      using decode_bit_half_shift[OF q_pos q_mod4 error_bound] by simp
    finally show ?thesis using decrypt_eq True by simp
  qed
qed

export_code
  vec_add vec_mod inner_prod
  mat_vec_mult transpose mat_transpose_vec_mult
  encode_bit decode_bit dist0
  lwe_encrypt lwe_decrypt
  in Haskell module_name "Lattice.LWE_Regev"

export_code
  vec_add vec_mod inner_prod
  mat_vec_mult transpose mat_transpose_vec_mult
  encode_bit decode_bit dist0
  lwe_encrypt lwe_decrypt
  in SML module_name LWE_Regev

export_code
  vec_add vec_mod inner_prod
  mat_vec_mult transpose mat_transpose_vec_mult
  encode_bit decode_bit dist0
  lwe_encrypt lwe_decrypt
  in OCaml module_name LWE_Regev

export_code
  vec_add vec_mod inner_prod
  mat_vec_mult transpose mat_transpose_vec_mult
  encode_bit decode_bit dist0
  lwe_encrypt lwe_decrypt
  in Scala module_name LWE_Regev

end
