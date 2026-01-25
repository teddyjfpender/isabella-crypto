theory Zq
  imports "../Prelude" "../Linear/ListVec"
begin

(* Modular arithmetic over Z_q for lattice cryptography *)

(* Centered modular reduction lemmas *)
lemma mod_centered_cong [mod_simp]:
  assumes "(q::int) > 0" shows "mod_centered x q mod q = x mod q"
proof (cases "x mod q > q div 2")
  case True
  have "mod_centered x q = x mod q - q" unfolding mod_centered_def Let_def using True by simp
  hence "mod_centered x q mod q = (x mod q - q) mod q" by simp
  also have "(x mod q - q) mod q = x mod q"
  proof -
    have "(x mod q - q) mod q = (x mod q + (-1) * q) mod q" by simp
    also have "... = x mod q mod q" using assms by (simp add: mod_mult_self2)
    also have "... = x mod q" by simp finally show ?thesis . qed
  finally show ?thesis . next
  case False then show ?thesis unfolding mod_centered_def Let_def by simp qed

lemma mod_centered_zero [mod_simp]: "(q::int) > 0 \<Longrightarrow> mod_centered 0 q = 0"
  unfolding mod_centered_def Let_def by simp

lemma mod_centered_abs_bound:
  assumes "(q::int) > 0" shows "abs (mod_centered x q) <= q div 2"
proof (cases "x mod q > q div 2")
  case True
  have mc: "mod_centered x q = x mod q - q" unfolding mod_centered_def Let_def using True by simp
  have "x mod q < q" using assms by simp hence "x mod q - q < 0" by arith
  hence neg: "mod_centered x q < 0" using mc by simp
  have "x mod q - q > -(q div 2 + 1)"
  proof - have "q div 2 - q >= -(q div 2 + 1)" by (simp add: div_plus_div_distrib_dvd_left)
    thus ?thesis using True by arith qed
  hence "mod_centered x q > -(q div 2 + 1)" using mc by simp
  hence "-(mod_centered x q) < q div 2 + 1" by arith
  hence "-(mod_centered x q) <= q div 2" by arith thus ?thesis using neg by simp
next case False
  have mc: "mod_centered x q = x mod q" unfolding mod_centered_def Let_def using False by simp
  have "x mod q >= 0" using assms by simp hence "mod_centered x q >= 0" using mc by simp
  moreover have "mod_centered x q <= q div 2" using mc False by simp
  ultimately show ?thesis by simp qed

(* Vector modular operations *)
definition vec_mod :: "int_vec => int => int_vec" where "vec_mod v q = map (\<lambda>x. x mod q) v"
definition vec_mod_centered :: "int_vec => int => int_vec" where "vec_mod_centered v q = map (\<lambda>x. mod_centered x q) v"
lemma vec_mod_length [dim_simp]: "length (vec_mod v q) = length v" unfolding vec_mod_def by simp
lemma vec_mod_centered_length [dim_simp]: "length (vec_mod_centered v q) = length v" unfolding vec_mod_centered_def by simp
lemma vec_mod_nth: "i < length v \<Longrightarrow> (vec_mod v q) ! i = (v ! i) mod q" unfolding vec_mod_def by simp
lemma vec_mod_idemp [mod_simp]: "(q::int) > 0 \<Longrightarrow> vec_mod (vec_mod v q) q = vec_mod v q" unfolding vec_mod_def by (simp add: map_map comp_def)

(* Distance to zero in Z_q *)
definition dist0 :: "int => int => int" where "dist0 q x = abs (mod_centered x q)"
lemma dist0_nonneg [dist_simp]: "dist0 q x >= 0" unfolding dist0_def by simp
lemma dist0_bound [dist_simp]: "(q::int) > 0 \<Longrightarrow> dist0 q x <= q div 2" unfolding dist0_def using mod_centered_abs_bound by simp
lemma dist0_zero [dist_simp]: "(q::int) > 0 \<Longrightarrow> dist0 q 0 = 0" unfolding dist0_def mod_centered_zero by simp
lemma dist0_mod [dist_simp]: "(q::int) > 0 \<Longrightarrow> dist0 q (x mod q) = dist0 q x" unfolding dist0_def mod_centered_def Let_def by simp

lemma neg_mod_eq: assumes "(q::int) > 0" "x < 0" "x > -q" shows "x mod q = x + q"
proof -
  have h1: "(0::int) <= x + q" using assms by arith have h2: "x + q < q" using assms by arith
  have xpq: "(x + q) mod q = x + q" using mod_pos_pos_trivial[OF h1 h2] by simp
  have "(x + q) mod q = x mod q" by simp thus ?thesis using xpq by simp qed

lemma dist0_small:
  assumes q_pos: "(q::int) > 0" assumes x_small: "abs x < q div 2" shows "dist0 q x = abs x"
proof (cases "x >= 0")
  case True hence x_eq: "x mod q = x" using x_small q_pos by simp
  have x_le: "x <= q div 2" using x_small True by arith hence not_gt: "\<not> (x mod q > q div 2)" using x_eq by arith
  have "mod_centered x q = x mod q" unfolding mod_centered_def Let_def using not_gt by simp
  hence "mod_centered x q = x" using x_eq by simp thus ?thesis unfolding dist0_def using True by simp
next case False hence x_neg: "x < 0" by simp
  have x_bound: "x > -q div 2" using x_small by arith hence x_gt_negq: "x > -q" using q_pos by arith
  have xmod_eq: "x mod q = x + q" by (rule neg_mod_eq[OF q_pos x_neg x_gt_negq])
  have "x + q > q div 2" proof - have "x > -q div 2" using x_small by arith thus ?thesis by arith qed
  hence gt_half: "x mod q > q div 2" using xmod_eq by simp
  have "mod_centered x q = x mod q - q" unfolding mod_centered_def Let_def using gt_half by simp
  hence mc_eq: "mod_centered x q = x" using xmod_eq by simp
  have "abs x = -x" using x_neg by simp thus ?thesis unfolding dist0_def mc_eq using x_neg by simp qed

(* Bit encoding/decoding for LWE *)
definition encode_bit :: "int => bool => int" where "encode_bit q b = (if b then q div 2 else 0)"
definition decode_bit :: "int => int => bool" where "decode_bit q x = (dist0 q x > q div 4)"
lemma encode_bit_False: "encode_bit q False = 0" unfolding encode_bit_def by simp
lemma encode_bit_True: "encode_bit q True = q div 2" unfolding encode_bit_def by simp

lemma encode_decode_inverse: assumes q_gt: "(q::int) > 2" shows "decode_bit q (encode_bit q b) = b"
proof (cases b)
  case False have enc: "encode_bit q False = 0" by (simp add: encode_bit_def)
  have "dist0 q 0 = 0" unfolding dist0_def mod_centered_def Let_def using q_gt by simp
  hence "dist0 q (encode_bit q False) = 0" using enc by simp
  moreover have "q div 4 >= 0" using q_gt by simp
  ultimately have "\<not> (dist0 q (encode_bit q False) > q div 4)" by arith
  thus ?thesis unfolding decode_bit_def using False by simp
next case True have enc: "encode_bit q True = q div 2" by (simp add: encode_bit_def)
  have q2_pos: "q div 2 > 0" using q_gt by arith
  have half_mod: "(q div 2) mod q = q div 2" using q_gt q2_pos by simp
  have not_gt: "\<not> ((q div 2) mod q > q div 2)" using half_mod by simp
  have "mod_centered (q div 2) q = (q div 2) mod q" unfolding mod_centered_def Let_def using not_gt by simp
  hence mc_eq: "mod_centered (q div 2) q = q div 2" using half_mod by simp
  have "dist0 q (q div 2) = q div 2" unfolding dist0_def mc_eq using q2_pos by simp
  hence "dist0 q (encode_bit q True) = q div 2" using enc by simp
  moreover have "q div 2 > q div 4" using q_gt by arith
  ultimately have "dist0 q (encode_bit q True) > q div 4" by arith
  thus ?thesis unfolding decode_bit_def using True by simp qed

lemma decode_bit_small: assumes q_pos: "(q::int) > 0" assumes x_small: "abs x < q div 4" shows "decode_bit q x = False"
proof -
  have q4_le_q2: "q div 4 <= q div 2" using q_pos by arith
  have x_lt_half: "abs x < q div 2" using x_small q4_le_q2 by arith
  have "dist0 q x = abs x" by (rule dist0_small[OF q_pos x_lt_half])
  hence "dist0 q x < q div 4" using x_small by simp
  thus ?thesis unfolding decode_bit_def by arith qed

(* Decoding with noise: if noise is small, encoded bit can be recovered *)
lemma decode_bit_half_shift:
  fixes q x :: int
  assumes q_pos: "q > 0"
  assumes q_div4: "q mod 4 = 0"
  assumes x_small: "abs x < q div 4"
  shows "decode_bit q (x + q div 2) = True"
proof -
  have dvd4: "4 dvd q"
    using q_div4 by auto

  obtain k where qk: "q = 4 * k"
    using dvd4 by (elim dvdE)

  have k_pos: "k > 0"
    using q_pos qk by linarith

  have q4_pos: "q div 4 > 0"
    using k_pos by (simp add: qk)

  have q2_eq: "q div 2 = 2 * (q div 4)"
    by (simp add: qk)

  have q_eq: "q = 4 * (q div 4)"
    by (simp add: qk)

  have x_lt: "x < q div 4" and x_gt: "x > - (q div 4)"
    using x_small by (simp_all add: abs_less_iff)

  have in_range: "x + q div 2 >= 0 \<and> x + q div 2 < q"
  proof
    have "x + q div 2 > - (q div 4) + 2 * (q div 4)"
      using x_gt q2_eq by linarith
    hence "x + q div 2 > q div 4"
      by simp
    thus "x + q div 2 >= 0"
      using q4_pos by linarith
  next
    have "x + q div 2 < (q div 4) + 2 * (q div 4)"
      using x_lt q2_eq by linarith
    hence upper: "x + q div 2 < 3 * (q div 4)"
      by simp
    have "3 * (q div 4) < 4 * (q div 4)"
      using q4_pos by linarith
    thus "x + q div 2 < q"
      using upper q_eq by linarith
  qed

  have xmod_eq: "(x + q div 2) mod q = x + q div 2"
    using in_range q_pos by simp

  show ?thesis
  proof (cases "x > 0")
    case True
    have gt_half: "x + q div 2 > q div 2"
      using True by linarith
    hence gt_half': "(x + q div 2) mod q > q div 2"
      using xmod_eq by simp

    have mc_eq: "mod_centered (x + q div 2) q = (x + q div 2) mod q - q"
      unfolding mod_centered_def Let_def using gt_half' by simp
    hence mc_val: "mod_centered (x + q div 2) q = x + q div 2 - q"
      using xmod_eq by simp

    have q_minus_half: "q - q div 2 = q div 2"
      by (simp add: qk)
    have mc_val': "mod_centered (x + q div 2) q = x - q div 2"
      using mc_val q_minus_half by simp

    have mc_neg: "x - q div 2 < 0"
    proof -
      have "q div 4 - 2 * (q div 4) = - (q div 4)" by simp
      hence half_diff: "q div 4 - q div 2 = - (q div 4)"
        using q2_eq by simp
      have "x - q div 2 < q div 4 - q div 2"
        using x_lt by linarith
      hence "x - q div 2 < - (q div 4)"
        using half_diff by simp
      thus ?thesis
        using q4_pos by linarith
    qed

    have dist_eq: "dist0 q (x + q div 2) = q div 2 - x"
      unfolding dist0_def using mc_val' mc_neg by simp

    have gt_q4: "q div 2 - x > q div 4"
      using x_lt q2_eq by linarith

    show ?thesis
      unfolding decode_bit_def
      using dist_eq gt_q4 by simp

  next
    case False
    have x_le0: "x <= 0" using False by simp

    have le_half: "x + q div 2 <= q div 2"
      using x_le0 by linarith
    have le_half': "(x + q div 2) mod q <= q div 2"
      using xmod_eq le_half by simp

    have not_gt: "\<not> ((x + q div 2) mod q > q div 2)"
      using le_half' by linarith

    have mc_eq: "mod_centered (x + q div 2) q = (x + q div 2) mod q"
      unfolding mod_centered_def Let_def using not_gt by simp
    hence mc_val: "mod_centered (x + q div 2) q = x + q div 2"
      using xmod_eq by simp

    have mc_pos: "x + q div 2 > 0"
    proof -
      have "- (q div 4) + 2 * (q div 4) = q div 4" by simp
      hence neg_plus_half: "- (q div 4) + q div 2 = q div 4"
        using q2_eq by simp
      have "x + q div 2 > - (q div 4) + q div 2"
        using x_gt by linarith
      hence "x + q div 2 > q div 4"
        using neg_plus_half by simp
      thus ?thesis
        using q4_pos by linarith
    qed

    have dist_eq: "dist0 q (x + q div 2) = x + q div 2"
      unfolding dist0_def using mc_val mc_pos by simp

    have gt_q4: "x + q div 2 > q div 4"
      using x_gt q2_eq by linarith

    show ?thesis
      unfolding decode_bit_def
      using dist_eq gt_q4 by simp
  qed
qed

end
