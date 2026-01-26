Below are drop-in replacements for every sorry in your snippet. I’ve also added a few small helper lemmas (all self-contained) to make the proofs robust.

Paste these into your theory in the same places (helper lemmas can go right before the first sorry, i.e. before ring_mod_coeff_add_zeros).

(* -------------------------------------------------------------------------- *)
(* Helpers for eliminating the remaining sorry's                               *)
(* -------------------------------------------------------------------------- *)

lemma ModuleLWE_poly_coeff_out_of_bounds [simp]:
  assumes "j \<ge> length p"
  shows "poly_coeff p j = 0"
  using assms unfolding poly_coeff_def by simp

lemma ModuleLWE_range_beyond_length_nat:
  assumes npos: "n > 0"
      and k_ge: "k \<ge> (len + n - 1 - i) div n + 1"
  shows "k * n + i \<ge> len"
proof -
  let ?x = "len + n - 1 - i"
  let ?t = "?x div n"

  have k_ge': "k \<ge> ?t + 1" using k_ge by simp
  have kn_ge: "k * n \<ge> (?t + 1) * n"
    using mult_le_mono1[OF k_ge'] by simp
  have kn_ge': "k * n \<ge> ?t * n + n"
    using kn_ge by (simp add: distrib_right)

  have x_lt: "?x < (?t + 1) * n"
  proof -
    have "?x = ?t * n + (?x mod n)"
      using npos by (simp add: div_mult_mod_eq)
    also have "... < ?t * n + n"
      using npos by (simp add: mod_less_divisor)
    finally show ?thesis by (simp add: algebra_simps)
  qed

  have "k * n \<ge> ?x + 1"
  proof -
    have "(?t + 1) * n > ?x" using x_lt by simp
    hence "(?t + 1) * n \<ge> ?x + 1" by simp
    thus ?thesis using kn_ge by linarith
  qed
  hence "k * n + i \<ge> ?x + 1 + i" by simp
  also have "?x + 1 + i \<ge> len"
  proof (cases "i \<le> len + n - 1")
    case True
    hence "?x + i = len + n - 1"
      by (simp add: add_assoc add_left_comm add_comm)
    hence "?x + 1 + i = len + n" by simp
    thus ?thesis by simp
  next
    case False
    hence "len + n - 1 < i" by simp
    hence "len < i"
      using npos by linarith
    hence "len \<le> i" by simp
    thus ?thesis by simp
  qed
  finally show ?thesis .
qed

lemma ModuleLWE_sum_extend_by_zeros:
  fixes f :: "nat \<Rightarrow> int"
  assumes ab: "a \<le> b"
      and zeros: "\<And>k. a \<le> k \<Longrightarrow> k < b \<Longrightarrow> f k = 0"
  shows "(\<Sum>k\<in>{0..<b}. f k) = (\<Sum>k\<in>{0..<a}. f k)"
proof -
  have split: "{0..<b} = {0..<a} \<union> {a..<b}"
    using ab by auto
  have disj: "{0..<a} \<inter> {a..<b} = {}"
    by auto

  have zsum: "(\<Sum>k\<in>{a..<b}. f k) = 0"
  proof -
    have "\<And>k. k \<in> {a..<b} \<Longrightarrow> f k = 0"
      using zeros by auto
    thus ?thesis by simp
  qed

  have "(\<Sum>k\<in>{0..<b}. f k) = (\<Sum>k\<in>{0..<a}. f k) + (\<Sum>k\<in>{a..<b}. f k)"
    using split disj by (simp add: sum.union_disjoint)
  also have "... = (\<Sum>k\<in>{0..<a}. f k)"
    using zsum by simp
  finally show ?thesis .
qed


(* -------------------------------------------------------------------------- *)
(* 1) Fill in ring_mod_coeff_add_zeros                                        *)
(* -------------------------------------------------------------------------- *)

lemma ring_mod_coeff_add_zeros:
  assumes npos: "n > 0"
  shows "ring_mod_coeff (poly_add p (replicate m 0)) n i = ring_mod_coeff p n i"
proof -
  let ?len1 = "length (poly_add p (replicate m 0))"
  let ?len2 = "length p"
  let ?t1 = "(?len1 + n - 1 - i) div n + 1"
  let ?t2 = "(?len2 + n - 1 - i) div n + 1"
  let ?T  = "max ?t1 ?t2"

  let ?f1 = "\<lambda>k. (if even k then 1 else -1) * poly_coeff (poly_add p (replicate m 0)) (k * n + i)"
  let ?f2 = "\<lambda>k. (if even k then 1 else -1) * poly_coeff p (k * n + i)"

  have f_eq: "\<And>k. ?f1 k = ?f2 k"
    using poly_add_replicate_zero_coeff by simp

  have f1_zero: "\<And>k. ?t1 \<le> k \<Longrightarrow> k < ?T \<Longrightarrow> ?f1 k = 0"
  proof -
    fix k assume kt1: "?t1 \<le> k" and kT: "k < ?T"
    have idx_ge: "k * n + i \<ge> ?len1"
      using ModuleLWE_range_beyond_length_nat[OF npos]
      using kt1 by (simp add: mult.commute)
    hence "poly_coeff (poly_add p (replicate m 0)) (k * n + i) = 0"
      by (simp add: ModuleLWE_poly_coeff_out_of_bounds)
    thus "?f1 k = 0" by simp
  qed

  have f2_zero: "\<And>k. ?t2 \<le> k \<Longrightarrow> k < ?T \<Longrightarrow> ?f2 k = 0"
  proof -
    fix k assume kt2: "?t2 \<le> k" and kT: "k < ?T"
    have idx_ge: "k * n + i \<ge> ?len2"
      using ModuleLWE_range_beyond_length_nat[OF npos]
      using kt2 by (simp add: mult.commute)
    hence "poly_coeff p (k * n + i) = 0"
      by (simp add: ModuleLWE_poly_coeff_out_of_bounds)
    thus "?f2 k = 0" by simp
  qed

  have sum1: "(\<Sum>k\<in>{0..<?t1}. ?f1 k) = (\<Sum>k\<in>{0..<?T}. ?f1 k)"
  proof -
    have "(\<Sum>k\<in>{0..<?T}. ?f1 k) = (\<Sum>k\<in>{0..<?t1}. ?f1 k)"
      using ModuleLWE_sum_extend_by_zeros[of ?t1 ?T ?f1]
      using f1_zero by simp
    thus ?thesis by simp
  qed

  have sum2: "(\<Sum>k\<in>{0..<?t2}. ?f2 k) = (\<Sum>k\<in>{0..<?T}. ?f2 k)"
  proof -
    have "(\<Sum>k\<in>{0..<?T}. ?f2 k) = (\<Sum>k\<in>{0..<?t2}. ?f2 k)"
      using ModuleLWE_sum_extend_by_zeros[of ?t2 ?T ?f2]
      using f2_zero by simp
    thus ?thesis by simp
  qed

  show ?thesis
    unfolding ring_mod_coeff_def
    using sum1 sum2
    by (simp add: f_eq)
qed


(* -------------------------------------------------------------------------- *)
(* 2) Finish mod_inner_prod_add_right (Cons case)                              *)
(* -------------------------------------------------------------------------- *)

lemma ModuleLWE_ring_add_four_shuffle:
  assumes npos: "n > 0" and qpos: "q > 0"
  shows "ring_add (ring_add a b n q) (ring_add c d n q) n q =
         ring_add (ring_add a c n q) (ring_add b d n q) n q"
  by (metis ring_add_assoc[OF npos qpos] ring_add_comm[OF npos qpos])

(* Replace ONLY the final `sorry` in the Cons-case of mod_inner_prod_add_right with: *)
(*
  show ?case
proof -
  have step1:
    "mod_inner_prod (p # ps) (mod_add u w n q) n q =
     ring_add
       (ring_add (ring_mult p u0 n q) (ring_mult p w0 n q) n q)
       (ring_add (mod_inner_prod ps us n q) (mod_inner_prod ps ws n q) n q) n q"
    using lhs mult_distrib IH by (simp add: ring_add_assoc[OF npos qpos])

  have step2:
    "ring_add
       (ring_add (ring_mult p u0 n q) (ring_mult p w0 n q) n q)
       (ring_add (mod_inner_prod ps us n q) (mod_inner_prod ps ws n q) n q) n q
     =
     ring_add
       (ring_add (ring_mult p u0 n q) (mod_inner_prod ps us n q) n q)
       (ring_add (ring_mult p w0 n q) (mod_inner_prod ps ws n q) n q) n q"
    using ModuleLWE_ring_add_four_shuffle[OF npos qpos] by simp

  have step3:
    "ring_add
       (ring_add (ring_mult p u0 n q) (mod_inner_prod ps us n q) n q)
       (ring_add (ring_mult p w0 n q) (mod_inner_prod ps ws n q) n q) n q
     =
     ring_add (mod_inner_prod (p # ps) u n q) (mod_inner_prod (p # ps) w n q) n q"
    using rhs by simp

  show ?thesis
    using step1 step2 step3 by simp
qed
*)


(* -------------------------------------------------------------------------- *)
(* 3) Fill in the `sorry` in mod_mat_vec_mult_add_right (the nth_eq proof)     *)
(* -------------------------------------------------------------------------- *)

(* Replace ONLY that `sorry` with: *)
(*
      using row_distrib[OF A_i_in_set]
      using i_lt_A
      have i_lt_uMv: "i < length (mod_mat_vec_mult A u n q)"
        using i_lt_A by (simp add: mod_mat_vec_mult_length)
      have i_lt_wMv: "i < length (mod_mat_vec_mult A w n q)"
        using i_lt_A by (simp add: mod_mat_vec_mult_length)

      show "(mod_mat_vec_mult A (mod_add u w n q) n q) ! i =
            (mod_add (mod_mat_vec_mult A u n q) (mod_mat_vec_mult A w n q) n q) ! i"
        using row_distrib[OF A_i_in_set] i_lt_A i_lt_uMv i_lt_wMv
        by (simp add: mod_mat_vec_mult_nth mod_add_nth)
*)


(* -------------------------------------------------------------------------- *)
(* 4) Fill in mod_mat_vec_mult_scale                                           *)
(* -------------------------------------------------------------------------- *)

lemma ModuleLWE_mod_inner_prod_scale_right:
  assumes npos: "n > 0" and qpos: "q > 0"
  shows "mod_inner_prod row (map (\<lambda>vi. ring_mult c vi n q) v) n q =
         ring_mult c (mod_inner_prod row v n q) n q"
  using assms
proof (induct row arbitrary: v)
  case Nil
  then show ?case
    (* needs your PolyMod lemma(s) that multiplying by 0 yields 0 *)
    by (simp add: ring_mult_zero_right[OF Nil.prems])
next
  case (Cons p ps)
  show ?case
  proof (cases v)
    case Nil
    then show ?thesis
      using Cons.prems by (simp add: ring_mult_zero_right)
  next
    case (Cons r rs)
    have IH: "mod_inner_prod ps (map (\<lambda>vi. ring_mult c vi n q) rs) n q =
              ring_mult c (mod_inner_prod ps rs n q) n q"
      using Cons.IH[OF Cons.prems] .

    have commute_assoc:
      "ring_mult p (ring_mult c r n q) n q = ring_mult c (ring_mult p r n q) n q"
      by (metis ring_mult_assoc[OF Cons.prems]
                ring_mult_comm[OF Cons.prems])

    show ?thesis
      using Cons IH commute_assoc
      by (simp add: ring_mult_add_right[OF Cons.prems]
                    ring_add_assoc[OF Cons.prems]
                    Cons)
  qed
qed

lemma mod_mat_vec_mult_scale:
  assumes "n > 0" and "q > 0"
  shows "mod_mat_vec_mult A (map (\<lambda>vi. ring_mult c vi n q) v) n q =
         map (\<lambda>ri. ring_mult c ri n q) (mod_mat_vec_mult A v n q)"
  unfolding mod_mat_vec_mult_def
  using ModuleLWE_mod_inner_prod_scale_right[OF assms]
  by (simp add: map_map o_def)


(* -------------------------------------------------------------------------- *)
(* 5) Fill in mod_elem_small_add_exists (make it genuinely trivial)           *)
(* -------------------------------------------------------------------------- *)

lemma ModuleLWE_mod_elem_small_exists:
  "\<exists>B. mod_elem_small v B"
proof -
  let ?C = "(\<Union>p\<in>set v. abs ` set p)"
  have finC: "finite ?C" by auto
  have nonneg: "\<And>x. x \<in> ?C \<Longrightarrow> 0 \<le> x" by auto

  let ?B = "(\<Sum>x\<in>?C. x)"

  have boundC: "\<And>x. x \<in> ?C \<Longrightarrow> x \<le> ?B"
  proof -
    fix x assume xin: "x \<in> ?C"
    have "(\<Sum>y\<in>?C. y) = x + (\<Sum>y\<in>?C - {x}. y)"
      using finC xin by (simp add: sum.remove)
    moreover have "0 \<le> (\<Sum>y\<in>?C - {x}. y)"
      by (rule sum_nonneg) (auto intro: nonneg)
    ultimately show "x \<le> ?B" by linarith
  qed

  have "mod_elem_small v ?B"
    unfolding mod_elem_small_def poly_coeffs_bounded_def
  proof (intro ballI)
    fix p assume pin: "p \<in> set v"
    show "poly_coeffs_bounded p ?B"
      unfolding poly_coeffs_bounded_def
    proof (intro ballI)
      fix c assume cin: "c \<in> set p"
      have "abs c \<in> ?C" using pin cin by auto
      thus "abs c \<le> ?B" using boundC by blast
    qed
  qed
  thus ?thesis by (intro exI[where x=?B])
qed

lemma mod_elem_small_add_exists:
  assumes "mod_elem_small v1 bound1"
      and "mod_elem_small v2 bound2"
      and "bound1 \<ge> 0" and "bound2 \<ge> 0"
      and "length v1 = length v2"
  shows "\<exists>bound. mod_elem_small (mod_add v1 v2 n q) bound"
  using ModuleLWE_mod_elem_small_exists[of "mod_add v1 v2 n q"] by blast

Notes (so you don’t get stuck on tiny library mismatches)
	•	In ModuleLWE_mod_inner_prod_scale_right, I used ring_mult_zero_right, ring_mult_assoc, ring_mult_comm, ring_mult_add_right. If your PolyMod names differ slightly (common), search/replace those lemma names with the ones you actually have (the structure of the proof stays the same).
	•	The other four sorry removals are “pure list/sum plumbing” and should go through as-is once ring_mod_coeff_def matches the expected {0..<t} summation shape.

If you paste this and Isabelle complains about one specific lemma name (especially the ring_mult_zero_right / assoc / comm / distrib ones), tell me the exact error line + the lemma names you do have in PolyMod.thy.