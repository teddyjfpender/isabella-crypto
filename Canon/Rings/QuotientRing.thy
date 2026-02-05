(*
  QuotientRing.thy - Quotient ring equivalence for distributivity proofs

  This theory establishes that multiplication respects the quotient ring
  equivalence in R_q = Z_q[X]/(X^n + 1).

  Key lemma: poly_mod (poly_mult a (poly_mod b q)) q = poly_mod (poly_mult a b) q
*)

theory QuotientRing
  imports PolyMod
begin

section \<open>Coefficient-Level Modular Arithmetic\<close>

lemma poly_coeff_poly_mod:
  "poly_coeff (poly_mod p q) i = (poly_coeff p i) mod q"
  unfolding poly_coeff_def poly_mod_def
  by (cases "i < length p") auto

lemma mod_mult_cong:
  "(a * (b mod q)) mod q = (a * b) mod (q::int)"
  by (simp add: mod_mult_right_eq)

lemma poly_mod_ne_if_ne:
  "p \<noteq> [] \<Longrightarrow> poly_mod p q \<noteq> []"
  unfolding poly_mod_def by simp

section \<open>Key Lemma: poly_mod Commutes Through poly_mult\<close>

text \<open>
  The crucial property: poly_mod (poly_mult a (poly_mod b q)) q = poly_mod (poly_mult a b) q

  Proof idea: The k-th coefficient of poly_mult a b is \<Sum>_j a_j * b_{k-j}.
  When we use poly_mod b q, each b_i becomes b_i mod q.
  But (a_j * (b_i mod q)) mod q = (a_j * b_i) mod q.
  So after the final poly_mod, we get the same result.

  This is the same pattern as mult_Mp in Berlekamp-Zassenhaus Poly_Mod locale.
\<close>

text \<open>Key lemma: sum of modded terms mod q equals sum of original terms mod q.
      This is equivalent to M_sum in AFP's Poly_Mod locale.\<close>
lemma sum_mod_eq:
  "(\<Sum>j \<in> A. f j mod (q::int)) mod q = (\<Sum>j \<in> A. f j) mod q"
proof (induct A rule: infinite_finite_induct)
  case (infinite A)
  then show ?case by simp
next
  case empty
  then show ?case by simp
next
  case (insert x A)
  have "(\<Sum>j\<in>insert x A. f j mod q) mod q = (f x mod q + (\<Sum>j\<in>A. f j mod q)) mod q"
    using insert(1-2) by simp
  also have "... = (f x mod q + ((\<Sum>j\<in>A. f j mod q) mod q)) mod q"
    by (simp add: mod_add_right_eq)
  also have "... = (f x mod q + ((\<Sum>j\<in>A. f j) mod q)) mod q"
    using insert(3) by simp
  also have "... = (f x + (\<Sum>j\<in>A. f j)) mod q"
    by (simp add: mod_add_eq)
  also have "... = (\<Sum>j\<in>insert x A. f j) mod q"
    using insert(1-2) by simp
  finally show ?case .
qed

text \<open>Generalization: sum where each term has a modded factor.\<close>
lemma sum_mult_mod_eq:
  "(\<Sum>j \<in> A. g j * (f j mod (q::int))) mod q = (\<Sum>j \<in> A. g j * f j) mod q"
proof (induct A rule: infinite_finite_induct)
  case (infinite A)
  then show ?case by simp
next
  case empty
  then show ?case by simp
next
  case (insert x A)
  have "(\<Sum>j\<in>insert x A. g j * (f j mod q)) mod q =
        (g x * (f x mod q) + (\<Sum>j\<in>A. g j * (f j mod q))) mod q"
    using insert(1-2) by simp
  also have "... = ((g x * (f x mod q)) mod q + ((\<Sum>j\<in>A. g j * (f j mod q)) mod q)) mod q"
    by (simp add: mod_add_eq)
  also have "... = ((g x * f x) mod q + ((\<Sum>j\<in>A. g j * f j) mod q)) mod q"
    using insert(3) by (simp add: mod_mult_right_eq)
  also have "... = (g x * f x + (\<Sum>j\<in>A. g j * f j)) mod q"
    by (simp add: mod_add_eq)
  also have "... = (\<Sum>j\<in>insert x A. g j * f j) mod q"
    using insert(1-2) by simp
  finally show ?case .
qed

text \<open>Specific instance of sum_mult_mod_eq for polynomial coefficient sums.\<close>
lemma sum_poly_coeff_mod_eq:
  "(\<Sum>j = 0 ..< m. poly_coeff p j * ((poly_coeff r (k - j)) mod q)) mod (q::int) =
   (\<Sum>j = 0 ..< m. poly_coeff p j * poly_coeff r (k - j)) mod q"
proof (induct m)
  case 0
  then show ?case by simp
next
  case (Suc m)
  have "(\<Sum>j = 0..<Suc m. poly_coeff p j * (poly_coeff r (k - j) mod q)) mod q =
        ((\<Sum>j = 0..<m. poly_coeff p j * (poly_coeff r (k - j) mod q)) +
         poly_coeff p m * (poly_coeff r (k - m) mod q)) mod q"
    by simp
  also have "... = (((\<Sum>j = 0..<m. poly_coeff p j * (poly_coeff r (k - j) mod q)) mod q) +
                    (poly_coeff p m * (poly_coeff r (k - m) mod q)) mod q) mod q"
    by (simp add: mod_add_eq)
  also have "... = (((\<Sum>j = 0..<m. poly_coeff p j * poly_coeff r (k - j)) mod q) +
                    (poly_coeff p m * poly_coeff r (k - m)) mod q) mod q"
    using Suc by (simp add: mod_mult_right_eq)
  also have "... = ((\<Sum>j = 0..<m. poly_coeff p j * poly_coeff r (k - j)) +
                    poly_coeff p m * poly_coeff r (k - m)) mod q"
    by (simp add: mod_add_eq)
  also have "... = (\<Sum>j = 0..<Suc m. poly_coeff p j * poly_coeff r (k - j)) mod q"
    by simp
  finally show ?case .
qed

lemma poly_mult_coeff_poly_mod_eq:
  assumes qpos: "q > 0"
  shows "poly_mult_coeff a (poly_mod b q) k mod q = poly_mult_coeff a b k mod q"
proof -
  \<comment> \<open>LHS uses poly_coeff_poly_mod\<close>
  have "poly_mult_coeff a (poly_mod b q) k =
        (\<Sum>j = 0 ..< Suc k. poly_coeff a j * poly_coeff (poly_mod b q) (k - j))"
    unfolding poly_mult_coeff_def by simp
  also have "... = (\<Sum>j = 0 ..< Suc k. poly_coeff a j * ((poly_coeff b (k - j)) mod q))"
    by (simp add: poly_coeff_poly_mod)
  finally have lhs: "poly_mult_coeff a (poly_mod b q) k =
                     (\<Sum>j = 0 ..< Suc k. poly_coeff a j * ((poly_coeff b (k - j)) mod q))" .

  have eq: "(\<Sum>j = 0..<Suc k. poly_coeff a j * (poly_coeff b (k - j) mod q)) mod q =
            (\<Sum>j = 0..<Suc k. poly_coeff a j * poly_coeff b (k - j)) mod q"
    using sum_poly_coeff_mod_eq[where m="Suc k" and p=a and r=b and k=k and q=q] by simp
  show ?thesis using lhs eq unfolding poly_mult_coeff_def by simp
qed

lemma poly_mod_poly_mult_poly_mod:
  assumes qpos: "q > 0"
  shows "poly_mod (poly_mult a (poly_mod b q)) q = poly_mod (poly_mult a b) q"
proof (cases "a = [] \<or> b = []")
  case True
  then show ?thesis
    by (cases "a = []") (auto simp: poly_mult_def poly_mod_def)
next
  case False
  hence a_ne: "a \<noteq> []" and b_ne: "b \<noteq> []" by auto

  have pm_len: "length (poly_mod b q) = length b" by simp
  have pm_ne: "poly_mod b q \<noteq> []" using b_ne poly_mod_ne_if_ne by auto
  have len_eq: "length (poly_mult a (poly_mod b q)) = length (poly_mult a b)"
    using a_ne b_ne pm_ne pm_len by (simp add: poly_mult_length)

  show ?thesis
  proof (intro nth_equalityI)
    show "length (poly_mod (poly_mult a (poly_mod b q)) q) =
          length (poly_mod (poly_mult a b) q)"
      using len_eq by simp
  next
    fix i assume i_lt: "i < length (poly_mod (poly_mult a (poly_mod b q)) q)"
    hence i_lt': "i < length (poly_mult a (poly_mod b q))" by simp
    hence i_lt_ab: "i < length (poly_mult a b)" using len_eq by simp

    have lhs: "(poly_mod (poly_mult a (poly_mod b q)) q) ! i =
               (poly_mult a (poly_mod b q)) ! i mod q"
      using i_lt' by (simp add: poly_mod_def)

    have rhs: "(poly_mod (poly_mult a b) q) ! i = (poly_mult a b) ! i mod q"
      using i_lt_ab by (simp add: poly_mod_def)

    have mult_pm: "(poly_mult a (poly_mod b q)) ! i = poly_mult_coeff a (poly_mod b q) i"
      using a_ne pm_ne i_lt' by (simp add: poly_mult_def)

    have mult_ab: "(poly_mult a b) ! i = poly_mult_coeff a b i"
      using a_ne b_ne i_lt_ab by (simp add: poly_mult_def)

    show "(poly_mod (poly_mult a (poly_mod b q)) q) ! i =
          (poly_mod (poly_mult a b) q) ! i"
      using lhs rhs mult_pm mult_ab poly_mult_coeff_poly_mod_eq[OF qpos, of a b i]
      by simp
  qed
qed

section \<open>Consequence: ring_mult Respects poly_mod\<close>

text \<open>
  From poly_mod_poly_mult_poly_mod, we can show that ring_mult with a poly_mod
  argument equals ring_mult with the original argument.
\<close>

text \<open>Helper: poly_mult indexing gives poly_mult_coeff.\<close>
lemma poly_mult_nth:
  assumes "p \<noteq> []" "q \<noteq> []" "i < length (poly_mult p q)"
  shows "(poly_mult p q) ! i = poly_mult_coeff p q i"
  using assms unfolding poly_mult_def by simp

text \<open>Helper: poly_coeff of poly_mult matches poly_mult_coeff.\<close>
lemma poly_coeff_poly_mult:
  "poly_coeff (poly_mult p q) i = (if p = [] \<or> q = [] then 0 else
     if i < length p + length q - 1 then poly_mult_coeff p q i else 0)"
proof (cases "p = [] \<or> q = []")
  case True
  then show ?thesis by (auto simp: poly_coeff_def)
next
  case False
  hence pne: "p \<noteq> []" and qne: "q \<noteq> []" by auto
  show ?thesis
  proof (cases "i < length p + length q - 1")
    case True
    hence ilt: "i < length (poly_mult p q)"
      using pne qne by (simp add: poly_mult_length)
    show ?thesis using True pne qne ilt poly_mult_nth[OF pne qne ilt]
      by (simp add: poly_coeff_nth)
  next
    case False
    hence "i \<ge> length (poly_mult p q)"
      using pne qne by (simp add: poly_mult_length)
    then show ?thesis using False pne qne by (simp add: poly_coeff_beyond)
  qed
qed

text \<open>Negation preserves mod equivalence.\<close>
lemma neg_mod_cong:
  assumes "a mod q = b mod (q::int)"
  shows "(-a) mod q = (-b) mod q"
proof -
  have "(-a) mod q = (-(a mod q)) mod q" by (simp add: mod_minus_eq)
  also have "... = (-(b mod q)) mod q" using assms by simp
  also have "... = (-b) mod q" by (simp add: mod_minus_eq)
  finally show ?thesis .
qed

text \<open>Sum of terms with alternating signs preserves mod equivalence.\<close>
lemma sum_list_signed_mod_eq:
  assumes "\<And>k. k \<in> set ks \<Longrightarrow> f k mod q = g k mod (q::int)"
  shows "sum_list (map (\<lambda>k. (if even k then 1 else -1) * f k) ks) mod q =
         sum_list (map (\<lambda>k. (if even k then 1 else -1) * g k) ks) mod q"
using assms
proof (induct ks)
  case Nil
  then show ?case by simp
next
  case (Cons k ks)
  have IH: "sum_list (map (\<lambda>k. (if even k then 1 else -1) * f k) ks) mod q =
            sum_list (map (\<lambda>k. (if even k then 1 else -1) * g k) ks) mod q"
    using Cons(2) by (intro Cons(1)) auto
  have fk_eq: "f k mod q = g k mod q"
    using Cons(2)[of k] by simp
  have term_eq: "((if even k then 1 else -1) * f k) mod q =
                 ((if even k then 1 else -1) * g k) mod q"
  proof (cases "even k")
    case True then show ?thesis using fk_eq by simp
  next
    case False then show ?thesis using neg_mod_cong[OF fk_eq] by simp
  qed
  have "sum_list (map (\<lambda>k. (if even k then 1 else -1) * f k) (k # ks)) mod q =
        ((if even k then 1 else -1) * f k +
         sum_list (map (\<lambda>k. (if even k then 1 else -1) * f k) ks)) mod q"
    by simp
  also have "... = (((if even k then 1 else -1) * f k) mod q +
                    sum_list (map (\<lambda>k. (if even k then 1 else -1) * f k) ks) mod q) mod q"
    by (simp add: mod_add_eq)
  also have "... = (((if even k then 1 else -1) * g k) mod q +
                    sum_list (map (\<lambda>k. (if even k then 1 else -1) * g k) ks) mod q) mod q"
    using term_eq IH by simp
  also have "... = sum_list (map (\<lambda>k. (if even k then 1 else -1) * g k) (k # ks)) mod q"
    by (simp add: mod_add_eq)
  finally show ?case .
qed

text \<open>ring_mod_coeff preserves mod equivalence when poly_coeff values are equivalent.
      This is a key structural lemma: ring_mod_coeff is a linear combination of
      poly_coeff values with signs ±1, so coefficient-wise mod equivalence propagates.

      Proof sketch:
      1. Both ring_mod_coeff results are signed sums of poly_coeff values
      2. The sums may have different ranges (depending on polynomial lengths)
      3. But poly_coeff returns 0 beyond length, so extending to common range is safe
      4. sum_list_signed_mod_eq shows the extended sums are equal mod q

      The arithmetic reasoning for bound extension requires explicit div/mod bounds;
      we discharge this by extending both sums to a common bound and showing
      the extra terms are zero.\<close>

lemma ring_mod_bound_index_ge:
  assumes n_gt0: "n > 0"
      and k_ge: "k \<ge> (length p + n - 1 - i) div n + 1"
  shows "k * n + i \<ge> length p"
proof -
  let ?m = "length p + n - 1 - i"
  have m_lt: "?m < ((?m div n) + 1) * n"
  proof -
    have mod_lt: "?m mod n < n"
      using n_gt0 by simp
    have "?m = (?m div n) * n + (?m mod n)"
      by simp
    also have "... < (?m div n) * n + n"
      using mod_lt by (rule add_strict_left_mono)
    also have "... = ((?m div n) + 1) * n"
      by (simp add: algebra_simps)
    finally show ?thesis .
  qed
  have k_ge': "((?m div n) + 1) \<le> k"
    using k_ge by simp
  have kn_ge: "((?m div n) + 1) * n \<le> k * n"
  proof -
    obtain d where k_def: "k = ((?m div n) + 1) + d"
      using k_ge' by (auto simp: le_iff_add)
    have "k * n = ((?m div n) + 1) * n + d * n"
      using k_def by (simp add: algebra_simps)
    then show ?thesis by simp
  qed
  have m_lt_kn: "?m < k * n"
    using m_lt kn_ge by (rule less_le_trans)
  have len_le_i_kn: "length p \<le> i + k * n"
  proof (cases "i \<le> length p + n - 1")
    case True
    hence i_m_eq: "i + ?m = length p + n - 1"
      by simp
    have "length p \<le> length p + n - 1"
      using n_gt0 by simp
    also have "... = i + ?m"
      using i_m_eq by simp
    also have "... < i + k * n"
      using m_lt_kn by simp
    finally show ?thesis
      by simp
  next
    case False
    hence i_gt: "i > length p + n - 1"
      by simp
    have "length p \<le> i"
      using i_gt n_gt0 by arith
    thus ?thesis
      by simp
  qed
  then show ?thesis
    by (simp add: add.commute)
qed

lemma ring_mod_coeff_mod_cong:
  assumes "\<And>j. poly_coeff p1 j mod q = poly_coeff p2 j mod (q::int)"
  shows "ring_mod_coeff p1 n i mod q = ring_mod_coeff p2 n i mod q"
proof (cases "n = 0")
  case True
  \<comment> \<open>When n = 0, ring_mod_coeff p 0 i = poly_coeff p i (single term sum)\<close>
  have "ring_mod_coeff p1 0 i = poly_coeff p1 i"
    unfolding ring_mod_coeff_def by simp
  moreover have "ring_mod_coeff p2 0 i = poly_coeff p2 i"
    unfolding ring_mod_coeff_def by simp
  ultimately show ?thesis using True assms[of i] by simp
next
  case npos: False
  hence n_gt0: "n > 0" by simp

  \<comment> \<open>Main case: n > 0.

      Structure of the proof:
      1. ring_mod_coeff is a signed sum: sum over k of (±1) * poly_coeff p (k*n+i)
      2. By assumption, poly_coeff p1 j ≡ poly_coeff p2 j (mod q) for all j
      3. Each term in the signed sum satisfies (±1)*f ≡ (±1)*g (mod q) when f ≡ g (mod q)
      4. The sums may have different bounds (based on polynomial lengths)
      5. But poly_coeff returns 0 beyond length, so extending to a common bound is safe
      6. Therefore the signed sums are equivalent mod q

      Key lemmas used:
      - neg_mod_cong: (-a) mod q = (-b) mod q when a mod q = b mod q
      - sum_list_signed_mod_eq: signed sums preserve mod equivalence term-by-term
      - poly_coeff_beyond: poly_coeff p i = 0 when i ≥ length p

      Full arithmetic for bound extension deferred.\<close>

  let ?t1 = "(length p1 + n - 1 - i) div n + 1"
  let ?t2 = "(length p2 + n - 1 - i) div n + 1"
  let ?t = "max ?t1 ?t2"
  let ?f1 = "\<lambda>k. (if even k then 1 else -1) * poly_coeff p1 (k * n + i)"
  let ?f2 = "\<lambda>k. (if even k then 1 else -1) * poly_coeff p2 (k * n + i)"

  have rm1: "ring_mod_coeff p1 n i = sum_list (map ?f1 [0 ..< ?t1])"
    unfolding ring_mod_coeff_def by simp
  have rm2: "ring_mod_coeff p2 n i = sum_list (map ?f2 [0 ..< ?t2])"
    unfolding ring_mod_coeff_def by simp

  \<comment> \<open>For k beyond the bound, the coefficient index is past the polynomial length.\<close>
  have f1_zero: "\<And>k. k \<ge> ?t1 \<Longrightarrow> ?f1 k = 0"
  proof -
    fix k assume k_ge: "k \<ge> ?t1"
    have idx_ge: "k * n + i \<ge> length p1"
      using ring_mod_bound_index_ge[OF n_gt0 k_ge] .
    thus "?f1 k = 0"
      by (simp add: poly_coeff_def)
  qed

  have f2_zero: "\<And>k. k \<ge> ?t2 \<Longrightarrow> ?f2 k = 0"
  proof -
    fix k assume k_ge: "k \<ge> ?t2"
    have idx_ge: "k * n + i \<ge> length p2"
      using ring_mod_bound_index_ge[OF n_gt0 k_ge] .
    thus "?f2 k = 0"
      by (simp add: poly_coeff_def)
  qed

  have split1: "[0 ..< ?t] = [0 ..< ?t1] @ [?t1 ..< ?t]"
    using upt_add_eq_append[of 0 ?t1 "?t - ?t1"] by simp
  have split2: "[0 ..< ?t] = [0 ..< ?t2] @ [?t2 ..< ?t]"
    using upt_add_eq_append[of 0 ?t2 "?t - ?t2"] by simp

  have tail1_zero: "sum_list (map ?f1 [?t1 ..< ?t]) = 0"
  proof -
    have all_zero: "\<forall>x \<in> set (map ?f1 [?t1 ..< ?t]). x = (0::int)"
    proof
      fix x assume "x \<in> set (map ?f1 [?t1 ..< ?t])"
      then obtain k where k_in: "k \<in> set [?t1 ..< ?t]" and x_def: "x = ?f1 k" by auto
      have k_ge: "k \<ge> ?t1" using k_in by auto
      show "x = 0" using f1_zero[OF k_ge] x_def by simp
    qed
    thus ?thesis using sum_list_all_zero_int by simp
  qed

  have tail2_zero: "sum_list (map ?f2 [?t2 ..< ?t]) = 0"
  proof -
    have all_zero: "\<forall>x \<in> set (map ?f2 [?t2 ..< ?t]). x = (0::int)"
    proof
      fix x assume "x \<in> set (map ?f2 [?t2 ..< ?t])"
      then obtain k where k_in: "k \<in> set [?t2 ..< ?t]" and x_def: "x = ?f2 k" by auto
      have k_ge: "k \<ge> ?t2" using k_in by auto
      show "x = 0" using f2_zero[OF k_ge] x_def by simp
    qed
    thus ?thesis using sum_list_all_zero_int by simp
  qed

  have extend1: "sum_list (map ?f1 [0 ..< ?t]) = sum_list (map ?f1 [0 ..< ?t1])"
    using split1 tail1_zero by simp
  have extend2: "sum_list (map ?f2 [0 ..< ?t]) = sum_list (map ?f2 [0 ..< ?t2])"
    using split2 tail2_zero by simp

  have coeff_equiv: "\<And>k. k \<in> set [0 ..< ?t] \<Longrightarrow>
        poly_coeff p1 (k * n + i) mod q = poly_coeff p2 (k * n + i) mod q"
    using assms by simp

  have sum_eq:
    "sum_list (map ?f1 [0 ..< ?t]) mod q =
     sum_list (map ?f2 [0 ..< ?t]) mod q"
    using sum_list_signed_mod_eq[OF coeff_equiv] .

  show ?thesis
    using rm1 rm2 extend1 extend2 sum_eq by simp
qed

text \<open>Helper: poly_mod of empty list is empty.\<close>
lemma poly_mod_empty [simp]: "poly_mod [] q = []"
  unfolding poly_mod_def by simp

lemma ring_mult_poly_mod_right:
  assumes npos: "n > 0" and qpos: "q > 0"
  shows "ring_mult a (poly_mod b q) n q = ring_mult a b n q"
proof -
  have "ring_mult a (poly_mod b q) n q = poly_mod (ring_mod (poly_mult a (poly_mod b q)) n) q"
    unfolding ring_mult_def ..

  also have "... = poly_mod (ring_mod (poly_mult a b) n) q"
  proof -
    \<comment> \<open>Coefficients of poly_mult a (poly_mod b q) \<equiv> coefficients of poly_mult a b (mod q)\<close>
    have coeff_equiv: "\<And>i. poly_coeff (poly_mult a (poly_mod b q)) i mod q =
                           poly_coeff (poly_mult a b) i mod q"
    proof -
      fix i
      show "poly_coeff (poly_mult a (poly_mod b q)) i mod q = poly_coeff (poly_mult a b) i mod q"
      proof (cases "a = []")
        case True
        then show ?thesis by simp
      next
        case False
        hence ane: "a \<noteq> []" by auto
        show ?thesis
        proof (cases "b = []")
          case True
          then show ?thesis by simp
        next
          case False
          hence bne: "b \<noteq> []" by auto
          hence pmne: "poly_mod b q \<noteq> []" using poly_mod_ne_if_ne by auto
          have pm_len: "length (poly_mod b q) = length b" by simp
          show ?thesis
          proof (cases "i < length a + length b - 1")
            case True
            hence ilt_pm: "i < length a + length (poly_mod b q) - 1" by simp
            show ?thesis using True ilt_pm ane bne pmne poly_mult_coeff_poly_mod_eq[OF qpos]
              by (simp add: poly_coeff_poly_mult)
          next
            case False
            hence "\<not> i < length a + length (poly_mod b q) - 1" by simp
            then show ?thesis using False ane bne pmne
              by (simp add: poly_coeff_poly_mult)
          qed
        qed
      qed
    qed

    \<comment> \<open>ring_mod_coeff preserves equivalence by linearity\<close>
    have rm_equiv: "\<And>j. ring_mod_coeff (poly_mult a (poly_mod b q)) n j mod q =
                         ring_mod_coeff (poly_mult a b) n j mod q"
      using coeff_equiv by (intro ring_mod_coeff_mod_cong) simp

    show ?thesis
    proof (intro nth_equalityI)
      show "length (poly_mod (ring_mod (poly_mult a (poly_mod b q)) n) q) =
            length (poly_mod (ring_mod (poly_mult a b) n) q)"
        using npos by (simp add: ring_mod_length)
    next
      fix i assume "i < length (poly_mod (ring_mod (poly_mult a (poly_mod b q)) n) q)"
      hence i_lt: "i < n" using npos by (simp add: ring_mod_length)
      show "(poly_mod (ring_mod (poly_mult a (poly_mod b q)) n) q) ! i =
            (poly_mod (ring_mod (poly_mult a b) n) q) ! i"
        using i_lt npos rm_equiv[of i]
        by (simp add: poly_mod_def ring_mod_length ring_mod_def)
    qed
  qed
  also have "... = ring_mult a b n q"
    unfolding ring_mult_def ..
  finally show ?thesis .
qed

section \<open>Distributivity in the Quotient Ring\<close>

text \<open>
  With ring_mult_poly_mod_right and reduced inputs (length n),
  we can prove distributivity: ring_mult a (ring_add b c n q) n q =
                               ring_add (ring_mult a b n q) (ring_mult a c n q) n q
\<close>

text \<open>Helper lemma: poly_mult distributes over poly_add, with case handling for empty lists.\<close>
lemma poly_mult_add_right_general:
  "poly_mult a (poly_add b c) = poly_add (poly_mult a b) (poly_mult a c)"
proof (cases "b = []")
  case True
  thus ?thesis by simp
next
  case bne: False
  show ?thesis
  proof (cases "c = []")
    case True
    thus ?thesis by simp
  next
    case cne: False
    show ?thesis using poly_mult_add_right[OF bne cne] by simp
  qed
qed

lemma ring_mult_add_right_via_quotient:
  assumes npos: "n > 0" and qpos: "q > 0"
      and len_b: "length b = n" and len_c: "length c = n"
  shows "ring_mult a (ring_add b c n q) n q =
         ring_add (ring_mult a b n q) (ring_mult a c n q) n q"
proof -
  have len_bc: "length (poly_add b c) = n"
    using len_b len_c by (simp add: poly_add_length)
  have ring_add_simp: "ring_add b c n q = poly_mod (poly_add b c) q"
    using npos len_bc unfolding ring_add_def by (simp add: ring_mod_already_n)

  \<comment> \<open>Remove outer poly_mod on the right argument\<close>
  have step1: "ring_mult a (ring_add b c n q) n q =
               ring_mult a (poly_add b c) n q"
    using ring_mult_poly_mod_right[OF npos qpos]
    by (simp add: ring_add_simp)

  \<comment> \<open>Distribute poly_mult over poly_add\<close>
  have dist: "poly_mult a (poly_add b c) = poly_add (poly_mult a b) (poly_mult a c)"
    by (rule poly_mult_add_right_general)

  have lhs_simp: "ring_mult a (poly_add b c) n q =
                  poly_mod (ring_mod (poly_add (poly_mult a b) (poly_mult a c)) n) q"
    unfolding ring_mult_def using dist by simp

  have rm_dist: "ring_mod (poly_add (poly_mult a b) (poly_mult a c)) n =
                 poly_add (ring_mod (poly_mult a b) n) (ring_mod (poly_mult a c) n)"
    using ring_mod_add[OF npos] .

  have lhs_final: "ring_mult a (poly_add b c) n q =
                   poly_mod (poly_add (ring_mod (poly_mult a b) n)
                                      (ring_mod (poly_mult a c) n)) q"
    using lhs_simp rm_dist by simp

  \<comment> \<open>RHS: ring_add of ring_mult results\<close>
  let ?ab = "ring_mult a b n q"
  let ?ac = "ring_mult a c n q"

  have len_ab: "length ?ab = n" using npos by (simp add: ring_mult_length)
  have len_ac: "length ?ac = n" using npos by (simp add: ring_mult_length)

  have rhs_simp: "ring_add ?ab ?ac n q = poly_mod (poly_add ?ab ?ac) q"
    using npos len_ab len_ac unfolding ring_add_def
    by (simp add: ring_mod_already_n poly_add_length)

  have step_a: "poly_mod (poly_add (ring_mod (poly_mult a b) n) (ring_mod (poly_mult a c) n)) q =
                poly_mod (poly_add ?ab ?ac) q"
  proof -
    have step_a1: "poly_mod (poly_add ?ab (ring_mod (poly_mult a c) n)) q =
                   poly_mod (poly_add (ring_mod (poly_mult a b) n) (ring_mod (poly_mult a c) n)) q"
      using poly_mod_poly_add_left[OF qpos,
                                   of "ring_mod (poly_mult a b) n" "ring_mod (poly_mult a c) n"]
      by (simp add: ring_mult_def)
    have step_a2: "poly_mod (poly_add ?ab ?ac) q =
                   poly_mod (poly_add ?ab (ring_mod (poly_mult a c) n)) q"
      using poly_mod_poly_add_right[OF qpos, of ?ab "ring_mod (poly_mult a c) n"]
      by (simp add: ring_mult_def)
    show ?thesis using step_a1 step_a2 by simp
  qed

  show ?thesis
    using step1 lhs_final rhs_simp step_a by simp
qed

section \<open>Summary\<close>

text \<open>
  We have established the key structural lemmas:
  1. poly_mod_poly_mult_poly_mod: poly_mod (poly_mult a (poly_mod b q)) q = poly_mod (poly_mult a b) q
  2. ring_mult_poly_mod_right: ring_mult a (poly_mod b q) n q = ring_mult a b n q
  3. ring_mult_add_right_via_quotient: distributivity in R_q for reduced inputs

  These show that multiplication distributes over addition on canonical
  representatives (length n lists). Extending to unreduced inputs would
  require a full quotient-ring proof of ring_mod compatibility.
\<close>

end
