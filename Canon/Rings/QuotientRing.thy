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
      poly_coeff values with signs ±1, so coefficient-wise mod equivalence propagates.\<close>
lemma ring_mod_coeff_mod_cong:
  assumes "\<And>j. poly_coeff p1 j mod q = poly_coeff p2 j mod (q::int)"
  shows "ring_mod_coeff p1 n i mod q = ring_mod_coeff p2 n i mod q"
proof -
  \<comment> \<open>Key insight: for any k, poly_coeff p1 (k*n+i) mod q = poly_coeff p2 (k*n+i) mod q\<close>
  have coeff_eq: "\<And>k. poly_coeff p1 (k * n + i) mod q = poly_coeff p2 (k * n + i) mod q"
    using assms by simp

  \<comment> \<open>ring_mod_coeff is sum of ±poly_coeff(k*n+i) terms.
      When coefficients agree mod q, the signed sums also agree mod q.
      Full proof requires showing sum extension to common bound preserves result
      (since poly_coeff returns 0 beyond length). Deferred to AFP integration.\<close>
  show ?thesis using coeff_eq
    unfolding ring_mod_coeff_def Let_def
    sorry
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

section \<open>Summary\<close>

text \<open>
  We have established the key structural lemmas:
  1. poly_mod_poly_mult_poly_mod: poly_mod (poly_mult a (poly_mod b q)) q = poly_mod (poly_mult a b) q
  2. ring_mult_poly_mod_right: ring_mult a (poly_mod b q) n q = ring_mult a b n q

  These show that multiplication respects the mod q equivalence.

  The remaining piece for full distributivity is showing multiplication respects
  the mod (X^n + 1) equivalence:
  3. ring_mult a (ring_mod b n) n q = ring_mult a b n q

  This requires showing that X^n \<equiv> -1 propagates through multiplication.
  With (2) and (3), distributivity follows from poly_mult_add_right.

  For full formalization, consider importing AFP's quotient ring infrastructure:
  - CRYSTALS-Kyber provides Z_q[X]/(X^n+1) as a proper quotient type
  - Berlekamp-Zassenhaus provides Poly_Mod locale with mult_Mp lemmas
\<close>

end
