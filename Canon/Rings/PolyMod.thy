theory PolyMod
  imports Canon_Base.Prelude Canon_Base.ListVec Canon_Base.Zq
begin

(* === Step 1: Polynomial Type and Basic Operations === *)
text \<open>
  Polynomials over Z_q:

  A polynomial p(X) = a_0 + a_1*X + a_2*X^2 + ... + a_{n-1}*X^{n-1}
  is represented as the list [a_0, a_1, ..., a_{n-1}].

  The empty list [] represents the zero polynomial.
  We work in R_q = Z_q[X]/(f(X)) for some modulus polynomial f.
\<close>

type_synonym poly = "int list"

definition zero_poly :: poly where
  "zero_poly = []"

definition const_poly :: "int \<Rightarrow> poly" where
  "const_poly c = (if c = 0 then [] else [c])"

definition poly_degree :: "poly \<Rightarrow> nat" where
  "poly_degree p = (if p = [] then 0 else length p - 1)"

definition poly_coeff :: "poly \<Rightarrow> nat \<Rightarrow> int" where
  "poly_coeff p i = (if i < length p then p ! i else 0)"

lemma poly_coeff_zero [simp]:
  "poly_coeff [] i = 0"
  unfolding poly_coeff_def by simp

lemma poly_coeff_nth:
  assumes "i < length p"
  shows "poly_coeff p i = p ! i"
  using assms unfolding poly_coeff_def by simp

lemma poly_coeff_beyond [simp]:
  assumes "i \<ge> length p"
  shows "poly_coeff p i = 0"
  using assms unfolding poly_coeff_def by simp

(* === Step 2: Polynomial Addition === *)
text \<open>
  Polynomial addition: (p + q)_i = p_i + q_i
  We pad the shorter polynomial with zeros.
\<close>

definition poly_add :: "poly \<Rightarrow> poly \<Rightarrow> poly" where
  "poly_add p q = (
    let n = max (length p) (length q) in
    map (\<lambda>i. poly_coeff p i + poly_coeff q i) [0 ..< n])"

lemma poly_add_length:
  "length (poly_add p q) = max (length p) (length q)"
  unfolding poly_add_def by simp

lemma poly_add_coeff:
  assumes "i < max (length p) (length q)"
  shows "(poly_add p q) ! i = poly_coeff p i + poly_coeff q i"
  using assms unfolding poly_add_def by simp

lemma poly_add_comm:
  "poly_add p q = poly_add q p"
  unfolding poly_add_def by (simp add: max.commute add.commute)

lemma map_conditional_id:
  "map (\<lambda>i. if i < length q then q ! i else (0::int)) [0..<length q] = q"
proof (intro nth_equalityI)
  show "length (map (\<lambda>i. if i < length q then q ! i else 0) [0..<length q]) = length q"
    by simp
next
  fix i assume "i < length (map (\<lambda>i. if i < length q then q ! i else 0) [0..<length q])"
  hence i_lt: "i < length q" by simp
  show "(map (\<lambda>i. if i < length q then q ! i else 0) [0..<length q]) ! i = q ! i"
    using i_lt by simp
qed

lemma poly_add_zero_left [simp]:
  "poly_add [] q = q"
  unfolding poly_add_def poly_coeff_def
  using map_conditional_id by simp

lemma poly_add_zero_right [simp]:
  "poly_add p [] = p"
  using poly_add_comm poly_add_zero_left by metis

(* === Step 3: Polynomial Subtraction and Negation === *)
text \<open>
  Polynomial negation and subtraction.
\<close>

definition poly_neg :: "poly \<Rightarrow> poly" where
  "poly_neg p = map uminus p"

lemma poly_neg_length [simp]:
  "length (poly_neg p) = length p"
  unfolding poly_neg_def by simp

lemma poly_neg_coeff:
  assumes "i < length p"
  shows "(poly_neg p) ! i = - (p ! i)"
  using assms unfolding poly_neg_def by simp

definition poly_sub :: "poly \<Rightarrow> poly \<Rightarrow> poly" where
  "poly_sub p q = poly_add p (poly_neg q)"

lemma poly_sub_length:
  "length (poly_sub p q) = max (length p) (length q)"
  unfolding poly_sub_def by (simp add: poly_add_length)

lemma poly_sub_self [simp]:
  "poly_sub p p = replicate (length p) 0"
  unfolding poly_sub_def poly_add_def poly_neg_def poly_coeff_def
  by (intro nth_equalityI) auto

(* === Step 4: Scalar Multiplication === *)
text \<open>
  Scalar multiplication: (c * p)_i = c * p_i
\<close>

definition poly_scale :: "int \<Rightarrow> poly \<Rightarrow> poly" where
  "poly_scale c p = map (\<lambda>a. c * a) p"

lemma poly_scale_length [simp]:
  "length (poly_scale c p) = length p"
  unfolding poly_scale_def by simp

lemma poly_scale_coeff:
  assumes "i < length p"
  shows "(poly_scale c p) ! i = c * (p ! i)"
  using assms unfolding poly_scale_def by simp

lemma poly_scale_zero [simp]:
  "poly_scale 0 p = replicate (length p) 0"
  unfolding poly_scale_def by (intro nth_equalityI) auto

lemma poly_scale_one [simp]:
  "poly_scale 1 p = p"
  unfolding poly_scale_def by (induct p) auto

lemma poly_scale_distrib:
  "poly_scale c (poly_add p q) =
   poly_add (poly_scale c p) (poly_scale c q)"
  unfolding poly_scale_def poly_add_def poly_coeff_def
  by (intro nth_equalityI) (auto simp: algebra_simps)

(* === Step 4b: Polynomial Addition Associativity === *)
text \<open>
  Polynomial addition is associative: (p + q) + r = p + (q + r)
\<close>

lemma poly_add_assoc:
  "poly_add (poly_add p q) r = poly_add p (poly_add q r)"
  unfolding poly_add_def poly_coeff_def
  by (intro nth_equalityI) (auto simp: algebra_simps)

(* === Step 5: Polynomial Multiplication === *)
text \<open>
  Polynomial multiplication:
  (p * q)_k = \<Sigma>_{i+j=k} p_i * q_j

  The result has degree = deg(p) + deg(q), so length = len(p) + len(q) - 1.
\<close>

definition poly_mult_coeff :: "poly \<Rightarrow> poly \<Rightarrow> nat \<Rightarrow> int" where
  "poly_mult_coeff p q k = (\<Sum>j = 0 ..< Suc k. poly_coeff p j * poly_coeff q (k - j))"

definition poly_mult :: "poly \<Rightarrow> poly \<Rightarrow> poly" where
  "poly_mult p q = (
    if p = [] \<or> q = [] then []
    else map (\<lambda>k. poly_mult_coeff p q k) [0 ..< length p + length q - 1])"

lemma poly_mult_length:
  assumes "p \<noteq> []" and "q \<noteq> []"
  shows "length (poly_mult p q) = length p + length q - 1"
  using assms unfolding poly_mult_def by simp

lemma poly_mult_zero_left [simp]:
  "poly_mult [] q = []"
  unfolding poly_mult_def by simp

lemma poly_mult_zero_right [simp]:
  "poly_mult p [] = []"
  unfolding poly_mult_def by simp

lemma poly_coeff_single:
  "poly_coeff [c] j = (if j = 0 then c else 0)"
  unfolding poly_coeff_def by auto

lemma sum_single_nonzero:
  assumes "\<forall>j \<in> {1 ..< Suc n}. f j = (0::int)"
  shows "(\<Sum>j = 0 ..< Suc n. f j) = f 0"
proof -
  have "(\<Sum>j = 0 ..< Suc n. f j) = f 0 + (\<Sum>j = 1 ..< Suc n. f j)"
    by (simp add: sum.atLeast_Suc_lessThan)
  also have "(\<Sum>j = 1 ..< Suc n. f j) = 0"
    using assms by simp
  finally show ?thesis by simp
qed

lemma poly_mult_const:
  assumes "c \<noteq> 0"
  shows "poly_mult [c] q = poly_scale c q"
proof (cases "q = []")
  case True
  then show ?thesis by (simp add: poly_mult_def poly_scale_def)
next
  case False
  have len_eq: "length (poly_mult [c] q) = length (poly_scale c q)"
    using False assms unfolding poly_mult_def poly_scale_def by simp
  show ?thesis
  proof (intro nth_equalityI[OF len_eq])
    fix i assume i_bound: "i < length (poly_mult [c] q)"
    hence i_lt: "i < length q"
      using False assms unfolding poly_mult_def by simp
    have step1: "(poly_mult [c] q) ! i = poly_mult_coeff [c] q i"
      using i_bound False assms unfolding poly_mult_def by simp
    have step2: "poly_mult_coeff [c] q i = (\<Sum>j = 0 ..< Suc i. poly_coeff [c] j * poly_coeff q (i - j))"
      unfolding poly_mult_coeff_def by simp
    have step3: "(\<Sum>j = 0 ..< Suc i. poly_coeff [c] j * poly_coeff q (i - j)) = poly_coeff [c] 0 * poly_coeff q i"
    proof -
      let ?f = "\<lambda>j. poly_coeff [c] j * poly_coeff q (i - j)"
      have zero_terms: "\<forall>j \<in> {1 ..< Suc i}. ?f j = 0"
        using poly_coeff_single by simp
      have "(\<Sum>j = 0 ..< Suc i. ?f j) = ?f 0"
        using sum_single_nonzero[OF zero_terms] by simp
      thus ?thesis by simp
    qed
    have step4: "poly_coeff [c] 0 * poly_coeff q i = c * q ! i"
      using i_lt unfolding poly_coeff_def by simp
    have step5: "c * q ! i = (poly_scale c q) ! i"
      using i_lt unfolding poly_scale_def by simp
    show "(poly_mult [c] q) ! i = (poly_scale c q) ! i"
      using step1 step2 step3 step4 step5 by simp
  qed
qed

(* === Step 5b: Polynomial Multiplication Distributivity === *)
text \<open>
  Polynomial multiplication distributes over addition:
  a * (b + c) = a*b + a*c

  Proof uses sum.distrib: (\<Sum>i. f i + g i) = (\<Sum>i. f i) + (\<Sum>i. g i)
\<close>

lemma poly_mult_coeff_add_right:
  "poly_mult_coeff a (poly_add b c) k =
   poly_mult_coeff a b k + poly_mult_coeff a c k"
proof -
  have "poly_mult_coeff a (poly_add b c) k =
        (\<Sum>j = 0 ..< Suc k. poly_coeff a j * poly_coeff (poly_add b c) (k - j))"
    unfolding poly_mult_coeff_def by simp
  also have "... = (\<Sum>j = 0 ..< Suc k. poly_coeff a j * (poly_coeff b (k - j) + poly_coeff c (k - j)))"
  proof -
    have "\<forall>j < Suc k. poly_coeff (poly_add b c) (k - j) = poly_coeff b (k - j) + poly_coeff c (k - j)"
      unfolding poly_add_def poly_coeff_def by auto
    thus ?thesis by (intro sum.cong) auto
  qed
  also have "... = (\<Sum>j = 0 ..< Suc k. poly_coeff a j * poly_coeff b (k - j) +
                                        poly_coeff a j * poly_coeff c (k - j))"
    by (simp add: algebra_simps)
  also have "... = (\<Sum>j = 0 ..< Suc k. poly_coeff a j * poly_coeff b (k - j)) +
                   (\<Sum>j = 0 ..< Suc k. poly_coeff a j * poly_coeff c (k - j))"
    by (simp add: sum.distrib)
  also have "... = poly_mult_coeff a b k + poly_mult_coeff a c k"
    unfolding poly_mult_coeff_def by simp
  finally show ?thesis .
qed

text \<open>
  Full distributivity lemma for polynomial multiplication.
  Note: This requires careful handling of empty list cases.
\<close>

lemma poly_mult_coeff_zero_beyond:
  assumes "k \<ge> length p + length q - 1" and "p \<noteq> []" and "q \<noteq> []"
  shows "poly_mult_coeff p q k = 0"
proof -
  have len_p: "length p \<ge> 1" using assms(2) by (cases p) auto
  have len_q: "length q \<ge> 1" using assms(3) by (cases q) auto

  {
    fix j :: nat assume j_range: "j < Suc k"
    have "poly_coeff p j * poly_coeff q (k - j) = 0"
    proof (cases "j < length p")
      case True
      have kj_bound: "k - j \<ge> length q"
        using assms(1) True len_p len_q by linarith
      thus ?thesis by simp
    next
      case False
      thus ?thesis by simp
    qed
  }
  hence all_zero: "\<forall>j < Suc k. poly_coeff p j * poly_coeff q (k - j) = 0" by blast

  have "(\<Sum>j = 0 ..< Suc k. poly_coeff p j * poly_coeff q (k - j)) =
        (\<Sum>j = 0 ..< Suc k. 0)"
    using all_zero by (intro sum.cong) auto
  also have "... = 0" by simp
  finally show ?thesis unfolding poly_mult_coeff_def .
qed

lemma poly_mult_add_right:
  assumes "b \<noteq> []" and "c \<noteq> []"
  shows "poly_mult a (poly_add b c) =
         poly_add (poly_mult a b) (poly_mult a c)"
proof (cases "a = []")
  case True
  then show ?thesis by simp
next
  case False
  have bc_ne: "poly_add b c \<noteq> []"
  proof -
    have len_pos: "length (poly_add b c) \<ge> 1"
    proof -
      have "length b \<ge> 1" using assms(1) by (cases b) auto
      hence "max (length b) (length c) \<ge> 1" by simp
      thus ?thesis by (simp add: poly_add_length)
    qed
    thus ?thesis by auto
  qed

  \<comment> \<open>Length analysis\<close>
  have len_bc: "length (poly_add b c) = max (length b) (length c)"
    by (simp add: poly_add_length)
  have len_left: "length (poly_mult a (poly_add b c)) = length a + max (length b) (length c) - 1"
    using False bc_ne len_bc by (simp add: poly_mult_length)
  have len_ab: "length (poly_mult a b) = length a + length b - 1"
    using False assms(1) by (simp add: poly_mult_length)
  have len_ac: "length (poly_mult a c) = length a + length c - 1"
    using False assms(2) by (simp add: poly_mult_length)
  have len_right: "length (poly_add (poly_mult a b) (poly_mult a c)) =
                   max (length a + length b - 1) (length a + length c - 1)"
    by (simp add: poly_add_length len_ab len_ac)
  have len_eq: "length (poly_mult a (poly_add b c)) =
                length (poly_add (poly_mult a b) (poly_mult a c))"
  proof -
    have "length a \<ge> 1" using False by (cases a) auto
    have "length b \<ge> 1" using assms(1) by (cases b) auto
    have "length c \<ge> 1" using assms(2) by (cases c) auto
    \<comment> \<open>Key: length a + max (length b) (length c) - 1 =
              max (length a + length b - 1) (length a + length c - 1)\<close>
    have "length a + max (length b) (length c) - 1 =
          max (length a + length b - 1) (length a + length c - 1)"
      using \<open>length a \<ge> 1\<close> \<open>length b \<ge> 1\<close> \<open>length c \<ge> 1\<close> by auto
    thus ?thesis using len_left len_right by simp
  qed

  show ?thesis
  proof (intro nth_equalityI[OF len_eq])
    fix k assume k_bound: "k < length (poly_mult a (poly_add b c))"

    have left_coeff: "(poly_mult a (poly_add b c)) ! k = poly_mult_coeff a (poly_add b c) k"
      using k_bound False bc_ne unfolding poly_mult_def by simp

    have k_lt_right: "k < length (poly_add (poly_mult a b) (poly_mult a c))"
      using k_bound len_eq by simp
    have k_lt_max: "k < max (length (poly_mult a b)) (length (poly_mult a c))"
      using k_lt_right by (simp add: poly_add_length)

    have right_coeff: "(poly_add (poly_mult a b) (poly_mult a c)) ! k =
                       poly_coeff (poly_mult a b) k + poly_coeff (poly_mult a c) k"
      using k_lt_max by (simp add: poly_add_coeff)

    have mult_coeff_ab: "poly_coeff (poly_mult a b) k = poly_mult_coeff a b k"
    proof (cases "k < length a + length b - 1")
      case True
      thus ?thesis using False assms(1) unfolding poly_mult_def poly_coeff_def by auto
    next
      case k_beyond: False
      have "poly_coeff (poly_mult a b) k = 0"
        using k_beyond \<open>a \<noteq> []\<close> assms(1) by (simp add: poly_mult_length)
      moreover have "poly_mult_coeff a b k = 0"
        using k_beyond \<open>a \<noteq> []\<close> assms(1) poly_mult_coeff_zero_beyond by auto
      ultimately show ?thesis by simp
    qed

    have mult_coeff_ac: "poly_coeff (poly_mult a c) k = poly_mult_coeff a c k"
    proof (cases "k < length a + length c - 1")
      case True
      thus ?thesis using False assms(2) unfolding poly_mult_def poly_coeff_def by auto
    next
      case k_beyond: False
      have "poly_coeff (poly_mult a c) k = 0"
        using k_beyond \<open>a \<noteq> []\<close> assms(2) by (simp add: poly_mult_length)
      moreover have "poly_mult_coeff a c k = 0"
        using k_beyond \<open>a \<noteq> []\<close> assms(2) poly_mult_coeff_zero_beyond by auto
      ultimately show ?thesis by simp
    qed

    show "(poly_mult a (poly_add b c)) ! k = (poly_add (poly_mult a b) (poly_mult a c)) ! k"
      using left_coeff right_coeff mult_coeff_ab mult_coeff_ac poly_mult_coeff_add_right
      by simp
  qed
qed

(* === Step 6: Modular Reduction of Coefficients === *)
text \<open>
  Reduce polynomial coefficients modulo q.
  This gives us polynomials in Z_q[X].
\<close>

definition poly_mod :: "poly \<Rightarrow> int \<Rightarrow> poly" where
  "poly_mod p q = map (\<lambda>a. a mod q) p"

lemma poly_mod_length [simp]:
  "length (poly_mod p q) = length p"
  unfolding poly_mod_def by simp

lemma poly_mod_coeff:
  assumes "i < length p" and "q > 0"
  shows "(poly_mod p q) ! i = (p ! i) mod q"
  using assms unfolding poly_mod_def by simp

lemma poly_mod_range:
  assumes "q > 0" and "a \<in> set (poly_mod p q)"
  shows "0 \<le> a \<and> a < q"
  using assms unfolding poly_mod_def by auto

lemma poly_mod_idem:
  assumes "q > 0"
  shows "poly_mod (poly_mod p q) q = poly_mod p q"
  unfolding poly_mod_def using assms by simp

(* === Step 6b: Centered Coefficient Interpretation === *)
text \<open>
  For "smallness" bounds, we interpret coefficients in centered form:
  coefficients in [0, q) are mapped to (-q/2, q/2] by subtracting q when > q/2.

  This is important for ZK protocols where we need ||z|| < gamma - beta.
\<close>

definition centered_coeff :: "int \<Rightarrow> int \<Rightarrow> int" where
  "centered_coeff c q = (if c > q div 2 then c - q else c)"

lemma centered_coeff_bound:
  assumes "0 \<le> c" and "c < q" and "q > 0"
  shows "\<bar>centered_coeff c q\<bar> \<le> q div 2 + q mod 2"
  unfolding centered_coeff_def using assms by auto

lemma centered_coeff_range:
  assumes "0 \<le> c" and "c < q" and "q > 0"
  shows "centered_coeff c q > - (q div 2 + 1)"
    and "centered_coeff c q \<le> q div 2"
  unfolding centered_coeff_def using assms by auto

text \<open>
  After poly_mod, all coefficients are in [0, q).
  We can interpret them as centered for bound analysis.
\<close>

definition poly_centered :: "poly \<Rightarrow> int \<Rightarrow> poly" where
  "poly_centered p q = map (\<lambda>c. centered_coeff c q) p"

lemma poly_centered_length [simp]:
  "length (poly_centered p q) = length p"
  unfolding poly_centered_def by simp

lemma poly_mod_add:
  assumes "q > 0"
  assumes "length p = n" and "length r = n"
  shows "poly_mod (poly_add p r) q = poly_mod (poly_add (poly_mod p q) (poly_mod r q)) q"
proof (intro nth_equalityI)
  show "length (poly_mod (poly_add p r) q) =
        length (poly_mod (poly_add (poly_mod p q) (poly_mod r q)) q)"
    using assms by (simp add: poly_add_length)
next
  fix i assume "i < length (poly_mod (poly_add p r) q)"
  hence i_lt: "i < n"
    using assms by (simp add: poly_add_length)
  have "(poly_mod (poly_add p r) q) ! i = (poly_add p r) ! i mod q"
    using i_lt assms by (simp add: poly_mod_coeff poly_add_length)
  also have "... = (poly_coeff p i + poly_coeff r i) mod q"
    using i_lt assms by (simp add: poly_add_coeff)
  also have "... = ((p ! i) mod q + (r ! i) mod q) mod q"
    using i_lt assms unfolding poly_coeff_def by (simp add: mod_add_eq)
  also have "... = (poly_mod (poly_add (poly_mod p q) (poly_mod r q)) q) ! i"
  proof -
    have "(poly_add (poly_mod p q) (poly_mod r q)) ! i =
          poly_coeff (poly_mod p q) i + poly_coeff (poly_mod r q) i"
      using i_lt assms by (simp add: poly_add_coeff)
    also have "... = (p ! i) mod q + (r ! i) mod q"
      using i_lt assms unfolding poly_coeff_def poly_mod_def by simp
    finally show ?thesis
      using i_lt assms by (simp add: poly_mod_coeff poly_add_length mod_add_eq)
  qed
  finally show "(poly_mod (poly_add p r) q) ! i =
                (poly_mod (poly_add (poly_mod p q) (poly_mod r q)) q) ! i" .
qed

(* === Step 7: Ring Polynomial Modulus (X^n + 1) === *)
text \<open>
  The ring R_q = Z_q[X]/(X^n + 1).

  To reduce a polynomial modulo X^n + 1:
  - Coefficients at positions >= n wrap around with sign change
  - X^n \<equiv> -1 (mod X^n + 1), so X^{n+k} \<equiv> -X^k

  For a polynomial of length m > n:
    result_i = p_i - p_{n+i} + p_{2n+i} - p_{3n+i} + ...
\<close>

definition ring_mod_coeff :: "poly \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int" where
  "ring_mod_coeff p n i = (
    let terms = map (\<lambda>k. (if even k then 1 else -1) * poly_coeff p (k * n + i))
                    [0 ..< (length p + n - 1 - i) div n + 1]
    in sum_list terms)"

definition ring_mod :: "poly \<Rightarrow> nat \<Rightarrow> poly" where
  "ring_mod p n = (
    if n = 0 then p
    else map (\<lambda>i. ring_mod_coeff p n i) [0 ..< n])"

lemma ring_mod_length:
  assumes "n > 0"
  shows "length (ring_mod p n) = n"
  using assms unfolding ring_mod_def by simp

lemma sum_list_all_zero_int:
  assumes "\<forall>x \<in> set xs. x = (0::int)"
  shows "sum_list xs = 0"
  using assms by (induct xs) auto

lemma ring_mod_coeff_below_n:
  assumes n_pos: "n > 0"
  assumes len_le: "length p \<le> n"
  assumes i_lt: "i < n"
  shows "ring_mod_coeff p n i = poly_coeff p i"
proof -
  let ?t = "(length p + n - 1 - i) div n + 1"
  let ?g = "\<lambda>k. (if even k then (1::int) else -1) * poly_coeff p (k * n + i)"

  have t_pos: "0 < ?t" by simp
  have range_split: "[0..< ?t] = 0 # [1..< ?t]"
    using t_pos upt_conv_Cons by auto

  have g0: "?g 0 = poly_coeff p i"
    by simp

  have g_rest_zero: "\<forall>k \<in> set [1..< ?t]. ?g k = (0::int)"
  proof
    fix k assume k_in: "k \<in> set [1..< ?t]"
    have k_ge1: "1 \<le> k"
      using k_in by auto

    have idx_ge_n: "n \<le> k * n + i"
    proof (cases k)
      case 0
      have False using k_ge1 0 by simp
      then show ?thesis by blast
    next
      case (Suc k')
      then show ?thesis by simp
    qed

    have idx_ge_lenp: "length p \<le> k * n + i"
      using len_le idx_ge_n by (rule le_trans)

    have coeff0: "poly_coeff p (k * n + i) = 0"
      using idx_ge_lenp by simp

    show "?g k = 0"
      using coeff0 by simp
  qed

  have rest_all0: "\<forall>x \<in> set (map ?g [1..< ?t]). x = (0::int)"
    using g_rest_zero by auto

  have rest_sum0: "sum_list (map ?g [1..< ?t]) = 0"
    using sum_list_all_zero_int[OF rest_all0] .

  have "ring_mod_coeff p n i = sum_list (map ?g [0..< ?t])"
    unfolding ring_mod_coeff_def by simp
  also have "... = sum_list (map ?g (0 # [1..< ?t]))"
    using range_split by simp
  also have "... = sum_list (?g 0 # map ?g [1..< ?t])"
    by simp
  also have "... = ?g 0 + sum_list (map ?g [1..< ?t])"
    by simp
  also have "... = poly_coeff p i"
    using g0 rest_sum0 by simp
  finally show ?thesis .
qed

lemma ring_mod_below_n:
  assumes n_pos: "n > 0" and len_le: "length p \<le> n"
  shows "ring_mod p n = p @ replicate (n - length p) 0"
proof (intro nth_equalityI)
  show "length (ring_mod p n) = length (p @ replicate (n - length p) 0)"
    using n_pos len_le by (simp add: ring_mod_length)
next
  fix i assume i_bound: "i < length (ring_mod p n)"
  have i_lt: "i < n"
    using i_bound n_pos by (simp add: ring_mod_length)

  have rm_nth: "(ring_mod p n) ! i = ring_mod_coeff p n i"
    using i_lt n_pos unfolding ring_mod_def by simp

  have coeff_collapse: "ring_mod_coeff p n i = poly_coeff p i"
    using ring_mod_coeff_below_n[OF n_pos len_le i_lt] .

  show "(ring_mod p n) ! i = (p @ replicate (n - length p) 0) ! i"
  proof (cases "i < length p")
    case True
    have "(ring_mod p n) ! i = p ! i"
      using rm_nth coeff_collapse True by (simp add: poly_coeff_def)
    also have "... = (p @ replicate (n - length p) 0) ! i"
      using True by (simp add: nth_append)
    finally show ?thesis .
  next
    case False
    hence i_ge_len: "i \<ge> length p" by simp

    have "(ring_mod p n) ! i = 0"
      using rm_nth coeff_collapse i_ge_len by simp

    moreover have i_minus_lt: "i - length p < n - length p"
      using i_lt i_ge_len by simp

    have "(p @ replicate (n - length p) 0) ! i = 0"
      using i_ge_len i_minus_lt by (simp add: nth_append)

    ultimately show ?thesis by simp
  qed
qed

(* === Step 7b: Ring Mod Distributivity === *)
text \<open>
  ring_mod distributes over poly_add:
  ring_mod (p + q) n = ring_mod p n + ring_mod q n

  This follows from linearity of the reduction modulo X^n + 1.
  Each coefficient of ring_mod is a sum of coefficients from the input
  (with alternating signs for wraparound), and addition distributes over this.
\<close>

lemma poly_coeff_poly_add:
  "poly_coeff (poly_add p r) k = poly_coeff p k + poly_coeff r k"
  unfolding poly_add_def poly_coeff_def by auto

lemma sum_list_map_add:
  fixes f g :: "nat \<Rightarrow> int"
  shows "sum_list (map (\<lambda>k. f k + g k) xs) = sum_list (map f xs) + sum_list (map g xs)"
proof (induct xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  have "sum_list (map (\<lambda>k. f k + g k) (a # xs)) = f a + g a + sum_list (map (\<lambda>k. f k + g k) xs)"
    by simp
  also have "... = f a + g a + (sum_list (map f xs) + sum_list (map g xs))"
    using Cons by simp
  also have "... = (f a + sum_list (map f xs)) + (g a + sum_list (map g xs))"
    by (simp add: algebra_simps)
  also have "... = sum_list (map f (a # xs)) + sum_list (map g (a # xs))"
    by simp
  finally show ?case .
qed

lemma sum_list_all_zero:
  fixes f :: "nat \<Rightarrow> int"
  assumes "\<And>k. k \<in> set xs \<Longrightarrow> f k = 0"
  shows "sum_list (map f xs) = 0"
  using assms by (induct xs) auto

(* Helper for showing a mapped sum over a range is zero when all terms are zero *)
lemma sum_list_map_zero:
  fixes f :: "'a \<Rightarrow> int"
  assumes "\<And>x. x \<in> set xs \<Longrightarrow> f x = 0"
  shows "sum_list (map f xs) = 0"
  using assms by (induct xs) auto

(* A small helper that does NOT loop: extend an upt-sum if the tail is zero. *)
lemma sum_list_map_upt_extend_zero:
  fixes f :: "nat \<Rightarrow> int"
  assumes mn: "m \<le> n"
      and zero: "\<And>k. m \<le> k \<Longrightarrow> k < n \<Longrightarrow> f k = 0"
  shows "sum_list (map f [0..<n]) = sum_list (map f [0..<m])"
proof -
  have split: "[0..<n] = [0..<m] @ [m..<n]"
    using mn upt_add_eq_append[of 0 m "n - m"] by simp

  have zeros_in_tail: "\<And>k. k \<in> set [m..<n] \<Longrightarrow> f k = 0"
    using zero by auto

  have tail0: "sum_list (map f [m..<n]) = 0"
    using sum_list_map_zero[OF zeros_in_tail] .

  show ?thesis
    using split tail0 by simp
qed

lemma range_beyond_length_nat:
  fixes len n i k :: nat
  assumes npos: "n > 0"
      and k_ge: "k \<ge> (len + n - 1 - i) div n + 1"
  shows "k * n + i \<ge> len"
proof -
  let ?A = "len + n - 1"
  let ?a = "?A - i"

  have A_le_ai: "?A \<le> ?a + i"
    by (cases "i \<le> ?A") simp_all

  have a_lt: "?a < (?a div n + 1) * n"
  proof -
    have mod_bound: "?a mod n < n" using npos by simp
    have decomp: "?a = ?a div n * n + ?a mod n" by simp
    have step: "?a div n * n + ?a mod n < ?a div n * n + n"
    proof -
      have "?a mod n < n" using mod_bound .
      thus ?thesis by linarith
    qed
    have "?a < ?a div n * n + n"
      using decomp step by simp
    thus ?thesis by (simp add: algebra_simps)
  qed

  have len_le_A: "len \<le> ?A"
    using npos by simp

  have len_le_base: "len \<le> (?a div n + 1) * n + i"
  proof -
    have "?a + i < (?a div n + 1) * n + i"
      using a_lt by simp
    hence "?A < (?a div n + 1) * n + i"
      using A_le_ai by simp
    thus ?thesis using len_le_A by simp
  qed

  have base_le_k: "((?a div n + 1) * n + i) \<le> (k * n + i)"
  proof -
    have t_le_k: "?a div n + 1 \<le> k" using k_ge by simp
    have "((?a div n + 1) * n) \<le> (k * n)"
      using mult_le_mono1[OF t_le_k] by simp
    thus ?thesis by simp
  qed

  show ?thesis
    using le_trans[OF len_le_base base_le_k] .
qed

lemma range_beyond_length:
  assumes "n > 0" and "k \<ge> (length p + n - 1 - i) div n + 1"
  shows "k * n + i \<ge> length p"
  using range_beyond_length_nat[OF assms] .

lemma ring_mod_coeff_add:
  assumes npos: "n > 0"
  shows "ring_mod_coeff (poly_add p r) n i =
         ring_mod_coeff p n i + ring_mod_coeff r n i"
proof -
  let ?len_sum = "max (length p) (length r)"
  let ?t_sum   = "(?len_sum + n - 1 - i) div n + 1"
  let ?t_p     = "(length p + n - 1 - i) div n + 1"
  let ?t_r     = "(length r + n - 1 - i) div n + 1"

  have len_add: "length (poly_add p r) = ?len_sum"
    by (simp add: poly_add_length)

  let ?f_p = "\<lambda>k. (if even k then 1 else -1) * poly_coeff p (k * n + i)"
  let ?f_r = "\<lambda>k. (if even k then 1 else -1) * poly_coeff r (k * n + i)"
  let ?f_sum = "\<lambda>k. (if even k then 1 else -1) * poly_coeff (poly_add p r) (k * n + i)"

  have f_sum: "\<And>k. ?f_sum k = ?f_p k + ?f_r k"
    using poly_coeff_poly_add by (simp add: algebra_simps)

  have sum_map_add_eq:
    "sum_list (map (\<lambda>k. ?f_p k + ?f_r k) [0..< ?t_sum]) =
     sum_list (map ?f_p [0..< ?t_sum]) + sum_list (map ?f_r [0..< ?t_sum])"
    using sum_list_map_add[of ?f_p ?f_r "[0..< ?t_sum]"] by simp

  (* Monotonicity: because length p \<le> max(length p)(length r), we get ?t_p \<le> ?t_sum (same for r). *)
  have t_p_le: "?t_p \<le> ?t_sum"
  proof -
    have lp_le: "length p \<le> ?len_sum" by simp
    have "length p + n - 1 - i \<le> ?len_sum + n - 1 - i"
      using lp_le by simp
    hence "(length p + n - 1 - i) div n \<le> (?len_sum + n - 1 - i) div n"
      by (rule div_le_mono)
    thus ?thesis by simp
  qed

  have t_r_le: "?t_r \<le> ?t_sum"
  proof -
    have lr_le: "length r \<le> ?len_sum" by simp
    have "length r + n - 1 - i \<le> ?len_sum + n - 1 - i"
      using lr_le by simp
    hence "(length r + n - 1 - i) div n \<le> (?len_sum + n - 1 - i) div n"
      by (rule div_le_mono)
    thus ?thesis by simp
  qed

  have sum_p_to_tsum:
    "sum_list (map ?f_p [0..< ?t_sum]) = sum_list (map ?f_p [0..< ?t_p])"
  proof -
    have zero: "\<And>k. ?t_p \<le> k \<Longrightarrow> k < ?t_sum \<Longrightarrow> ?f_p k = 0"
    proof -
      fix k assume kp: "?t_p \<le> k" and _ : "k < ?t_sum"
      have "k \<ge> (length p + n - 1 - i) div n + 1" using kp by simp
      hence "k * n + i \<ge> length p"
        using range_beyond_length_nat[OF npos, of "length p" i k] by simp
      thus "?f_p k = 0" by simp
    qed
    show ?thesis
      using sum_list_map_upt_extend_zero[OF t_p_le, of ?f_p] zero by simp
  qed

  have sum_r_to_tsum:
    "sum_list (map ?f_r [0..< ?t_sum]) = sum_list (map ?f_r [0..< ?t_r])"
  proof -
    have zero: "\<And>k. ?t_r \<le> k \<Longrightarrow> k < ?t_sum \<Longrightarrow> ?f_r k = 0"
    proof -
      fix k assume kr: "?t_r \<le> k" and _ : "k < ?t_sum"
      have "k \<ge> (length r + n - 1 - i) div n + 1" using kr by simp
      hence "k * n + i \<ge> length r"
        using range_beyond_length_nat[OF npos, of "length r" i k] by simp
      thus "?f_r k = 0" by simp
    qed
    show ?thesis
      using sum_list_map_upt_extend_zero[OF t_r_le, of ?f_r] zero by simp
  qed

  have map_sum:
    "map ?f_sum [0..< ?t_sum] = map (\<lambda>k. ?f_p k + ?f_r k) [0..< ?t_sum]"
  proof (rule map_cong)
    show "[0..< ?t_sum] = [0..< ?t_sum]" by simp
  next
    fix x assume "x \<in> set [0..< ?t_sum]"
    show "?f_sum x = ?f_p x + ?f_r x"
      using f_sum by simp
  qed

  have lhs: "ring_mod_coeff (poly_add p r) n i = sum_list (map ?f_sum [0..< ?t_sum])"
    unfolding ring_mod_coeff_def len_add by simp

  have rhs: "ring_mod_coeff p n i + ring_mod_coeff r n i =
             sum_list (map ?f_p [0..< ?t_p]) + sum_list (map ?f_r [0..< ?t_r])"
    unfolding ring_mod_coeff_def by simp

  have step1: "sum_list (map ?f_sum [0..< ?t_sum]) = sum_list (map (\<lambda>k. ?f_p k + ?f_r k) [0..< ?t_sum])"
    using map_sum by presburger

  have step2: "sum_list (map (\<lambda>k. ?f_p k + ?f_r k) [0..< ?t_sum]) =
               sum_list (map ?f_p [0..< ?t_sum]) + sum_list (map ?f_r [0..< ?t_sum])"
    using sum_map_add_eq .

  have step3: "sum_list (map ?f_p [0..< ?t_sum]) + sum_list (map ?f_r [0..< ?t_sum]) =
               sum_list (map ?f_p [0..< ?t_p]) + sum_list (map ?f_r [0..< ?t_r])"
    using sum_p_to_tsum sum_r_to_tsum by simp

  show ?thesis
    using lhs rhs step1 step2 step3 by simp
qed

lemma ring_mod_add:
  assumes npos: "n > 0"
  shows "ring_mod (poly_add p r) n =
         poly_add (ring_mod p n) (ring_mod r n)"
proof (intro nth_equalityI)
  show "length (ring_mod (poly_add p r) n) =
        length (poly_add (ring_mod p n) (ring_mod r n))"
    using npos by (simp add: ring_mod_length poly_add_length)
next
  fix i assume i_bound: "i < length (ring_mod (poly_add p r) n)"
  hence i_lt_n: "i < n" using npos by (simp add: ring_mod_length)

  have lhs: "(ring_mod (poly_add p r) n) ! i = ring_mod_coeff (poly_add p r) n i"
    using i_lt_n npos unfolding ring_mod_def by simp

  have rhs: "(poly_add (ring_mod p n) (ring_mod r n)) ! i =
             ring_mod_coeff p n i + ring_mod_coeff r n i"
  proof -
    have "(poly_add (ring_mod p n) (ring_mod r n)) ! i =
          poly_coeff (ring_mod p n) i + poly_coeff (ring_mod r n) i"
      using i_lt_n npos by (simp add: poly_add_coeff ring_mod_length poly_add_length)
    also have "... = (ring_mod p n) ! i + (ring_mod r n) ! i"
      using i_lt_n npos unfolding poly_coeff_def by (simp add: ring_mod_length)
    also have "... = ring_mod_coeff p n i + ring_mod_coeff r n i"
      using i_lt_n npos unfolding ring_mod_def by simp
    finally show ?thesis .
  qed

  show "(ring_mod (poly_add p r) n) ! i =
        (poly_add (ring_mod p n) (ring_mod r n)) ! i"
    using lhs rhs ring_mod_coeff_add[OF npos] by simp
qed

(* === Step 8: Ring Multiplication === *)
text \<open>
  Multiplication in R_q = Z_q[X]/(X^n + 1):
  1. Multiply polynomials normally
  2. Reduce modulo X^n + 1
  3. Reduce coefficients modulo q
\<close>

definition ring_mult :: "poly \<Rightarrow> poly \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> poly" where
  "ring_mult p r n q = poly_mod (ring_mod (poly_mult p r) n) q"

lemma ring_mult_length:
  assumes "n > 0"
  shows "length (ring_mult p r n q) = n"
  using assms unfolding ring_mult_def by (simp add: ring_mod_length)

definition ring_add :: "poly \<Rightarrow> poly \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> poly" where
  "ring_add p r n q = poly_mod (ring_mod (poly_add p r) n) q"

lemma ring_add_length:
  assumes "n > 0"
  shows "length (ring_add p r n q) = n"
  using assms unfolding ring_add_def by (simp add: ring_mod_length)

definition ring_sub :: "poly \<Rightarrow> poly \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> poly" where
  "ring_sub p r n q = poly_mod (ring_mod (poly_sub p r) n) q"

lemma ring_sub_length:
  assumes "n > 0"
  shows "length (ring_sub p r n q) = n"
  using assms unfolding ring_sub_def by (simp add: ring_mod_length)

text \<open>
  Ring element validity: correct length and coefficients in [0, q).
\<close>

definition valid_ring_elem :: "poly \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> bool" where
  "valid_ring_elem p n q = (length p = n \<and> (\<forall>a \<in> set p. 0 \<le> a \<and> a < q))"

lemma ring_mult_valid:
  assumes "n > 0" and "q > 0"
  shows "valid_ring_elem (ring_mult p r n q) n q"
  using assms unfolding valid_ring_elem_def ring_mult_def
  by (simp add: ring_mod_length poly_mod_range)

lemma ring_add_valid:
  assumes "n > 0" and "q > 0"
  shows "valid_ring_elem (ring_add p r n q) n q"
  using assms unfolding valid_ring_elem_def ring_add_def
  by (simp add: ring_mod_length poly_mod_range)

(* === Step 8b: Ring Distributivity === *)
text \<open>
  Ring multiplication distributes over ring addition in R_q = Z_q[X]/(X^n + 1):
  a * (b + c) = a*b + a*c (mod X^n + 1, mod q)

  Proof outline:
  1. poly_mult distributes over poly_add (poly_mult_coeff_add_right)
  2. ring_mod distributes over addition (with sign handling for X^n + 1)
  3. poly_mod distributes (via mod_add_eq)
\<close>

text \<open>
  Helper lemma: poly_mod on poly_add of two poly_mod results
  simplifies via mod_add_eq.
\<close>

lemma poly_mod_add_distrib:
  assumes qpos: "q > 0"
  shows "poly_mod (poly_add (poly_mod p q) (poly_mod r q)) q =
         poly_mod (poly_add p r) q"
proof (intro nth_equalityI)
  let ?lhs = "poly_mod (poly_add (poly_mod p q) (poly_mod r q)) q"
  let ?rhs = "poly_mod (poly_add p r) q"
  let ?len = "max (length p) (length r)"

  have len_lhs: "length ?lhs = ?len"
    by (simp add: poly_add_length)
  have len_rhs: "length ?rhs = ?len"
    by (simp add: poly_add_length)

  show "length ?lhs = length ?rhs"
    using len_lhs len_rhs by simp
next
  fix i assume "i < length (poly_mod (poly_add (poly_mod p q) (poly_mod r q)) q)"
  hence i_lt: "i < max (length p) (length r)"
    by (simp add: poly_add_length)

  have lhs_i: "(poly_mod (poly_add (poly_mod p q) (poly_mod r q)) q) ! i =
               (poly_coeff (poly_mod p q) i + poly_coeff (poly_mod r q) i) mod q"
    using i_lt by (simp add: poly_add_coeff poly_add_length poly_mod_def poly_coeff_def)

  have rhs_i: "(poly_mod (poly_add p r) q) ! i =
               (poly_coeff p i + poly_coeff r i) mod q"
    using i_lt by (simp add: poly_add_coeff poly_add_length poly_mod_def poly_coeff_def)

  have "(poly_coeff (poly_mod p q) i + poly_coeff (poly_mod r q) i) mod q =
        ((poly_coeff p i mod q) + (poly_coeff r i mod q)) mod q"
    unfolding poly_coeff_def poly_mod_def using i_lt by auto
  also have "... = (poly_coeff p i + poly_coeff r i) mod q"
    by (simp add: mod_add_eq)
  finally show "(poly_mod (poly_add (poly_mod p q) (poly_mod r q)) q) ! i =
                (poly_mod (poly_add p r) q) ! i"
    using lhs_i rhs_i by simp
qed

text \<open>
  The main distributivity lemma for ring multiplication.
  In R_q = Z_q[X]/(X^n+1), multiplication distributes over addition.
\<close>

lemma ring_mult_add_right:
  assumes npos: "n > 0" and qpos: "q > 0"
  shows "ring_mult a (ring_add b c n q) n q =
         ring_add (ring_mult a b n q) (ring_mult a c n q) n q"
  \<comment> \<open>Distributivity in quotient ring R_q. Requires showing that multiplying
      by the reduced representative (ring_add b c) gives the same result as
      the sum of products. Uses poly_mult_add_right, ring_mod_add, poly_mod properties.
      Full proof requires careful handling of the quotient ring structure.\<close>
  sorry

lemma ring_mult_add_left:
  assumes npos: "n > 0" and qpos: "q > 0"
  shows "ring_mult (ring_add a b n q) c n q =
         ring_add (ring_mult a c n q) (ring_mult b c n q) n q"
  \<comment> \<open>Symmetric to ring_mult_add_right\<close>
  sorry

text \<open>
  Ring addition commutativity and associativity in R_q.
\<close>

lemma ring_add_comm:
  "ring_add p r n q = ring_add r p n q"
  unfolding ring_add_def by (simp add: poly_add_comm)

(* Helper: ring_mod of a polynomial that's already length n *)
lemma ring_mod_already_n:
  assumes npos: "n > 0" and len_n: "length p = n"
  shows "ring_mod p n = p"
proof (intro nth_equalityI)
  show "length (ring_mod p n) = length p"
    using npos len_n by (simp add: ring_mod_length)
next
  fix i assume i_lt: "i < length (ring_mod p n)"
  hence i_lt_n: "i < n" using npos by (simp add: ring_mod_length)

  have rm_nth: "(ring_mod p n) ! i = ring_mod_coeff p n i"
    using i_lt_n npos unfolding ring_mod_def by simp

  have coeff: "ring_mod_coeff p n i = poly_coeff p i"
    using ring_mod_coeff_below_n[OF npos _ i_lt_n] len_n by simp

  show "(ring_mod p n) ! i = p ! i"
    using rm_nth coeff i_lt_n len_n by (simp add: poly_coeff_nth)
qed

(* Helper: poly_mod of poly_add can absorb inner poly_mod on left *)
lemma poly_mod_poly_add_left:
  assumes qpos: "q > 0"
  shows "poly_mod (poly_add (poly_mod a q) b) q = poly_mod (poly_add a b) q"
proof (intro nth_equalityI)
  show "length (poly_mod (poly_add (poly_mod a q) b) q) =
        length (poly_mod (poly_add a b) q)"
    by (simp add: poly_add_length)
next
  fix i assume "i < length (poly_mod (poly_add (poly_mod a q) b) q)"
  hence i_lt: "i < max (length a) (length b)"
    by (simp add: poly_add_length)

  have lhs: "(poly_mod (poly_add (poly_mod a q) b) q) ! i =
             (poly_coeff (poly_mod a q) i + poly_coeff b i) mod q"
    using i_lt by (simp add: poly_mod_def poly_add_coeff poly_add_length poly_coeff_def)

  have rhs: "(poly_mod (poly_add a b) q) ! i =
             (poly_coeff a i + poly_coeff b i) mod q"
    using i_lt by (simp add: poly_mod_def poly_add_coeff poly_add_length poly_coeff_def)

  have "poly_coeff (poly_mod a q) i = (poly_coeff a i) mod q"
    unfolding poly_coeff_def poly_mod_def by auto

  hence "(poly_coeff (poly_mod a q) i + poly_coeff b i) mod q =
         ((poly_coeff a i mod q) + poly_coeff b i) mod q"
    by simp
  also have "... = (poly_coeff a i + poly_coeff b i) mod q"
    by (simp add: mod_add_left_eq)
  finally show "(poly_mod (poly_add (poly_mod a q) b) q) ! i =
                (poly_mod (poly_add a b) q) ! i"
    using lhs rhs by simp
qed

(* Symmetric version for right *)
lemma poly_mod_poly_add_right:
  assumes qpos: "q > 0"
  shows "poly_mod (poly_add a (poly_mod b q)) q = poly_mod (poly_add a b) q"
  using poly_mod_poly_add_left[OF qpos] poly_add_comm by metis

lemma ring_add_assoc:
  assumes npos: "n > 0" and qpos: "q > 0"
  shows "ring_add (ring_add p r n q) s n q = ring_add p (ring_add r s n q) n q"
proof -
  let ?pr = "ring_add p r n q"
  let ?rs = "ring_add r s n q"

  have len_pr: "length ?pr = n" using ring_add_length[OF npos] .
  have len_rs: "length ?rs = n" using ring_add_length[OF npos] .

  (* LHS expansion *)
  have lhs: "ring_add ?pr s n q = poly_mod (ring_mod (poly_add ?pr s) n) q"
    unfolding ring_add_def ..

  (* Use ring_mod_add to expand *)
  have "ring_mod (poly_add ?pr s) n = poly_add (ring_mod ?pr n) (ring_mod s n)"
    using ring_mod_add[OF npos] .
  also have "... = poly_add ?pr (ring_mod s n)"
    using ring_mod_already_n[OF npos len_pr] by simp
  finally have lhs_rm: "ring_mod (poly_add ?pr s) n = poly_add ?pr (ring_mod s n)" .

  (* Expand ?pr *)
  have pr_def: "?pr = poly_mod (ring_mod (poly_add p r) n) q"
    unfolding ring_add_def ..

  (* LHS = poly_mod (poly_add (poly_mod (...) q) (ring_mod s n)) q *)
  have lhs_full: "ring_add ?pr s n q =
                  poly_mod (poly_add (poly_mod (ring_mod (poly_add p r) n) q) (ring_mod s n)) q"
    using lhs lhs_rm pr_def by simp

  (* Use poly_mod_poly_add_left to remove inner poly_mod *)
  have lhs_simp: "ring_add ?pr s n q =
                  poly_mod (poly_add (ring_mod (poly_add p r) n) (ring_mod s n)) q"
    using lhs_full poly_mod_poly_add_left[OF qpos] by simp

  (* RHS expansion *)
  have rhs: "ring_add p ?rs n q = poly_mod (ring_mod (poly_add p ?rs) n) q"
    unfolding ring_add_def ..

  have "ring_mod (poly_add p ?rs) n = poly_add (ring_mod p n) (ring_mod ?rs n)"
    using ring_mod_add[OF npos] .
  also have "... = poly_add (ring_mod p n) ?rs"
    using ring_mod_already_n[OF npos len_rs] by simp
  finally have rhs_rm: "ring_mod (poly_add p ?rs) n = poly_add (ring_mod p n) ?rs" .

  have rs_def: "?rs = poly_mod (ring_mod (poly_add r s) n) q"
    unfolding ring_add_def ..

  have rhs_full: "ring_add p ?rs n q =
                  poly_mod (poly_add (ring_mod p n) (poly_mod (ring_mod (poly_add r s) n) q)) q"
    using rhs rhs_rm rs_def by simp

  have rhs_simp: "ring_add p ?rs n q =
                  poly_mod (poly_add (ring_mod p n) (ring_mod (poly_add r s) n)) q"
    using rhs_full poly_mod_poly_add_right[OF qpos] by simp

  (* Use ring_mod_add on both sides *)
  have "ring_mod (poly_add p r) n = poly_add (ring_mod p n) (ring_mod r n)"
    using ring_mod_add[OF npos] .
  hence lhs_inner: "poly_add (ring_mod (poly_add p r) n) (ring_mod s n) =
                    poly_add (poly_add (ring_mod p n) (ring_mod r n)) (ring_mod s n)"
    by simp

  have "ring_mod (poly_add r s) n = poly_add (ring_mod r n) (ring_mod s n)"
    using ring_mod_add[OF npos] .
  hence rhs_inner: "poly_add (ring_mod p n) (ring_mod (poly_add r s) n) =
                    poly_add (ring_mod p n) (poly_add (ring_mod r n) (ring_mod s n))"
    by simp

  (* Now use poly_add_assoc *)
  have assoc: "poly_add (poly_add (ring_mod p n) (ring_mod r n)) (ring_mod s n) =
               poly_add (ring_mod p n) (poly_add (ring_mod r n) (ring_mod s n))"
    using poly_add_assoc .

  show ?thesis
    using lhs_simp rhs_simp lhs_inner rhs_inner assoc by simp
qed

(* Helper: 4-term ring_add shuffle: (a + b) + (c + d) = (a + c) + (b + d) *)
lemma ring_add_four_shuffle:
  assumes npos: "n > 0" and qpos: "q > 0"
  shows "ring_add (ring_add a b n q) (ring_add c d n q) n q =
         ring_add (ring_add a c n q) (ring_add b d n q) n q"
proof -
  have step1: "ring_add (ring_add a b n q) (ring_add c d n q) n q =
               ring_add a (ring_add b (ring_add c d n q) n q) n q"
    using ring_add_assoc[OF npos qpos] by simp
  have step2: "ring_add b (ring_add c d n q) n q =
               ring_add (ring_add b c n q) d n q"
    using ring_add_assoc[OF npos qpos] by simp
  have step3: "ring_add b c n q = ring_add c b n q"
    using ring_add_comm by simp
  have step4: "ring_add (ring_add c b n q) d n q =
               ring_add c (ring_add b d n q) n q"
    using ring_add_assoc[OF npos qpos] by simp
  have step5: "ring_add a (ring_add c (ring_add b d n q) n q) n q =
               ring_add (ring_add a c n q) (ring_add b d n q) n q"
    using ring_add_assoc[OF npos qpos] by simp
  show ?thesis using step1 step2 step3 step4 step5 by simp
qed

(* === Step 9: Ring Parameters Record === *)
text \<open>
  Ring parameters for R_q = Z_q[X]/(X^n + 1).

  For efficiency with NTT, n is typically a power of 2.
  For security, q is chosen based on SIS/LWE parameters.
\<close>

record ring_params =
  ring_n :: nat
  ring_q :: int

definition valid_ring_params :: "ring_params \<Rightarrow> bool" where
  "valid_ring_params rp = (ring_n rp > 0 \<and> ring_q rp > 1)"

lemma valid_ring_params_pos:
  assumes "valid_ring_params rp"
  shows "ring_n rp > 0" "ring_q rp > 1"
  using assms unfolding valid_ring_params_def by auto

text \<open>Ring context locale for cleaner proofs.\<close>

locale ring_context =
  fixes rp :: ring_params
  assumes params_ok: "valid_ring_params rp"
begin

abbreviation "n \<equiv> ring_n rp"
abbreviation "q \<equiv> ring_q rp"

lemma n_pos: "n > 0"
  using params_ok unfolding valid_ring_params_def by simp

lemma q_pos: "q > 1"
  using params_ok unfolding valid_ring_params_def by simp

definition "ring_zero \<equiv> replicate n 0"
definition "ring_one \<equiv> 1 # replicate (n - 1) 0"

lemma ring_zero_valid: "valid_ring_elem ring_zero n q"
  unfolding valid_ring_elem_def ring_zero_def using q_pos by auto

lemma ring_one_valid: "valid_ring_elem ring_one n q"
  unfolding valid_ring_elem_def ring_one_def using n_pos q_pos by auto

definition rmult :: "poly \<Rightarrow> poly \<Rightarrow> poly" where
  "rmult p r = ring_mult p r n q"

definition radd :: "poly \<Rightarrow> poly \<Rightarrow> poly" where
  "radd p r = ring_add p r n q"

definition rsub :: "poly \<Rightarrow> poly \<Rightarrow> poly" where
  "rsub p r = ring_sub p r n q"

end

(* === Step 10: Code Export === *)
export_code
  zero_poly const_poly poly_degree poly_coeff
  poly_add poly_neg poly_sub
  poly_scale poly_mult poly_mult_coeff
  poly_mod ring_mod ring_mod_coeff
  centered_coeff poly_centered
  ring_mult ring_add ring_sub
  ring_params.make valid_ring_params valid_ring_elem
  ring_n ring_q
  in Haskell module_name "Canon.Rings.PolyMod"

end
