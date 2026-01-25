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
  ring_mult ring_add ring_sub
  ring_params.make valid_ring_params valid_ring_elem
  ring_n ring_q
  in Haskell module_name "Canon.Rings.PolyMod"

end
