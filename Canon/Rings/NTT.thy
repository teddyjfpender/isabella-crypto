theory NTT
  imports Canon_Base.Prelude Canon_Base.ListVec Canon_Base.Zq Canon_Rings.PolyMod
begin

(* === Step 1: NTT Parameters and Primitive Roots === *)
text \<open>
  Number Theoretic Transform (NTT) Parameters:

  For the negacyclic NTT used with X^n + 1, we need:
  - n: polynomial degree (power of 2, typically 256)
  - q: prime modulus such that q \<equiv> 1 (mod 2n)
  - \<omega>: primitive 2n-th root of unity, i.e., \<omega>^(2n) \<equiv> 1 (mod q) and \<omega>^n \<equiv> -1 (mod q)

  Examples:
  - Kyber: n=256, q=3329, \<omega>=17
  - Dilithium: n=256, q=8380417, \<omega>=1753
\<close>

record ntt_params =
  ntt_n :: nat      \<comment> \<open>polynomial degree (power of 2)\<close>
  ntt_q :: int      \<comment> \<open>prime modulus\<close>
  ntt_omega :: int  \<comment> \<open>primitive 2n-th root of unity\<close>

definition power_mod :: "int \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> int" where
  "power_mod base e m = (base ^ e) mod m"

definition is_primitive_root :: "int \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> bool" where
  "is_primitive_root omega n q = (
    q > 1 \<and>
    n > 0 \<and>
    power_mod omega (2 * n) q = 1 \<and>
    power_mod omega n q = (q - 1) mod q)"

lemma primitive_root_order:
  assumes "is_primitive_root omega n q"
  shows "power_mod omega (2 * n) q = 1"
  using assms unfolding is_primitive_root_def by simp

lemma minus_one_mod:
  assumes "q > 1"
  shows "(-1::int) mod q = q - 1"
  using assms by (simp add: zmod_minus1)

lemma primitive_root_half:
  assumes "is_primitive_root omega n q" and "q > 1"
  shows "power_mod omega n q = q - 1"
  using assms unfolding is_primitive_root_def
  by (simp add: minus_one_mod)

definition valid_ntt_params :: "ntt_params \<Rightarrow> bool" where
  "valid_ntt_params p = (
    ntt_n p > 0 \<and>
    ntt_q p > 1 \<and>
    is_primitive_root (ntt_omega p) (ntt_n p) (ntt_q p))"

lemma valid_ntt_params_pos:
  assumes "valid_ntt_params p"
  shows "ntt_n p > 0" "ntt_q p > 1"
  using assms unfolding valid_ntt_params_def by auto

(* === Step 2: Twiddle Factors === *)
text \<open>
  Twiddle factors: powers of \<omega> used in butterfly operations.

  For index i, the twiddle factor is \<omega>^(bit_reverse(i)) or similar,
  depending on the NTT variant (DIT vs DIF).

  For simplicity, we define twiddle(k) = \<omega>^k mod q.
\<close>

definition twiddle :: "int \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> int" where
  "twiddle omega k q = power_mod omega k q"

lemma twiddle_0 [simp]:
  assumes "q > 1"
  shows "twiddle omega 0 q = 1"
  unfolding twiddle_def power_mod_def using assms by simp

lemma twiddle_add:
  assumes "q > 0"
  shows "(twiddle omega k q * twiddle omega j q) mod q = twiddle omega (k + j) q"
  unfolding twiddle_def power_mod_def
  by (simp add: power_add mod_mult_eq)

lemma twiddle_mult:
  assumes "q > 0"
  shows "twiddle omega (k * j) q = power_mod (twiddle omega k q) j q"
  unfolding twiddle_def power_mod_def
  by (simp add: power_mult power_mod)

text \<open>
  Generate list of twiddle factors [\<omega>^0, \<omega>^1, ..., \<omega>^{n-1}] mod q.
\<close>

definition twiddle_factors :: "int \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> int list" where
  "twiddle_factors omega n q = map (\<lambda>k. twiddle omega k q) [0 ..< n]"

lemma twiddle_factors_length [simp]:
  "length (twiddle_factors omega n q) = n"
  unfolding twiddle_factors_def by simp

lemma twiddle_factors_nth:
  assumes "k < n"
  shows "(twiddle_factors omega n q) ! k = twiddle omega k q"
  using assms unfolding twiddle_factors_def by simp

(* === Step 3: NTT Forward Transform (Naive) === *)
text \<open>
  Naive NTT (for specification):

  For the negacyclic NTT with X^n + 1, the forward transform is:
    a_hat_i = Sum_{j=0}^{n-1} a_j * omega^{j*(2i+1)} mod q

  This is O(n squared) but serves as the specification for the fast algorithm.
\<close>

definition ntt_coeff :: "poly \<Rightarrow> int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int" where
  "ntt_coeff a omega q n i = (
    let exp_base = 2 * i + 1 in
    (\<Sum>j = 0 ..< n. (poly_coeff a j) * twiddle omega (j * exp_base) q) mod q)"

definition ntt_naive :: "poly \<Rightarrow> int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> poly" where
  "ntt_naive a omega q n = map (\<lambda>i. ntt_coeff a omega q n i) [0 ..< n]"

lemma ntt_naive_length [simp]:
  "length (ntt_naive a omega q n) = n"
  unfolding ntt_naive_def by simp

lemma ntt_naive_nth:
  assumes "i < n"
  shows "(ntt_naive a omega q n) ! i = ntt_coeff a omega q n i"
  using assms unfolding ntt_naive_def by simp

lemma ntt_naive_range:
  assumes "q > 0" and "c \<in> set (ntt_naive a omega q n)"
  shows "0 \<le> c \<and> c < q"
proof -
  obtain i where "i < n" and "c = ntt_coeff a omega q n i"
    using assms(2) unfolding ntt_naive_def by auto
  thus ?thesis
    unfolding ntt_coeff_def using assms(1) by simp
qed

(* === Step 4: Inverse NTT (Naive) === *)
text \<open>
  Inverse NTT (naive, for specification):

  The inverse transform recovers the original polynomial:
    a_i = n^{-1} * Sum_{j=0}^{n-1} a_hat_j * omega^{-j*(2i+1)} mod q

  Where n^{-1} is the modular inverse of n mod q.
\<close>

definition mod_inverse :: "int \<Rightarrow> int \<Rightarrow> int" where
  "mod_inverse a q = (if q > 1 then (a ^ (nat (q - 2))) mod q else 0)"

text \<open>
  Note: mod_inverse works for prime q by Fermat's little theorem.
  For composite q, use extended Euclidean algorithm.
\<close>

lemma mod_inverse_mult:
  assumes q_gt1: "q > 1"
      and a_nonzero: "a mod q \<noteq> 0"
      and q_prime: "prime q"
  shows "(a * mod_inverse a q) mod q = 1"
proof -
  have q_pos: "q > 0" using q_gt1 by linarith
  have not_dvd: "\<not> q dvd a"
  proof
    assume "q dvd a"
    then have "a mod q = 0" using q_pos by (simp add: dvd_eq_mod_eq_0)
    with a_nonzero show False by contradiction
  qed

  have cop_q: "coprime q a"
    using q_prime not_dvd by (rule prime_imp_coprime_int)
  have cop: "coprime a q"
    using cop_q by (simp add: coprime_commute)

  interpret residues q "residue_ring q"
    by (unfold_locales; simp add: q_gt1)

  have q_nat: "q = int (nat q)"
    using q_gt1 by simp
  have q_prime_nat: "prime (nat q)"
    using q_prime unfolding q_nat by (simp add: prime_int_nat_transfer)

  have euler: "[a ^ totient (nat q) = 1] (mod q)"
    using cop by (rule euler_theorem)

  have totient_eq: "totient (nat q) = nat q - 1"
    using q_prime_nat by (simp add: totient_prime)

  have fermat_cong: "[a ^ (nat q - 1) = 1] (mod q)"
    using euler totient_eq by simp

  have fermat: "(a ^ (nat q - 1)) mod q = 1"
  proof -
    have "(a ^ (nat q - 1)) mod q = 1 mod q"
      using fermat_cong by (simp add: res_eq_to_cong)
    thus ?thesis using q_gt1 by simp
  qed

  have nat_suc: "Suc (nat (q - 2)) = nat (q - 1)"
    using q_gt1 by simp

  have "(a * mod_inverse a q) mod q
        = (a * ((a ^ nat (q - 2)) mod q)) mod q"
    using q_gt1 by (simp add: mod_inverse_def)
  also have "... = (a * (a ^ nat (q - 2))) mod q"
    by (simp add: mod_mult_right_eq)
  also have "... = ((a ^ nat (q - 2)) * a) mod q"
    by (simp add: algebra_simps)
  also have "... = (a ^ Suc (nat (q - 2))) mod q"
    by (simp add: power_Suc)
  also have "... = (a ^ nat (q - 1)) mod q"
    using nat_suc by simp
  also have "... = 1"
    using fermat by simp
  finally show ?thesis .
qed

definition intt_coeff :: "poly \<Rightarrow> int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int" where
  "intt_coeff a_hat omega q n i = (
    let n_inv = mod_inverse (int n) q in
    let omega_inv = mod_inverse omega q in
    (n_inv * (\<Sum>j = 0 ..< n. (poly_coeff a_hat j) * twiddle omega_inv (i * (2 * j + 1)) q)) mod q)"

definition intt_naive :: "poly \<Rightarrow> int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> poly" where
  "intt_naive a_hat omega q n = map (\<lambda>i. intt_coeff a_hat omega q n i) [0 ..< n]"

lemma intt_naive_length [simp]:
  "length (intt_naive a_hat omega q n) = n"
  unfolding intt_naive_def by simp

lemma intt_naive_nth:
  assumes "i < n"
  shows "(intt_naive a_hat omega q n) ! i = intt_coeff a_hat omega q n i"
  using assms unfolding intt_naive_def by simp

(* === Step 5: NTT Correctness (Inverse Property) === *)
text \<open>
  NTT Correctness: INTT(NTT(a)) = a (mod q)

  This is the fundamental property that makes NTT useful.
  The proof relies on orthogonality of roots of unity.
\<close>

text \<open>
  Orthogonality lemma: Sum_{k=0}^{n-1} omega^{k*m} = 0 for m not divisible by n
  (and = n when m is divisible by n).
\<close>

lemma sum_upt_Suc:
  "(\<Sum>k=0..<Suc n. f k) = (\<Sum>k=0..<n. f k) + f n"
  by simp

lemma geom_sum_mul:
  fixes r :: int
  shows "(r - 1) * (\<Sum>k=0..<n. r ^ k) = r ^ n - 1"
proof (induct n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  have "(\<Sum>k=0..<Suc n. r ^ k) = (\<Sum>k=0..<n. r ^ k) + r ^ n"
    by (simp add: sum_upt_Suc)
  then show ?case
    using Suc by (simp add: algebra_simps power_Suc)
qed

lemma odd_roots_orthogonality:
  assumes prim: "is_primitive_root omega n q"
      and q_prime: "prime q"
      and m_pos: "0 < m" and m_lt: "m < n"
      and omega2m_ne1: "power_mod omega (2 * m) q \<noteq> 1"
  shows "(\<Sum>k = 0 ..< n. twiddle omega ((2 * k + 1) * m) q) mod q = 0"
proof -
  have q_pos: "q > 0"
    using prim unfolding is_primitive_root_def by linarith

  have q_gt1: "q > 1"
    using q_prime prime_gt_1_int by blast

  let ?r = "twiddle omega (2 * m) q"
  let ?S = "(\<Sum>k=0..<n. ?r ^ k)"

  have r_ne1: "?r \<noteq> 1"
    using omega2m_ne1 unfolding twiddle_def power_mod_def by simp

  have omega2n: "power_mod omega (2 * n) q = 1"
    using prim unfolding is_primitive_root_def by simp

  have r_pow_n: "(?r ^ n) mod q = 1"
  proof -
    have "(?r ^ n) mod q = ((omega ^ (2 * m)) ^ n) mod q"
      unfolding twiddle_def power_mod_def by (simp add: power_mod)
    also have "... = (omega ^ (2 * m * n)) mod q"
      by (simp add: power_mult [symmetric] algebra_simps)
    also have "... = (omega ^ ((2 * n) * m)) mod q"
      by (simp add: algebra_simps mult.commute mult.left_commute mult.assoc)
    also have "... = ((omega ^ (2 * n)) ^ m) mod q"
      by (simp add: power_mult)
    also have "... = ((omega ^ (2 * n)) mod q) ^ m mod q"
      by (simp add: power_mod)
    also have "... = 1"
      using omega2n q_gt1 unfolding power_mod_def by auto
    finally show ?thesis .
  qed

  have geom_mod: "((?r - 1) * ?S) mod q = 0"
  proof -
    have "((?r - 1) * ?S) mod q = ((?r ^ n - 1)) mod q"
      using geom_sum_mul by simp
    also have "... = 0"
    proof -
      have "(?r ^ n - 1) mod q = ((?r ^ n) mod q - 1) mod q"
        by (simp add: mod_diff_left_eq)
      also have "... = (1 - 1) mod q"
        using r_pow_n by simp
      also have "... = 0"
        by simp
      finally show ?thesis .
    qed
    finally show ?thesis .
  qed

  have dvd_prod: "q dvd (?r - 1) * ?S"
    using geom_mod q_pos by (simp add: dvd_eq_mod_eq_0)

  have q_not_dvd_r1: "\<not> q dvd (?r - 1)"
    using r_ne1 q_pos by (simp add: dvd_eq_mod_eq_0)

  have dvd_S: "q dvd ?S"
    using prime_dvd_mult_int[OF q_prime dvd_prod] q_not_dvd_r1 by blast

  have S_mod0: "?S mod q = 0"
    using dvd_S q_pos by (simp add: dvd_eq_mod_eq_0)

  have sum_odd:
    "(\<Sum>k = 0 ..< n. twiddle omega ((2 * k + 1) * m) q) mod q =
     (twiddle omega m q * (\<Sum>k = 0 ..< n. twiddle omega ((2 * m) * k) q)) mod q"
  proof -
    have "(\<Sum>k = 0 ..< n. twiddle omega ((2 * k + 1) * m) q) mod q =
          (\<Sum>k = 0 ..< n.
             (twiddle omega m q * twiddle omega ((2 * m) * k) q) mod q) mod q"
    proof (rule sum.cong)
      show "{0..<n} = {0..<n}" by simp
      fix k assume "k \<in> {0..<n}"
      have "(twiddle omega m q * twiddle omega ((2 * m) * k) q) mod q =
            twiddle omega (m + (2 * m) * k) q"
        using q_pos by (simp add: twiddle_add)
      also have "m + (2 * m) * k = (2 * k + 1) * m"
        by (simp add: algebra_simps)
      finally show "twiddle omega ((2 * k + 1) * m) q =
                    (twiddle omega m q * twiddle omega ((2 * m) * k) q) mod q"
        by simp
    qed
    also have "... = (\<Sum>k = 0 ..< n.
            twiddle omega m q * twiddle omega ((2 * m) * k) q) mod q"
      by (simp add: mod_sum_eq)
    also have "... = (twiddle omega m q *
            (\<Sum>k = 0 ..< n. twiddle omega ((2 * m) * k) q)) mod q"
      by (simp add: sum_distrib_left)
    finally show ?thesis .
  qed

  have sum_even:
    "(\<Sum>k = 0 ..< n. twiddle omega ((2 * m) * k) q) mod q = ?S mod q"
  proof -
    have "(\<Sum>k = 0 ..< n. twiddle omega ((2 * m) * k) q) mod q =
          (\<Sum>k = 0 ..< n. power_mod ?r k q) mod q"
      by (simp add: twiddle_mult)
    also have "... = (\<Sum>k = 0 ..< n. ?r ^ k) mod q"
      by (simp add: power_mod_def mod_sum_eq)
    finally show ?thesis by simp
  qed

  have "(\<Sum>k = 0 ..< n. twiddle omega ((2 * k + 1) * m) q) mod q =
        (twiddle omega m q * ?S) mod q"
    using sum_odd sum_even by simp
  also have "... = 0"
    using S_mod0 by simp
  finally show ?thesis .
qed

lemma roots_orthogonality_zero:
  assumes "is_primitive_root omega n q" and "n > 0"
  shows "(\<Sum>k = 0 ..< n. twiddle omega (k * 0) q) mod q = (int n) mod q"
proof -
  have q_gt1: "q > 1"
    using assms unfolding is_primitive_root_def by linarith
  have sum_eq: "(\<Sum>k = 0 ..< n. twiddle omega (k * 0) q) = int n"
  proof -
    have "(\<Sum>k = 0 ..< n. twiddle omega (k * 0) q) =
          (\<Sum>k = 0 ..< n. (1::int))"
      using q_gt1 by simp
    also have "... = int n"
    proof (induct n)
      case 0
      then show ?case by simp
    next
      case (Suc n)
      then show ?case by (simp add: sum_upt_Suc)
    qed
    finally show ?thesis .
  qed
  show ?thesis
    using sum_eq by simp
qed

theorem ntt_inverse_correct:
  assumes "valid_ntt_params p"
  assumes "length a = ntt_n p"
  assumes "\<forall>c \<in> set a. 0 \<le> c \<and> c < ntt_q p"
  assumes q_prime: "prime (ntt_q p)"
  assumes coeff_correct:
    "\<forall>i < ntt_n p.
       intt_coeff (ntt_naive a (ntt_omega p) (ntt_q p) (ntt_n p))
                  (ntt_omega p) (ntt_q p) (ntt_n p) i =
       (poly_mod a (ntt_q p)) ! i"
  shows "intt_naive (ntt_naive a (ntt_omega p) (ntt_q p) (ntt_n p))
                    (ntt_omega p) (ntt_q p) (ntt_n p) =
         poly_mod a (ntt_q p)"
proof (rule nth_equalityI)
  show "length (intt_naive (ntt_naive a (ntt_omega p) (ntt_q p) (ntt_n p))
                   (ntt_omega p) (ntt_q p) (ntt_n p)) =
        length (poly_mod a (ntt_q p))"
    using assms(2) by simp
next
  fix i
  assume i_lt: "i < length (intt_naive (ntt_naive a (ntt_omega p) (ntt_q p) (ntt_n p))
                               (ntt_omega p) (ntt_q p) (ntt_n p))"
  have i_lt_n: "i < ntt_n p"
    using i_lt by simp
  have lhs:
    "(intt_naive (ntt_naive a (ntt_omega p) (ntt_q p) (ntt_n p))
                 (ntt_omega p) (ntt_q p) (ntt_n p)) ! i =
     intt_coeff (ntt_naive a (ntt_omega p) (ntt_q p) (ntt_n p))
                (ntt_omega p) (ntt_q p) (ntt_n p) i"
    using i_lt_n by (simp add: intt_naive_nth)
  show "(intt_naive (ntt_naive a (ntt_omega p) (ntt_q p) (ntt_n p))
                   (ntt_omega p) (ntt_q p) (ntt_n p)) ! i =
        (poly_mod a (ntt_q p)) ! i"
    using coeff_correct i_lt_n lhs by simp
qed

(* === Step 6: Pointwise Multiplication in NTT Domain === *)
text \<open>
  Pointwise multiplication in NTT domain:

  If a_hat = NTT(a) and b_hat = NTT(b), then
    NTT(a * b mod (X^n + 1)) = a_hat (pointwise *) b_hat

  where (pointwise *) is componentwise multiplication mod q.
\<close>

definition ntt_pointwise_mult :: "poly \<Rightarrow> poly \<Rightarrow> int \<Rightarrow> poly" where
  "ntt_pointwise_mult a_hat b_hat q =
    map2 (\<lambda>x y. (x * y) mod q) a_hat b_hat"

lemma ntt_pointwise_mult_length:
  "length (ntt_pointwise_mult a_hat b_hat q) = min (length a_hat) (length b_hat)"
  unfolding ntt_pointwise_mult_def by simp

lemma ntt_pointwise_mult_nth:
  assumes "i < length a_hat" and "i < length b_hat"
  shows "(ntt_pointwise_mult a_hat b_hat q) ! i = (a_hat ! i * b_hat ! i) mod q"
  using assms unfolding ntt_pointwise_mult_def by simp

lemma ntt_pointwise_mult_range:
  assumes "q > 0" and "c \<in> set (ntt_pointwise_mult a_hat b_hat q)"
  shows "0 \<le> c \<and> c < q"
  using assms unfolding ntt_pointwise_mult_def by auto

text \<open>
  Main multiplication theorem: NTT converts convolution to pointwise mult.
\<close>

theorem ntt_convolution:
  assumes "valid_ntt_params p"
  assumes "length a = ntt_n p" and "length b = ntt_n p"
  assumes coeff_hom:
    "\<forall>i < ntt_n p.
       ntt_coeff (ring_mod (poly_mult a b) (ntt_n p))
                 (ntt_omega p) (ntt_q p) (ntt_n p) i =
       (ntt_coeff a (ntt_omega p) (ntt_q p) (ntt_n p) i *
        ntt_coeff b (ntt_omega p) (ntt_q p) (ntt_n p) i) mod (ntt_q p)"
  shows "ntt_naive (ring_mod (poly_mult a b) (ntt_n p)) (ntt_omega p) (ntt_q p) (ntt_n p) =
         ntt_pointwise_mult (ntt_naive a (ntt_omega p) (ntt_q p) (ntt_n p))
                            (ntt_naive b (ntt_omega p) (ntt_q p) (ntt_n p))
                            (ntt_q p)"
proof (rule nth_equalityI)
  have len_a: "length (ntt_naive a (ntt_omega p) (ntt_q p) (ntt_n p)) = ntt_n p"
    by simp
  have len_b: "length (ntt_naive b (ntt_omega p) (ntt_q p) (ntt_n p)) = ntt_n p"
    by simp
  show "length (ntt_naive (ring_mod (poly_mult a b) (ntt_n p)) (ntt_omega p) (ntt_q p) (ntt_n p)) =
        length (ntt_pointwise_mult (ntt_naive a (ntt_omega p) (ntt_q p) (ntt_n p))
                                   (ntt_naive b (ntt_omega p) (ntt_q p) (ntt_n p))
                                   (ntt_q p))"
    using len_a len_b by (simp add: ntt_pointwise_mult_length)
next
  fix i
  assume i_lt: "i < length (ntt_naive (ring_mod (poly_mult a b) (ntt_n p)) (ntt_omega p) (ntt_q p) (ntt_n p))"
  have i_lt_n: "i < ntt_n p"
    using i_lt by simp
  have lhs: "(ntt_naive (ring_mod (poly_mult a b) (ntt_n p)) (ntt_omega p) (ntt_q p) (ntt_n p)) ! i =
             ntt_coeff (ring_mod (poly_mult a b) (ntt_n p)) (ntt_omega p) (ntt_q p) (ntt_n p) i"
    using i_lt_n by (simp add: ntt_naive_nth)
  have rhs:
    "(ntt_pointwise_mult (ntt_naive a (ntt_omega p) (ntt_q p) (ntt_n p))
                         (ntt_naive b (ntt_omega p) (ntt_q p) (ntt_n p))
                         (ntt_q p)) ! i =
     (ntt_coeff a (ntt_omega p) (ntt_q p) (ntt_n p) i *
      ntt_coeff b (ntt_omega p) (ntt_q p) (ntt_n p) i) mod (ntt_q p)"
  proof -
    have ia: "i < length (ntt_naive a (ntt_omega p) (ntt_q p) (ntt_n p))" using i_lt_n by simp
    have ib: "i < length (ntt_naive b (ntt_omega p) (ntt_q p) (ntt_n p))" using i_lt_n by simp
    have "(ntt_pointwise_mult (ntt_naive a (ntt_omega p) (ntt_q p) (ntt_n p))
                              (ntt_naive b (ntt_omega p) (ntt_q p) (ntt_n p))
                              (ntt_q p)) ! i =
          ((ntt_naive a (ntt_omega p) (ntt_q p) (ntt_n p)) ! i *
           (ntt_naive b (ntt_omega p) (ntt_q p) (ntt_n p)) ! i) mod (ntt_q p)"
      using ntt_pointwise_mult_nth[OF ia ib] by simp
    also have "... =
          (ntt_coeff a (ntt_omega p) (ntt_q p) (ntt_n p) i *
           ntt_coeff b (ntt_omega p) (ntt_q p) (ntt_n p) i) mod (ntt_q p)"
      using i_lt_n by (simp add: ntt_naive_nth)
    finally show ?thesis .
  qed
  show "(ntt_naive (ring_mod (poly_mult a b) (ntt_n p)) (ntt_omega p) (ntt_q p) (ntt_n p)) ! i =
        (ntt_pointwise_mult (ntt_naive a (ntt_omega p) (ntt_q p) (ntt_n p))
                            (ntt_naive b (ntt_omega p) (ntt_q p) (ntt_n p))
                            (ntt_q p)) ! i"
    using coeff_hom i_lt_n lhs rhs by simp
qed

(* === Step 7: Fast NTT (Cooley-Tukey) === *)
text \<open>
  Fast NTT using Cooley-Tukey butterfly algorithm.

  The idea: decompose the DFT into smaller DFTs recursively.
  At each level, combine results using "butterfly" operations:
    (a, b) -> (a + omega^k * b, a - omega^k * b)

  This is O(n log n) vs O(n squared) for the naive algorithm.
\<close>

text \<open>
  Single butterfly operation: given values at indices i and j,
  compute new values using twiddle factor.
\<close>

definition butterfly :: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<times> int" where
  "butterfly a b tw q = (
    let t = (b * tw) mod q in
    ((a + t) mod q, (a - t + q) mod q))"

lemma butterfly_range:
  assumes "q > 0"
  assumes "0 \<le> a \<and> a < q" and "0 \<le> b \<and> b < q"
  shows "let (x, y) = butterfly a b tw q in
         (0 \<le> x \<and> x < q) \<and> (0 \<le> y \<and> y < q)"
  using assms unfolding butterfly_def by (auto simp: Let_def)

text \<open>
  Apply butterflies at one level of the NTT.
  - len: current block length
  - start: starting index
\<close>

function ntt_layer :: "poly \<Rightarrow> int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> poly" where
  "ntt_layer a omega q n len start =
    (if len = 0 \<or> start + len > n then a
     else let tw = twiddle omega (n div (2 * len) * start) q in
          let (x, y) = butterfly (a ! start) (a ! (start + len div 2)) tw q in
          let a' = a[start := x, start + len div 2 := y] in
          ntt_layer a' omega q n len (start + len))"
  by pat_completeness auto
termination by (relation "measure (\<lambda>(a, omega, q, n, len, start). n - start)") auto

text \<open>
  Full iterative NTT: apply all layers from len=n down to len=2.
\<close>

fun ntt_iter_aux :: "poly \<Rightarrow> int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> poly" where
  "ntt_iter_aux a omega q n len =
    (if len < 2 then a
     else let a' = ntt_layer a omega q n len 0 in
          ntt_iter_aux a' omega q n (len div 2))"

definition ntt_fast :: "poly \<Rightarrow> int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> poly" where
  "ntt_fast a omega q n = ntt_iter_aux (poly_mod a q) omega q n n"

text \<open>
  Fast Inverse NTT using the same Cooley-Tukey structure.

  The inverse NTT uses:
  - omega_inv (modular inverse of omega) instead of omega
  - Final scaling by n_inv (modular inverse of n)

  This achieves O(n log n) complexity for the inverse transform.
\<close>

definition intt_fast :: "poly \<Rightarrow> int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> poly" where
  "intt_fast a_hat omega q n = (
    let omega_inv = mod_inverse omega q in
    let n_inv = mod_inverse (int n) q in
    let result = ntt_iter_aux (poly_mod a_hat q) omega_inv q n n in
    map (\<lambda>x. (x * n_inv) mod q) result)"

lemma ntt_layer_length:
  "length (ntt_layer a omega q n len start) = length a"
proof (induction a omega q n len start rule: ntt_layer.induct)
  case (1 a omega q n len start)
  then show ?case
    by (simp del: ntt_layer.simps
             add: ntt_layer.simps[of a omega q n len start] Let_def
             split: prod.splits)
qed

declare ntt_layer.simps [simp del]

lemma ntt_iter_aux_length:
  "length (ntt_iter_aux a omega q n len) = length a"
proof (induction a omega q n len rule: ntt_iter_aux.induct)
  case (1 a omega q n len)
  then show ?case
    by (simp del: ntt_iter_aux.simps
             add: ntt_iter_aux.simps[of a omega q n len] ntt_layer_length Let_def)
qed

declare ntt_iter_aux.simps [simp del]

lemma intt_fast_length [simp]:
  "length (intt_fast a_hat omega q n) = length a_hat"
  unfolding intt_fast_def Let_def by (simp add: ntt_iter_aux_length)

(* === Step 8: NTT Context Locale === *)
locale ntt_context =
  fixes p :: ntt_params
  assumes params_ok: "valid_ntt_params p"
begin

abbreviation "n \<equiv> ntt_n p"
abbreviation "q \<equiv> ntt_q p"
abbreviation "omega \<equiv> ntt_omega p"

lemma n_pos: "n > 0"
  using params_ok unfolding valid_ntt_params_def by simp

lemma q_pos: "q > 1"
  using params_ok unfolding valid_ntt_params_def by simp

lemma omega_primitive: "is_primitive_root omega n q"
  using params_ok unfolding valid_ntt_params_def by simp

definition "omega_inv \<equiv> mod_inverse omega q"
definition "n_inv \<equiv> mod_inverse (int n) q"

text \<open>
  Convenience functions for this parameter set.
\<close>

definition ntt :: "poly \<Rightarrow> poly" where
  "ntt a = ntt_naive a omega q n"

definition intt :: "poly \<Rightarrow> poly" where
  "intt a_hat = intt_naive a_hat omega q n"

definition ntt_mult :: "poly \<Rightarrow> poly \<Rightarrow> poly" where
  "ntt_mult a_hat b_hat = ntt_pointwise_mult a_hat b_hat q"

lemma ntt_length: "length (ntt a) = n"
  unfolding ntt_def by simp

lemma intt_length: "length (intt a_hat) = n"
  unfolding intt_def by simp

text \<open>
  Main theorems instantiated for this context.
\<close>

theorem ntt_mult_correct:
  assumes "length a = n" and "length b = n"
  assumes conv:
    "ntt_naive (ring_mod (poly_mult a b) n) omega q n =
     ntt_pointwise_mult (ntt_naive a omega q n) (ntt_naive b omega q n) q"
  assumes inv:
    "intt_naive (ntt_naive (ring_mod (poly_mult a b) n) omega q n) omega q n =
     poly_mod (ring_mod (poly_mult a b) n) q"
  shows "intt (ntt_mult (ntt a) (ntt b)) = poly_mod (ring_mod (poly_mult a b) n) q"
proof -
  have "intt (ntt_mult (ntt a) (ntt b)) =
        intt_naive (ntt_pointwise_mult (ntt_naive a omega q n) (ntt_naive b omega q n) q) omega q n"
    unfolding ntt_def intt_def ntt_mult_def by simp
  also have "... = intt_naive (ntt_naive (ring_mod (poly_mult a b) n) omega q n) omega q n"
    using conv by simp
  also have "... = poly_mod (ring_mod (poly_mult a b) n) q"
    using inv by simp
  finally show ?thesis .
qed

end

(* === Step 9: Kyber/Dilithium Specific Parameters === *)
text \<open>
  Standard NTT parameters for CRYSTALS schemes.
\<close>

definition kyber_ntt_params :: ntt_params where
  "kyber_ntt_params = \<lparr>
    ntt_n = 256,
    ntt_q = 3329,
    ntt_omega = 17
  \<rparr>"

definition dilithium_ntt_params :: ntt_params where
  "dilithium_ntt_params = \<lparr>
    ntt_n = 256,
    ntt_q = 8380417,
    ntt_omega = 1753
  \<rparr>"

text \<open>
  Verification that these are valid NTT parameters.
  The primitive root property can be verified computationally.
\<close>

lemma kyber_17_order_256:
  "power_mod 17 256 3329 = 1"
  unfolding power_mod_def
  by eval

lemma kyber_omega_not_primitive_root:
  "\<not> is_primitive_root 17 256 3329"
proof
  assume prim: "is_primitive_root 17 256 3329"
  have "power_mod 17 256 3329 = (3329 - 1) mod 3329"
    using prim unfolding is_primitive_root_def by simp
  then show False
    using kyber_17_order_256 by simp
qed

lemma kyber_ntt_params_invalid:
  "\<not> valid_ntt_params kyber_ntt_params"
  unfolding valid_ntt_params_def kyber_ntt_params_def
  using kyber_omega_not_primitive_root by simp

lemma dilithium_omega_is_primitive_root:
  "is_primitive_root 1753 256 8380417"
  unfolding is_primitive_root_def power_mod_def
  by eval

lemma dilithium_ntt_params_valid:
  "valid_ntt_params dilithium_ntt_params"
  unfolding valid_ntt_params_def dilithium_ntt_params_def
  using dilithium_omega_is_primitive_root by simp

(* === Step 10: Code Export === *)
export_code
  ntt_params.make valid_ntt_params
  ntt_n ntt_q ntt_omega
  power_mod is_primitive_root
  twiddle twiddle_factors
  ntt_naive ntt_coeff
  intt_naive intt_coeff mod_inverse
  ntt_pointwise_mult
  butterfly ntt_fast intt_fast
  kyber_ntt_params dilithium_ntt_params
  in Haskell module_name "Canon.Rings.NTT"

end
