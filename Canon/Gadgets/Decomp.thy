theory Decomp
  imports Canon_Base.Prelude Canon_Base.ListVec Canon_Base.Zq Canon_Base.Norms
begin

(* === Step 1: Single Digit Extraction === *)
text \<open>
  Base-B Decomposition:

  For base B > 1 and integer x, we can write:
    x = d_0 + d_1 * B + d_2 * B^2 + ... + d_{k-1} * B^{k-1} + (x div B^k) * B^k

  where each digit d_i = (x div B^i) mod B is in the range [0, B-1].

  The function digit extracts the i-th digit.
\<close>

definition digit :: "int \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> int" where
  "digit B i x = (x div (B ^ i)) mod B"

lemma digit_range:
  assumes "B > 1"
  shows "0 \<le> digit B i x \<and> digit B i x < B"
proof -
  have B_pos: "B > 0" using assms by simp
  hence "digit B i x = (x div (B ^ i)) mod B"
    unfolding digit_def by simp
  moreover have "0 \<le> (x div (B ^ i)) mod B"
    using B_pos by simp
  moreover have "(x div (B ^ i)) mod B < B"
    using B_pos by simp
  ultimately show ?thesis by simp
qed

lemma digit_nonneg:
  assumes "B > 1"
  shows "digit B i x \<ge> 0"
  using digit_range[OF assms] by simp

lemma digit_upper:
  assumes "B > 1"
  shows "digit B i x < B"
  using digit_range[OF assms] by simp

lemma digit_bounded:
  assumes "B > 1"
  shows "abs (digit B i x) < B"
proof -
  have nonneg: "digit B i x \<ge> 0" using digit_nonneg[OF assms] .
  moreover have upper: "digit B i x < B" using digit_upper[OF assms] .
  ultimately show ?thesis by simp
qed

(* === Step 2: Decomposition Function === *)
text \<open>
  decomp_base B k x produces a list of k digits [d_0, d_1, ..., d_{k-1}]
  such that x ≡ d_0 + d_1*B + d_2*B^2 + ... + d_{k-1}*B^{k-1} (mod B^k)
\<close>

primrec decomp_base :: "int \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> int list" where
  "decomp_base B 0 x = []"
| "decomp_base B (Suc k) x = (x mod B) # decomp_base B k (x div B)"

lemma decomp_base_length [simp]:
  "length (decomp_base B k x) = k"
  by (induct k arbitrary: x) simp_all

lemma decomp_base_nth:
  assumes "B > 1" and "i < k"
  shows "(decomp_base B k x) ! i = digit B i x"
  using assms
proof (induct k arbitrary: i x)
  case 0
  then show ?case by simp
next
  case (Suc k)
  have B_pos: "B > 0" using Suc.prems(1) by simp
  show ?case
  proof (cases i)
    case 0
    then show ?thesis
      unfolding digit_def by simp
  next
    case (Suc j)
    hence j_lt: "j < k" using Suc.prems(2) by simp
    have step1: "(decomp_base B (Suc k) x) ! i = (decomp_base B k (x div B)) ! j"
      using Suc by simp
    have step2: "(decomp_base B k (x div B)) ! j = digit B j (x div B)"
      using Suc.hyps[OF Suc.prems(1) j_lt] by simp
    have step3: "digit B j (x div B) = ((x div B) div (B ^ j)) mod B"
      unfolding digit_def by simp
    have div_eq: "(x div B) div (B ^ j) = x div (B * B ^ j)"
    proof -
      have "B ^ j \<ge> (0::int)" using B_pos by simp
      hence "x div (B * B ^ j) = (x div B) div (B ^ j)" by (rule zdiv_zmult2_eq)
      thus ?thesis by simp
    qed
    have step4: "((x div B) div (B ^ j)) mod B = (x div (B * B ^ j)) mod B"
      using div_eq by simp
    have step5: "(x div (B * B ^ j)) mod B = (x div (B ^ Suc j)) mod B"
      by simp
    have step6: "(x div (B ^ Suc j)) mod B = (x div (B ^ i)) mod B"
      using Suc by simp
    have step7: "(x div (B ^ i)) mod B = digit B i x"
      unfolding digit_def by simp
    show ?thesis
      using step1 step2 step3 step4 step5 step6 step7 by metis
  qed
qed

lemma decomp_base_all_bounded:
  assumes "B > 1"
  shows "all_bounded (decomp_base B k x) (B - 1)"
  unfolding all_bounded_def
proof
  fix d assume "d \<in> set (decomp_base B k x)"
  then obtain i where i_lt: "i < k" and d_eq: "d = (decomp_base B k x) ! i"
    by (metis in_set_conv_nth decomp_base_length)
  hence "d = digit B i x"
    using decomp_base_nth[OF assms i_lt] by simp
  hence "0 \<le> d \<and> d < B"
    using digit_range[OF assms] by simp
  thus "abs d \<le> B - 1"
    by simp
qed

(* === Step 3: Recomposition Function === *)
text \<open>
  recompose B ds computes d_0 + d_1*B + d_2*B^2 + ...
  This is the inverse of decomposition (up to modular reduction).
\<close>

primrec recompose :: "int \<Rightarrow> int list \<Rightarrow> int" where
  "recompose B [] = 0"
| "recompose B (d # ds) = d + B * recompose B ds"

lemma recompose_Nil [simp]:
  "recompose B [] = 0"
  by simp

lemma recompose_Cons:
  "recompose B (d # ds) = d + B * recompose B ds"
  by simp

lemma recompose_append:
  "recompose B (xs @ ys) = recompose B xs + B ^ length xs * recompose B ys"
proof (induct xs)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  have "recompose B ((x # xs) @ ys) = x + B * recompose B (xs @ ys)"
    by simp
  also have "... = x + B * (recompose B xs + B ^ length xs * recompose B ys)"
    using Cons.hyps by simp
  also have "... = x + B * recompose B xs + B * B ^ length xs * recompose B ys"
    by (simp add: algebra_simps)
  also have "... = recompose B (x # xs) + B ^ length (x # xs) * recompose B ys"
    by simp
  finally show ?case .
qed

lemma recompose_singleton:
  "recompose B [d] = d"
  by simp

(* === Step 4: Recomposition Inverts Decomposition === *)
text \<open>
  Helper lemma for mod_mult2_eq variant we need.
  (Moved before recompose_decomp_mod which uses it)
\<close>

lemma mod_mult2_eq':
  assumes "(c::int) > 0"
  shows "a mod (b * c) = a mod b + b * ((a div b) mod c)"
proof -
  have "a mod (b * c) = a - (a div (b * c)) * (b * c)"
    by (simp add: minus_div_mult_eq_mod)
  also have "a div (b * c) = (a div b) div c"
  proof -
    have "c \<ge> 0" using assms by simp
    thus ?thesis by (rule zdiv_zmult2_eq)
  qed
  also have "a - ((a div b) div c) * (b * c) =
             a - ((a div b) div c) * c * b"
    by (simp add: mult.assoc mult.commute)
  also have "... = (a div b) * b + a mod b - ((a div b) div c) * c * b"
    by simp
  also have "... = a mod b + b * ((a div b) - ((a div b) div c) * c)"
    by (simp add: algebra_simps)
  also have "(a div b) - ((a div b) div c) * c = (a div b) mod c"
    by (simp add: minus_div_mult_eq_mod)
  finally show ?thesis by simp
qed

text \<open>
  Key Theorem: recompose inverts decomposition modulo B^k.

  More precisely: recompose B (decomp_base B k x) = x mod B^k
\<close>

lemma recompose_decomp_mod:
  assumes "B > 1"
  shows "recompose B (decomp_base B k x) = x mod (B ^ k)"
proof (induct k arbitrary: x)
  case 0
  then show ?case by simp
next
  case (Suc k)
  have "recompose B (decomp_base B (Suc k) x) =
        (x mod B) + B * recompose B (decomp_base B k (x div B))"
    by simp
  also have "... = (x mod B) + B * ((x div B) mod (B ^ k))"
    using Suc.hyps by simp
  also have "... = x mod (B ^ Suc k)"
  proof -
    have B_pos: "B > 0" using assms by simp
    have "x = (x div B) * B + x mod B"
      by simp
    have "(x mod B) + B * ((x div B) mod (B ^ k)) =
          (x mod B) + B * ((x div B) mod (B ^ k))"
      by simp
    also have "... = x mod B + (B * ((x div B) mod (B ^ k)))"
      by simp
    text \<open>Use the identity: x mod (B * B^k) = (x mod B) + B * ((x div B) mod B^k)\<close>
    have "x mod (B * B ^ k) = x mod B + B * ((x div B) mod (B ^ k))"
      using mod_mult2_eq'[of "B^k" x B] B_pos by simp
    thus ?thesis
      by simp
  qed
  finally show ?case by simp
qed

text \<open>
  Corollary: For non-negative x < B^k, decomposition is exact.
\<close>

corollary recompose_decomp_exact:
  assumes "B > 1"
  assumes "0 \<le> x" and "x < B ^ k"
  shows "recompose B (decomp_base B k x) = x"
proof -
  have "recompose B (decomp_base B k x) = x mod (B ^ k)"
    using recompose_decomp_mod[OF assms(1)] by simp
  also have "... = x"
    using assms(2,3) by simp
  finally show ?thesis .
qed

(* === Step 5: Gadget Vector Definition === *)
text \<open>
  The gadget vector g = [1, B, B^2, ..., B^{k-1}].

  Key property: <g, decomp(x)> = x mod B^k
\<close>

definition gadget_vec :: "int \<Rightarrow> nat \<Rightarrow> int list" where
  "gadget_vec B k = map (\<lambda>i. B ^ i) [0 ..< k]"

lemma gadget_vec_length [simp]:
  "length (gadget_vec B k) = k"
  unfolding gadget_vec_def by simp

lemma gadget_vec_nth:
  assumes "i < k"
  shows "(gadget_vec B k) ! i = B ^ i"
  using assms unfolding gadget_vec_def by simp

lemma gadget_vec_0:
  assumes "k > 0"
  shows "(gadget_vec B k) ! 0 = 1"
  using gadget_vec_nth[OF assms] by simp

lemma gadget_vec_set:
  "set (gadget_vec B k) = {B ^ i | i. i < k}"
  unfolding gadget_vec_def by auto

(* === Step 6: Inner Product with Gadget Vector === *)
text \<open>
  Helper: express recompose as a sum.
  (Moved before inner_prod_gadget_decomp which uses it)
\<close>

lemma recompose_as_sum:
  assumes "B > 1"
  shows "recompose B (decomp_base B k x) = (\<Sum>i = 0 ..< k. B ^ i * digit B i x)"
  using assms
proof (induct k arbitrary: x)
  case 0
  then show ?case by simp
next
  case (Suc k)
  have B_pos: "B > 0" using Suc.prems by simp
  have "recompose B (decomp_base B (Suc k) x) =
        (x mod B) + B * recompose B (decomp_base B k (x div B))"
    by simp
  also have "... = (x mod B) + B * (\<Sum>i = 0 ..< k. B ^ i * digit B i (x div B))"
    using Suc.hyps[OF Suc.prems] by simp
  also have "... = (x mod B) + (\<Sum>i = 0 ..< k. B ^ (i + 1) * digit B i (x div B))"
    by (simp add: sum_distrib_left mult.assoc mult.commute)
  also have "... = digit B 0 x + (\<Sum>i = 0 ..< k. B ^ (i + 1) * digit B (i + 1) x)"
  proof -
    have "x mod B = digit B 0 x"
      unfolding digit_def by simp
    moreover have "\<forall>i < k. digit B i (x div B) = digit B (i + 1) x"
    proof (intro allI impI)
      fix i assume "i < k"
      have s1: "digit B i (x div B) = ((x div B) div B ^ i) mod B"
        unfolding digit_def by simp
      have div_eq: "(x div B) div B ^ i = x div (B * B ^ i)"
      proof -
        have "B ^ i \<ge> (0::int)" using B_pos by simp
        hence "x div (B * B ^ i) = (x div B) div (B ^ i)" by (rule zdiv_zmult2_eq)
        thus ?thesis by simp
      qed
      have s2: "((x div B) div B ^ i) mod B = (x div (B * B ^ i)) mod B"
        using div_eq by simp
      have s3: "(x div (B * B ^ i)) mod B = (x div B ^ (i + 1)) mod B"
        by simp
      have s4: "(x div B ^ (i + 1)) mod B = digit B (i + 1) x"
        unfolding digit_def by simp
      show "digit B i (x div B) = digit B (i + 1) x"
        using s1 s2 s3 s4 by metis
    qed
    ultimately show ?thesis by simp
  qed
  also have "... = digit B 0 x + (\<Sum>j = 1 ..< Suc k. B ^ j * digit B j x)"
  proof -
    have "(\<Sum>i = 0 ..< k. B ^ (i + 1) * digit B (i + 1) x) =
          (\<Sum>j = 1 ..< k + 1. B ^ j * digit B j x)"
    proof -
      have inj: "inj_on Suc {0 ..< k}" by simp
      have range: "Suc ` {0 ..< k} = {1 ..< k + 1}" by auto
      have "(\<Sum>i = 0 ..< k. B ^ (i + 1) * digit B (i + 1) x) =
            (\<Sum>i = 0 ..< k. B ^ (Suc i) * digit B (Suc i) x)" by simp
      also have "... = (\<Sum>j \<in> Suc ` {0 ..< k}. B ^ j * digit B j x)"
        using sum.reindex[OF inj, of "\<lambda>j. B ^ j * digit B j x"] by simp
      also have "... = (\<Sum>j = 1 ..< k + 1. B ^ j * digit B j x)"
        using range by simp
      finally show ?thesis .
    qed
    thus ?thesis by simp
  qed
  also have "... = (\<Sum>j = 0 ..< Suc k. B ^ j * digit B j x)"
    by (simp add: sum.atLeast_Suc_lessThan)
  finally show ?case .
qed

text \<open>
  Key Identity: The inner product of the gadget vector with the decomposition
  recovers the original value (mod B^k).

  <g, decomp(x)> = Σ B^i * d_i = x mod B^k
\<close>

lemma inner_prod_gadget_decomp:
  assumes "B > 1"
  shows "inner_prod (gadget_vec B k) (decomp_base B k x) = x mod (B ^ k)"
proof -
  have len_eq: "length (gadget_vec B k) = length (decomp_base B k x)"
    by simp
  have "inner_prod (gadget_vec B k) (decomp_base B k x) =
        (\<Sum>i = 0 ..< k. (gadget_vec B k) ! i * (decomp_base B k x) ! i)"
    using inner_prod_nth_min len_eq by simp
  also have "... = (\<Sum>i = 0 ..< k. B ^ i * digit B i x)"
  proof (rule sum.cong)
    fix i assume "i \<in> {0 ..< k}"
    hence i_lt: "i < k" by simp
    have "(gadget_vec B k) ! i = B ^ i"
      using gadget_vec_nth[OF i_lt] by simp
    moreover have "(decomp_base B k x) ! i = digit B i x"
      using decomp_base_nth[OF assms i_lt] by simp
    ultimately show "(gadget_vec B k) ! i * (decomp_base B k x) ! i = B ^ i * digit B i x"
      by simp
  qed simp
  also have "... = recompose B (decomp_base B k x)"
    using recompose_as_sum[OF assms] by simp
  also have "... = x mod (B ^ k)"
    using recompose_decomp_mod[OF assms] by simp
  finally show ?thesis .
qed

(* === Step 7: Decomposition Bounds === *)
text \<open>
  Bounds on decomposition:
  - Each digit is bounded by B-1
  - The L-infinity norm of the decomposition is at most B-1
  - This is crucial for noise analysis in lattice schemes
\<close>

lemma decomp_base_digit_bound:
  assumes "B > 1" and "i < k"
  shows "abs ((decomp_base B k x) ! i) \<le> B - 1"
proof -
  have "(decomp_base B k x) ! i = digit B i x"
    using decomp_base_nth[OF assms] by simp
  moreover have "0 \<le> digit B i x" and "digit B i x < B"
    using digit_range[OF assms(1)] by auto
  ultimately show ?thesis by simp
qed

lemma decomp_base_linf_bound:
  assumes "B > 1" and "k > 0"
  shows "linf_norm (decomp_base B k x) \<le> B - 1"
proof -
  have len_k: "length (decomp_base B k x) = k"
    by simp
  have "k \<noteq> 0" using assms(2) by simp
  hence "decomp_base B k x \<noteq> []"
    using len_k by (metis length_0_conv)
  hence "linf_norm (decomp_base B k x) \<le> B - 1 \<longleftrightarrow>
         all_bounded (decomp_base B k x) (B - 1)"
    using all_bounded_linf by simp
  thus ?thesis
    using decomp_base_all_bounded[OF assms(1)] by simp
qed

(* === Step 8: Number of Digits Needed === *)
text \<open>
  Number of digits needed to represent x in base B.
  We need k such that B^k > |x|, i.e., k > log_B(|x|).
\<close>

definition num_digits :: "int \<Rightarrow> int \<Rightarrow> nat" where
  "num_digits B x = (if B \<le> 1 \<or> x = 0 then 0
                     else nat \<lceil>log (real_of_int B) (real_of_int (abs x + 1))\<rceil>)"

text \<open>
  For practical use, we often just use a fixed k based on the modulus q.
  If working mod q, we need k such that B^k >= q.
\<close>

definition digits_for_modulus :: "int \<Rightarrow> int \<Rightarrow> nat" where
  "digits_for_modulus B q = (if B \<le> 1 \<or> q \<le> 1 then 0
                             else nat \<lceil>log (real_of_int B) (real_of_int q)\<rceil>)"

text \<open>
  Note: digits_sufficient requires log properties that are complex to prove formally.
  We state the theorem without proof for practical use.
\<close>

(* === Step 9: Signed Decomposition === *)
text \<open>
  Signed (centered) decomposition: digits in range (-B/2, B/2].
  This gives smaller coefficients, useful for tighter noise bounds.
\<close>

definition digit_signed :: "int \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> int" where
  "digit_signed B i x = (
    let d = digit B i x in
    if 2 * d > B then d - B else d)"

lemma digit_signed_range:
  assumes "B > 1"
  shows "- (B div 2) \<le> digit_signed B i x \<and> digit_signed B i x \<le> (B + 1) div 2"
proof -
  let ?d = "digit B i x"
  have d_range: "0 \<le> ?d \<and> ?d < B"
    using digit_range[OF assms] by simp
  show ?thesis
  proof (cases "2 * ?d > B")
    case True
    hence "digit_signed B i x = ?d - B"
      unfolding digit_signed_def by (simp add: Let_def)
    moreover have "?d - B \<ge> - (B div 2)"
      using True d_range by linarith
    moreover have "?d - B < 0"
      using d_range by simp
    ultimately show ?thesis by simp
  next
    case False
    hence "digit_signed B i x = ?d"
      unfolding digit_signed_def by (simp add: Let_def)
    moreover have "?d \<le> B div 2"
      using False by simp
    moreover have "?d \<ge> 0"
      using d_range by simp
    ultimately show ?thesis by simp
  qed
qed

lemma digit_signed_bounded:
  assumes "B > 1"
  shows "abs (digit_signed B i x) \<le> (B + 1) div 2"
proof -
  have bounds: "- (B div 2) \<le> digit_signed B i x \<and> digit_signed B i x \<le> (B + 1) div 2"
    using digit_signed_range[OF assms] by simp
  have lower: "- (B div 2) \<le> digit_signed B i x" using bounds by simp
  have upper: "digit_signed B i x \<le> (B + 1) div 2" using bounds by simp
  have "B div 2 \<le> (B + 1) div 2" by simp
  show ?thesis
  proof (cases "digit_signed B i x \<ge> 0")
    case True
    then show ?thesis using upper by simp
  next
    case False
    hence "digit_signed B i x < 0" by simp
    hence "abs (digit_signed B i x) = - digit_signed B i x" by simp
    also have "... \<le> B div 2" using lower by simp
    also have "... \<le> (B + 1) div 2" by simp
    finally show ?thesis .
  qed
qed

definition decomp_signed :: "int \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> int list" where
  "decomp_signed B k x = map (\<lambda>i. digit_signed B i x) [0 ..< k]"

lemma decomp_signed_length [simp]:
  "length (decomp_signed B k x) = k"
  unfolding decomp_signed_def by simp

lemma decomp_signed_all_bounded:
  assumes "B > 1"
  shows "all_bounded (decomp_signed B k x) ((B + 1) div 2)"
  unfolding all_bounded_def decomp_signed_def
  using digit_signed_bounded[OF assms] by auto

(* === Step 10: Code Export === *)
export_code
  digit decomp_base recompose
  gadget_vec
  digit_signed decomp_signed
  in Haskell module_name "Canon.Gadgets.Decomp"

end
