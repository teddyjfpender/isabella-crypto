# Prompt ID: canon-gadgets-decomp

## Task

Create the Canon/Gadgets/Decomp.thy theory file - base-B decomposition and gadget vectors.

This theory provides the formal definition of base-B decomposition, which is fundamental to gadget-based lattice constructions. The key insight is that any integer x can be written as x = Σ B^i · d_i where each digit d_i is small.

**Key identity**: `⟨g, decomp(x)⟩ = x` where g = [1, B, B², ..., B^{k-1}]

This is used in:
- GSW fully homomorphic encryption
- Gadget matrices and trapdoors
- Noise management in lattice schemes

## Note on Theory Structure

The step-loop provides the theory header automatically. Your steps output content for inside `begin...end`.

**IMPORTANT**: These functions are already defined - do NOT redefine them:
- `inner_prod`, `scalar_mult`, `valid_vec` - from ListVec.thy
- `vec_mod` - from Zq.thy
- `all_bounded` - from Norms.thy

## Step-Loop Invocation

```bash
./ralph/step-loop-v2.sh --prompt canon-gadgets-decomp \
    --output-dir Canon \
    --theory-name Decomp \
    --theory-path Gadgets \
    --session Canon_Gadgets \
    --imports 'Canon_Base.Prelude Canon_Base.ListVec Canon_Base.Zq Canon_Base.Norms' \
    --parent-session Canon_Base \
    --session-dir Canon
```

**Prerequisites**: Prelude, ListVec, Zq, and Norms must be completed first.

## Proof Robustness Guidelines

**CRITICAL**: Follow these rules for robust proofs that work across Isabelle versions.

1. **If exact code is provided, USE IT EXACTLY** - do not simplify or "improve"
2. **Type annotations** are required for numeric lemmas - e.g., `(k::nat)`, `(B::int)`
3. **Explicit case splits** for conditionals - use `proof (cases "condition")`
4. **Use `arith` or `linarith`** for integer inequalities
5. **Induction on nat** - use `proof (induct k)` with explicit base and step cases
6. **Power lemmas** - be careful with `B^k` vs `B^(k-1)` off-by-one errors
7. **Name intermediate facts** for readability and debugging

## Steps

### Step 1: Single Digit Extraction

Extract a single digit from the base-B representation.

**USE THIS EXACT CODE**:
```isabelle
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
  have "B > 0" using assms by simp
  hence "digit B i x = (x div (B ^ i)) mod B"
    unfolding digit_def by simp
  moreover have "0 \<le> (x div (B ^ i)) mod B"
    using `B > 0` by simp
  moreover have "(x div (B ^ i)) mod B < B"
    using `B > 0` by simp
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
  have "digit B i x \<ge> 0" using digit_nonneg[OF assms] .
  moreover have "digit B i x < B" using digit_upper[OF assms] .
  ultimately show ?thesis by simp
qed
```

### Step 2: Decomposition Function

Decompose an integer into k digits in base B.

**USE THIS EXACT CODE**:
```isabelle
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
  assumes "i < k"
  shows "(decomp_base B k x) ! i = digit B i x"
  using assms
proof (induct k arbitrary: i x)
  case 0
  then show ?case by simp
next
  case (Suc k)
  show ?case
  proof (cases i)
    case 0
    then show ?thesis
      unfolding digit_def by simp
  next
    case (Suc j)
    hence "j < k" using Suc.prems by simp
    have "(decomp_base B (Suc k) x) ! i = (decomp_base B k (x div B)) ! j"
      using Suc by simp
    also have "... = digit B j (x div B)"
      using Suc.hyps[OF `j < k`] by simp
    also have "... = ((x div B) div (B ^ j)) mod B"
      unfolding digit_def by simp
    also have "... = (x div (B * B ^ j)) mod B"
      by (simp add: div_mult2_eq mult.commute)
    also have "... = (x div (B ^ Suc j)) mod B"
      by simp
    also have "... = (x div (B ^ i)) mod B"
      using Suc by simp
    also have "... = digit B i x"
      unfolding digit_def by simp
    finally show ?thesis .
  qed
qed

lemma decomp_base_all_bounded:
  assumes "B > 1"
  shows "all_bounded (decomp_base B k x) (B - 1)"
  unfolding all_bounded_def
proof
  fix d assume "d \<in> set (decomp_base B k x)"
  then obtain i where "i < k" and "d = (decomp_base B k x) ! i"
    by (metis in_set_conv_nth decomp_base_length)
  hence "d = digit B i x"
    using decomp_base_nth by simp
  hence "0 \<le> d \<and> d < B"
    using digit_range[OF assms] by simp
  thus "abs d \<le> B - 1"
    by simp
qed
```

### Step 3: Recomposition Function

Reconstruct an integer from its digits.

**USE THIS EXACT CODE**:
```isabelle
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
```

### Step 4: Recomposition Inverts Decomposition

The key theorem: recompose (decomp x) = x mod B^k.

**USE THIS EXACT CODE**:
```isabelle
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
    have "B > 0" using assms by simp
    have "x = (x div B) * B + x mod B"
      by simp
    have "(x mod B) + B * ((x div B) mod (B ^ k)) =
          (x mod B) + B * ((x div B) mod (B ^ k))"
      by simp
    also have "... = x mod B + (B * ((x div B) mod (B ^ k)))"
      by simp
    text \<open>Use the identity: x mod (B * B^k) = (x mod B) + B * ((x div B) mod B^k)\<close>
    have "x mod (B * B ^ k) = x mod B + B * ((x div B) mod (B ^ k))"
      using mod_mult2_eq'[of x B "B^k"] `B > 0` by simp
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

text \<open>
  Helper lemma for mod_mult2_eq variant we need.
\<close>

lemma mod_mult2_eq':
  assumes "(c::int) > 0"
  shows "a mod (b * c) = a mod b + b * ((a div b) mod c)"
proof -
  have "a mod (b * c) = a - (a div (b * c)) * (b * c)"
    by (simp add: minus_div_mult_eq_mod)
  also have "a div (b * c) = (a div b) div c"
    by (simp add: div_mult2_eq)
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
```

### Step 5: Gadget Vector Definition

The gadget vector g = [1, B, B², ..., B^{k-1}].

**USE THIS EXACT CODE**:
```isabelle
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
```

### Step 6: Inner Product with Gadget Vector

The key identity: ⟨g, decomp(x)⟩ = x mod B^k.

**USE THIS EXACT CODE**:
```isabelle
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
    hence "i < k" by simp
    have "(gadget_vec B k) ! i = B ^ i"
      using gadget_vec_nth[OF `i < k`] by simp
    moreover have "(decomp_base B k x) ! i = digit B i x"
      using decomp_base_nth[OF `i < k`] by simp
    ultimately show "(gadget_vec B k) ! i * (decomp_base B k x) ! i = B ^ i * digit B i x"
      by simp
  qed simp
  also have "... = recompose B (decomp_base B k x)"
    using recompose_as_sum[of B k x] by simp
  also have "... = x mod (B ^ k)"
    using recompose_decomp_mod[OF assms] by simp
  finally show ?thesis .
qed

text \<open>
  Helper: express recompose as a sum.
\<close>

lemma recompose_as_sum:
  "recompose B (decomp_base B k x) = (\<Sum>i = 0 ..< k. B ^ i * digit B i x)"
proof (induct k arbitrary: x)
  case 0
  then show ?case by simp
next
  case (Suc k)
  have "recompose B (decomp_base B (Suc k) x) =
        (x mod B) + B * recompose B (decomp_base B k (x div B))"
    by simp
  also have "... = (x mod B) + B * (\<Sum>i = 0 ..< k. B ^ i * digit B i (x div B))"
    using Suc.hyps by simp
  also have "... = (x mod B) + (\<Sum>i = 0 ..< k. B ^ (i + 1) * digit B i (x div B))"
    by (simp add: sum_distrib_left mult.assoc mult.commute)
  also have "... = digit B 0 x + (\<Sum>i = 0 ..< k. B ^ (i + 1) * digit B (i + 1) x)"
  proof -
    have "x mod B = digit B 0 x"
      unfolding digit_def by simp
    moreover have "\<forall>i < k. digit B i (x div B) = digit B (i + 1) x"
    proof (intro allI impI)
      fix i assume "i < k"
      have "digit B i (x div B) = ((x div B) div B ^ i) mod B"
        unfolding digit_def by simp
      also have "... = (x div (B * B ^ i)) mod B"
        by (simp add: div_mult2_eq mult.commute)
      also have "... = (x div B ^ (i + 1)) mod B"
        by simp
      also have "... = digit B (i + 1) x"
        unfolding digit_def by simp
      finally show "digit B i (x div B) = digit B (i + 1) x" .
    qed
    ultimately show ?thesis by simp
  qed
  also have "... = digit B 0 x + (\<Sum>j = 1 ..< Suc k. B ^ j * digit B j x)"
  proof -
    have "(\<Sum>i = 0 ..< k. B ^ (i + 1) * digit B (i + 1) x) =
          (\<Sum>j = 1 ..< k + 1. B ^ j * digit B j x)"
      by (rule sum.reindex_cong[of Suc]) auto
    thus ?thesis by simp
  qed
  also have "... = (\<Sum>j = 0 ..< Suc k. B ^ j * digit B j x)"
    by (simp add: sum.atLeast_Suc_lessThan)
  finally show ?case .
qed
```

### Step 7: Decomposition Bounds

Bounds on the decomposition for use in noise analysis.

**USE THIS EXACT CODE**:
```isabelle
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
    using decomp_base_nth[OF assms(2)] by simp
  moreover have "0 \<le> digit B i x" and "digit B i x < B"
    using digit_range[OF assms(1)] by auto
  ultimately show ?thesis by simp
qed

lemma decomp_base_linf_bound:
  assumes "B > 1" and "k > 0"
  shows "linf_norm (decomp_base B k x) \<le> B - 1"
proof -
  have "decomp_base B k x \<noteq> []"
    using assms(2) by (simp add: decomp_base_length)
  hence "linf_norm (decomp_base B k x) \<le> B - 1 \<longleftrightarrow>
         all_bounded (decomp_base B k x) (B - 1)"
    using all_bounded_linf by simp
  thus ?thesis
    using decomp_base_all_bounded[OF assms(1)] by simp
qed
```

### Step 8: Number of Digits Needed

Calculate how many digits are needed to represent a value.

**USE THIS EXACT CODE**:
```isabelle
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

lemma digits_sufficient:
  assumes "B > 1" and "q > 1"
  assumes "k = digits_for_modulus B q"
  assumes "0 \<le> x" and "x < q"
  shows "recompose B (decomp_base B k x) = x"
proof -
  have "x < B ^ k"
    sorry \<comment> \<open>This requires log properties - simplified for export\<close>
  thus ?thesis
    using recompose_decomp_exact[OF assms(1) assms(4)] by simp
qed
```

### Step 9: Signed Decomposition

Alternative decomposition with centered digits in [-B/2, B/2).

**USE THIS EXACT CODE**:
```isabelle
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
  have "B div 2 \<le> (B + 1) div 2"
    by simp
  thus ?thesis using bounds by simp
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
```

### Step 10: Code Export

**USE THIS EXACT CODE**:
```isabelle
export_code
  digit decomp_base recompose
  gadget_vec
  digit_signed decomp_signed
  in Haskell module_name "Canon.Gadgets.Decomp"
```

## Constraints

- Theory name: `Decomp`
- Session: `Canon_Gadgets` (depends on `Canon_Base`)
- Imports: Prelude, ListVec, Zq, Norms
- No sorry/oops - all proofs must be complete (except digits_sufficient which uses log)
- The `inner_prod_gadget_decomp` lemma is the key identity
- Be careful with off-by-one errors in power indices

## Proof Strategy Reference

| Goal Type | Recommended Tactic |
|-----------|-------------------|
| List length | `by simp` (after declaring [simp]) |
| Induction on nat | `proof (induct k arbitrary: x)` |
| Sum manipulation | `by (rule sum.cong) auto` |
| Index rewriting | `by (rule sum.reindex_cong[of Suc]) auto` |
| Division/mod | `by (simp add: div_mult2_eq)` |
| Digit bounds | `using digit_range by simp` |

## Key Insights

1. **digit extracts coefficients**: `digit B i x = (x div B^i) mod B`
2. **decomp_base is recursive**: Base case [], inductive case uses mod and div
3. **recompose is Horner's method**: `d₀ + B*(d₁ + B*(d₂ + ...))
4. **Key identity**: `recompose (decomp x) = x mod B^k`
5. **Gadget identity**: `⟨g, decomp(x)⟩ = x mod B^k` where g = [1, B, B², ...]
6. **Signed digits**: Centered in (-B/2, B/2] for tighter bounds
7. **mod_mult2_eq'**: Key lemma for the recompose proof

## Deliverable

A working Decomp.thy that:
1. Compiles as part of Canon_Gadgets session
2. Defines `digit`, `decomp_base`, `recompose`
3. Has `recompose_decomp_mod` theorem
4. Defines `gadget_vec` with `inner_prod_gadget_decomp`
5. Has signed decomposition variant
6. Exports to Haskell
