# Prompt ID: canon-rings-polymod

## Task

Create the Canon/Rings/PolyMod.thy theory file - polynomials over Z_q modulo a cyclotomic-like polynomial.

This theory provides the foundation for Module-LWE/SIS and CRYSTALS-style schemes (Kyber, Dilithium). Polynomials are represented as coefficient lists, with operations defined modulo both q (coefficient modulus) and f(X) (ring modulus).

**Key insight**: R_q = Z_q[X]/(f(X)) where f(X) is typically X^n + 1 (power-of-2 cyclotomic).

## Note on Theory Structure

The step-loop provides the theory header automatically. Your steps output content for inside `begin...end`.

**IMPORTANT**: These functions are already defined - do NOT redefine them:
- `valid_vec`, `vec_add`, `vec_sub`, `scalar_mult` - from ListVec.thy
- `vec_mod`, `mod_centered` - from Zq.thy

## Step-Loop Invocation

```bash
./ralph/step-loop-v2.sh --prompt canon-rings-polymod \
    --output-dir Canon \
    --theory-name PolyMod \
    --theory-path Rings \
    --session Canon_Rings \
    --imports 'Canon_Base.Prelude Canon_Base.ListVec Canon_Base.Zq' \
    --parent-session Canon_Base \
    --session-dir Canon
```

**Prerequisites**: Prelude, ListVec, and Zq must be completed first.

## Proof Robustness Guidelines

**CRITICAL**: Follow these rules for robust proofs that work across Isabelle versions.

1. **If exact code is provided, USE IT EXACTLY** - do not simplify or "improve"
2. **Type annotations** are required for numeric lemmas - e.g., `(n::nat)`, `(q::int)`
3. **Explicit case splits** for conditionals - use `proof (cases "condition")`
4. **Use `arith` or `linarith`** for integer inequalities
5. **Induction on lists** - use `proof (induct xs)` with explicit cases
6. **Name intermediate facts** for readability and debugging
7. **Polynomial degree** = length - 1; empty list represents zero polynomial

## Steps

### Step 1: Polynomial Type and Basic Operations

Define polynomials as coefficient lists and basic validation.

**USE THIS EXACT CODE**:
```isabelle
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
```

### Step 2: Polynomial Addition

Addition is coefficient-wise, padding shorter polynomial with zeros.

**USE THIS EXACT CODE**:
```isabelle
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
```

### Step 3: Polynomial Subtraction and Negation

**USE THIS EXACT CODE**:
```isabelle
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
```

### Step 4: Scalar Multiplication

**USE THIS EXACT CODE**:
```isabelle
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
```

### Step 5: Polynomial Multiplication (Convolution)

**USE THIS EXACT CODE**:
```isabelle
text \<open>
  Polynomial multiplication:
  (p * q)_k = Σ_{i+j=k} p_i * q_j

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
```

### Step 6: Modular Reduction of Coefficients

**USE THIS EXACT CODE**:
```isabelle
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
```

### Step 7: Ring Polynomial Modulus (X^n + 1)

**USE THIS EXACT CODE**:
```isabelle
text \<open>
  The ring R_q = Z_q[X]/(X^n + 1).

  To reduce a polynomial modulo X^n + 1:
  - Coefficients at positions >= n wrap around with sign change
  - X^n ≡ -1 (mod X^n + 1), so X^{n+k} ≡ -X^k

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

text \<open>
  Key property: X^n ≡ -1 means high coefficients fold back with alternating signs.
\<close>

lemma ring_mod_below_n:
  assumes "n > 0" and "length p \<le> n"
  shows "ring_mod p n = p @ replicate (n - length p) 0"
proof (intro nth_equalityI)
  show "length (ring_mod p n) = length (p @ replicate (n - length p) 0)"
    using assms by (simp add: ring_mod_length)
next
  fix i assume "i < length (ring_mod p n)"
  hence i_lt: "i < n" using assms by (simp add: ring_mod_length)
  show "(ring_mod p n) ! i = (p @ replicate (n - length p) 0) ! i"
  proof (cases "i < length p")
    case True
    have "(ring_mod p n) ! i = ring_mod_coeff p n i"
      using i_lt assms unfolding ring_mod_def by simp
    also have "... = poly_coeff p i"
    proof -
      have "(length p + n - 1 - i) div n + 1 = 1"
        using True assms by simp
      thus ?thesis
        unfolding ring_mod_coeff_def by simp
    qed
    also have "... = p ! i"
      using True unfolding poly_coeff_def by simp
    also have "... = (p @ replicate (n - length p) 0) ! i"
      using True by (simp add: nth_append)
    finally show ?thesis .
  next
    case False
    hence i_ge_len: "i \<ge> length p" by simp
    have "(ring_mod p n) ! i = ring_mod_coeff p n i"
      using i_lt assms unfolding ring_mod_def by simp
    also have "... = 0"
    proof -
      have "(length p + n - 1 - i) div n + 1 = 1"
        using i_ge_len i_lt assms by simp
      moreover have "poly_coeff p i = 0"
        using i_ge_len by simp
      ultimately show ?thesis
        unfolding ring_mod_coeff_def by simp
    qed
    also have "... = (p @ replicate (n - length p) 0) ! i"
      using i_ge_len i_lt assms by (simp add: nth_append)
    finally show ?thesis .
  qed
qed
```

### Step 8: Ring Multiplication

**USE THIS EXACT CODE**:
```isabelle
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
```

### Step 9: Ring Parameters Record

**USE THIS EXACT CODE**:
```isabelle
text \<open>
  Ring parameters for R_q = Z_q[X]/(X^n + 1).

  For efficiency with NTT, n is typically a power of 2.
  For security, q is chosen based on SIS/LWE parameters.
\<close>

record ring_params =
  ring_n :: nat     \<comment> \<open>polynomial degree (power of 2 for NTT)\<close>
  ring_q :: int     \<comment> \<open>coefficient modulus\<close>

definition valid_ring_params :: "ring_params \<Rightarrow> bool" where
  "valid_ring_params rp = (ring_n rp > 0 \<and> ring_q rp > 1)"

lemma valid_ring_params_pos:
  assumes "valid_ring_params rp"
  shows "ring_n rp > 0" "ring_q rp > 1"
  using assms unfolding valid_ring_params_def by auto

text \<open>
  Ring context locale for cleaner proofs.
\<close>

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
```

### Step 10: Code Export

**USE THIS EXACT CODE**:
```isabelle
export_code
  zero_poly const_poly poly_degree poly_coeff
  poly_add poly_neg poly_sub
  poly_scale poly_mult poly_mult_coeff
  poly_mod ring_mod ring_mod_coeff
  ring_mult ring_add ring_sub
  ring_params.make valid_ring_params valid_ring_elem
  ring_n ring_q
  in Haskell module_name "Canon.Rings.PolyMod"
```

## Constraints

- Theory name: `PolyMod`
- Session: `Canon_Rings` (depends on `Canon_Base`)
- Imports: Prelude, ListVec, Zq
- No sorry/oops - all proofs must be complete
- Polynomials represented as coefficient lists (little-endian: constant term first)
- Empty list = zero polynomial
- All ring operations reduce modulo both q and X^n + 1

## Proof Strategy Reference

| Goal Type | Recommended Tactic |
|-----------|-------------------|
| List equality | `by (intro nth_equalityI) simp_all` |
| Length lemmas | `by simp` (after declaring [simp]) |
| Coefficient access | `by (simp add: poly_coeff_def)` |
| Sum manipulation | `by (simp add: sum.atLeast_Suc_lessThan)` |
| Modular arithmetic | `by (simp add: mod_add_eq)` |
| Case on list | `proof (cases "p = []")` |

## Key Insights

1. **Little-endian representation**: p = [a_0, a_1, ...] means a_0 + a_1*X + ...
2. **Convolution**: (p*q)_k = Σ_{i+j=k} p_i * q_j
3. **X^n + 1 reduction**: X^n ≡ -1, so coefficients wrap with sign flip
4. **ring_mod_coeff**: Handles arbitrary length via alternating sums
5. **Two moduli**: q for coefficients, X^n+1 for polynomial degree
6. **NTT-friendly**: n = power of 2 enables fast multiplication (future)
7. **ring_context locale**: Packages parameters for cleaner proofs

## Deliverable

A working PolyMod.thy that:
1. Compiles as part of Canon_Rings session
2. Defines polynomial type and basic operations (add, sub, scale, mult)
3. Has coefficient and polynomial modular reduction
4. Has ring operations for R_q = Z_q[X]/(X^n + 1)
5. Has `ring_params` record and `ring_context` locale
6. Exports to Haskell
