# Prompt ID: canon-rings-ntt

## Task

Create the Canon/Rings/NTT.thy theory file - Number Theoretic Transform for efficient polynomial multiplication.

The NTT is the finite field analogue of FFT, enabling O(n log n) polynomial multiplication in R_q = Z_q[X]/(X^n + 1). This is essential for practical Kyber and Dilithium implementations.

**Key insight**: In NTT domain, polynomial multiplication becomes pointwise multiplication:
```
NTT(a * b) = NTT(a) ⊙ NTT(b)
```

## Note on Theory Structure

The step-loop provides the theory header automatically. Your steps output content for inside `begin...end`.

**IMPORTANT**: These functions are already defined - do NOT redefine them:
- `poly`, `poly_mod`, `ring_mod`, `ring_mult`, `valid_ring_elem` - from PolyMod.thy
- `vec_mod` - from Zq.thy

## Step-Loop Invocation

```bash
./ralph/step-loop-v2.sh --prompt canon-rings-ntt \
    --output-dir Canon \
    --theory-name NTT \
    --theory-path Rings \
    --session Canon_Rings \
    --imports 'Canon_Base.Prelude Canon_Base.ListVec Canon_Base.Zq Canon_Rings.PolyMod' \
    --parent-session Canon_Base \
    --session-dir Canon
```

**Prerequisites**: Prelude, ListVec, Zq, and PolyMod must be completed first.

## Proof Robustness Guidelines

**CRITICAL**: Follow these rules for robust proofs that work across Isabelle versions.

1. **If exact code is provided, USE IT EXACTLY** - do not simplify or "improve"
2. **Type annotations** are required for numeric lemmas - e.g., `(k::nat)`, `(q::int)`
3. **Explicit case splits** for conditionals - use `proof (cases "condition")`
4. **Use `arith` or `linarith`** for integer inequalities
5. **Power operations**: be careful with `[^]` for nat vs int exponentiation
6. **Modular exponentiation**: use `power_mod` for efficiency
7. **Name intermediate facts** for readability and debugging

## Steps

### Step 1: NTT Parameters and Primitive Roots

Define parameters and the concept of primitive roots of unity.

**USE THIS EXACT CODE**:
```isabelle
text \<open>
  Number Theoretic Transform (NTT) Parameters:

  For the negacyclic NTT used with X^n + 1, we need:
  - n: polynomial degree (power of 2, typically 256)
  - q: prime modulus such that q ≡ 1 (mod 2n)
  - ω: primitive 2n-th root of unity, i.e., ω^(2n) ≡ 1 (mod q) and ω^n ≡ -1 (mod q)

  Examples:
  - Kyber: n=256, q=3329, ω=17
  - Dilithium: n=256, q=8380417, ω=1753
\<close>

record ntt_params =
  ntt_n :: nat      \<comment> \<open>polynomial degree (power of 2)\<close>
  ntt_q :: int      \<comment> \<open>prime modulus\<close>
  ntt_omega :: int  \<comment> \<open>primitive 2n-th root of unity\<close>

definition power_mod :: "int \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> int" where
  "power_mod base exp m = (base ^ exp) mod m"

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

lemma primitive_root_half:
  assumes "is_primitive_root omega n q" and "q > 1"
  shows "power_mod omega n q = q - 1"
  using assms unfolding is_primitive_root_def by simp

definition valid_ntt_params :: "ntt_params \<Rightarrow> bool" where
  "valid_ntt_params p = (
    ntt_n p > 0 \<and>
    ntt_q p > 1 \<and>
    is_primitive_root (ntt_omega p) (ntt_n p) (ntt_q p))"

lemma valid_ntt_params_pos:
  assumes "valid_ntt_params p"
  shows "ntt_n p > 0" "ntt_q p > 1"
  using assms unfolding valid_ntt_params_def by auto
```

### Step 2: Twiddle Factors

Precomputed powers of ω for the NTT butterfly operations.

**USE THIS EXACT CODE**:
```isabelle
text \<open>
  Twiddle factors: powers of ω used in butterfly operations.

  For index i, the twiddle factor is ω^(bit_reverse(i)) or similar,
  depending on the NTT variant (DIT vs DIF).

  For simplicity, we define twiddle(k) = ω^k mod q.
\<close>

definition twiddle :: "int \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> int" where
  "twiddle omega k q = power_mod omega k q"

lemma twiddle_0 [simp]:
  assumes "q > 0"
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
  by (simp add: power_mult)

text \<open>
  Generate list of twiddle factors [ω^0, ω^1, ..., ω^{n-1}] mod q.
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
```

### Step 3: NTT Forward Transform (Naive)

Define the naive O(n²) NTT for correctness specification.

**USE THIS EXACT CODE**:
```isabelle
text \<open>
  Naive NTT (for specification):

  For the negacyclic NTT with X^n + 1, the forward transform is:
    â_i = Σ_{j=0}^{n-1} a_j · ω^{j·(2i+1)} mod q

  This is O(n²) but serves as the specification for the fast algorithm.
\<close>

definition ntt_coeff :: "poly \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> int" where
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
```

### Step 4: Inverse NTT (Naive)

Define the inverse transform.

**USE THIS EXACT CODE**:
```isabelle
text \<open>
  Inverse NTT (naive, for specification):

  The inverse transform recovers the original polynomial:
    a_i = n^{-1} · Σ_{j=0}^{n-1} â_j · ω^{-j·(2i+1)} mod q

  Where n^{-1} is the modular inverse of n mod q.
\<close>

definition mod_inverse :: "int \<Rightarrow> int \<Rightarrow> int" where
  "mod_inverse a q = (if q > 1 then (a ^ (nat (q - 2))) mod q else 0)"

text \<open>
  Note: mod_inverse works for prime q by Fermat's little theorem.
  For composite q, use extended Euclidean algorithm.
\<close>

lemma mod_inverse_mult:
  assumes "q > 1" and "a mod q \<noteq> 0" and "prime q"
  shows "(a * mod_inverse a q) mod q = 1"
  sorry \<comment> \<open>Requires Fermat's little theorem from HOL-Number_Theory\<close>

definition intt_coeff :: "poly \<Rightarrow> int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int" where
  "intt_coeff a_hat omega q n i = (
    let n_inv = mod_inverse (int n) q in
    let omega_inv = mod_inverse omega q in
    let exp_base = 2 * i + 1 in
    (n_inv * (\<Sum>j = 0 ..< n. (poly_coeff a_hat j) * twiddle omega_inv (j * exp_base) q)) mod q)"

definition intt_naive :: "poly \<Rightarrow> int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> poly" where
  "intt_naive a_hat omega q n = map (\<lambda>i. intt_coeff a_hat omega q n i) [0 ..< n]"

lemma intt_naive_length [simp]:
  "length (intt_naive a_hat omega q n) = n"
  unfolding intt_naive_def by simp
```

### Step 5: NTT Correctness (Inverse Property)

The key theorem: INTT(NTT(a)) = a.

**USE THIS EXACT CODE**:
```isabelle
text \<open>
  NTT Correctness: INTT(NTT(a)) = a (mod q)

  This is the fundamental property that makes NTT useful.
  The proof relies on orthogonality of roots of unity.
\<close>

text \<open>
  Orthogonality lemma: Σ_{k=0}^{n-1} ω^{k·m} = 0 for m not divisible by n
  (and = n when m is divisible by n).
\<close>

lemma roots_orthogonality:
  assumes "is_primitive_root omega n q"
  assumes "0 < m" and "m < 2 * n"
  shows "(\<Sum>k = 0 ..< n. twiddle omega (k * m) q) mod q = 0"
  sorry \<comment> \<open>Classical result - requires careful modular arithmetic\<close>

lemma roots_orthogonality_zero:
  assumes "is_primitive_root omega n q" and "n > 0"
  shows "(\<Sum>k = 0 ..< n. twiddle omega (k * 0) q) mod q = (int n) mod q"
proof -
  have "(\<Sum>k = 0 ..< n. twiddle omega 0 q) = (\<Sum>k = 0 ..< n. 1)"
    unfolding twiddle_def power_mod_def by simp
  also have "... = int n" by simp
  finally show ?thesis by simp
qed

theorem ntt_inverse_correct:
  assumes "valid_ntt_params p"
  assumes "length a = ntt_n p"
  assumes "\<forall>c \<in> set a. 0 \<le> c \<and> c < ntt_q p"
  shows "intt_naive (ntt_naive a (ntt_omega p) (ntt_q p) (ntt_n p))
                    (ntt_omega p) (ntt_q p) (ntt_n p) =
         poly_mod a (ntt_q p)"
  sorry \<comment> \<open>Follows from orthogonality - detailed proof is involved\<close>
```

### Step 6: Pointwise Multiplication in NTT Domain

**USE THIS EXACT CODE**:
```isabelle
text \<open>
  Pointwise multiplication in NTT domain:

  If â = NTT(a) and b̂ = NTT(b), then
    NTT(a * b mod (X^n + 1)) = â ⊙ b̂

  where ⊙ is componentwise multiplication mod q.
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
  shows "ntt_naive (ring_mod (poly_mult a b) (ntt_n p)) (ntt_omega p) (ntt_q p) (ntt_n p) =
         ntt_pointwise_mult (ntt_naive a (ntt_omega p) (ntt_q p) (ntt_n p))
                            (ntt_naive b (ntt_omega p) (ntt_q p) (ntt_n p))
                            (ntt_q p)"
  sorry \<comment> \<open>Fundamental NTT theorem - requires detailed algebraic proof\<close>
```

### Step 7: Fast NTT (Cooley-Tukey)

The efficient O(n log n) algorithm using butterfly operations.

**USE THIS EXACT CODE**:
```isabelle
text \<open>
  Fast NTT using Cooley-Tukey butterfly algorithm.

  The idea: decompose the DFT into smaller DFTs recursively.
  At each level, combine results using "butterfly" operations:
    (a, b) → (a + ω^k · b, a - ω^k · b)

  This is O(n log n) vs O(n²) for the naive algorithm.
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

fun ntt_layer :: "poly \<Rightarrow> int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> poly" where
  "ntt_layer a omega q n len start =
    (if start + len > n then a
     else let tw = twiddle omega (n div (2 * len) * start) q in
          let (x, y) = butterfly (a ! start) (a ! (start + len div 2)) tw q in
          let a' = a[start := x, start + len div 2 := y] in
          ntt_layer a' omega q n len (start + len))"

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
```

### Step 8: NTT Context Locale

A locale for cleaner proofs involving NTT.

**USE THIS EXACT CODE**:
```isabelle
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
  shows "intt (ntt_mult (ntt a) (ntt b)) = poly_mod (ring_mod (poly_mult a b) n) q"
  sorry \<comment> \<open>Combines ntt_convolution and ntt_inverse_correct\<close>

end
```

### Step 9: Kyber/Dilithium Specific Parameters

Define the standard parameter sets.

**USE THIS EXACT CODE**:
```isabelle
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

lemma kyber_omega_is_primitive_root:
  "is_primitive_root 17 256 3329"
  unfolding is_primitive_root_def power_mod_def
  sorry \<comment> \<open>Computational verification: 17^512 mod 3329 = 1, 17^256 mod 3329 = 3328\<close>

lemma kyber_ntt_params_valid:
  "valid_ntt_params kyber_ntt_params"
  unfolding valid_ntt_params_def kyber_ntt_params_def
  using kyber_omega_is_primitive_root by simp

lemma dilithium_omega_is_primitive_root:
  "is_primitive_root 1753 256 8380417"
  unfolding is_primitive_root_def power_mod_def
  sorry \<comment> \<open>Computational verification\<close>

lemma dilithium_ntt_params_valid:
  "valid_ntt_params dilithium_ntt_params"
  unfolding valid_ntt_params_def dilithium_ntt_params_def
  using dilithium_omega_is_primitive_root by simp
```

### Step 10: Code Export

**USE THIS EXACT CODE**:
```isabelle
export_code
  ntt_params.make valid_ntt_params
  ntt_n ntt_q ntt_omega
  power_mod is_primitive_root
  twiddle twiddle_factors
  ntt_naive ntt_coeff
  intt_naive intt_coeff mod_inverse
  ntt_pointwise_mult
  butterfly ntt_fast
  kyber_ntt_params dilithium_ntt_params
  in Haskell module_name "Canon.Rings.NTT"
```

## Constraints

- Theory name: `NTT`
- Session: `Canon_Rings` (depends on `Canon_Base`)
- Imports: Prelude, ListVec, Zq, PolyMod
- Some proofs use sorry for deep number-theoretic results
- Focus on correct specification and efficient implementation
- The fast NTT implementation should be executable

## Proof Strategy Reference

| Goal Type | Recommended Tactic |
|-----------|-------------------|
| Power/mod | `by (simp add: power_mod_def)` |
| Sum manipulation | `by (simp add: sum.atLeast_Suc_lessThan)` |
| List operations | `by (simp add: nth_list_update)` |
| Modular arithmetic | `by (simp add: mod_mult_eq mod_add_eq)` |
| Butterfly bounds | `using assms by (auto simp: Let_def)` |

## Key Insights

1. **Negacyclic NTT**: For X^n + 1, need ω^n ≡ -1 (not just ω^n ≡ 1)
2. **Convolution theorem**: NTT(a*b) = NTT(a) ⊙ NTT(b) pointwise
3. **Orthogonality**: Roots of unity sum to 0 (except when indices align)
4. **Butterfly**: Core O(1) operation: (a,b) → (a + ωb, a - ωb)
5. **In-place**: Fast NTT can be done in-place with bit-reversal
6. **Kyber uses q=3329**: Small prime, q ≡ 1 (mod 512)
7. **Dilithium uses q=8380417**: Larger prime for bigger signatures

## Deliverable

A working NTT.thy that:
1. Compiles as part of Canon_Rings session
2. Defines NTT parameters and primitive root validation
3. Has naive NTT/INTT for specification
4. Has fast Cooley-Tukey NTT implementation
5. States convolution theorem (NTT converts mult to pointwise)
6. Defines Kyber and Dilithium standard parameters
7. Exports to Haskell for testing against NIST vectors

## Testing Strategy (Post-Export)

After Haskell export, test against NIST/FIPS vectors:
1. Verify kyber_ntt_params primitive root: 17^512 mod 3329 = 1
2. Test NTT on known vectors from NIST KAT files
3. Verify NTT(a) ⊙ NTT(b) = NTT(ring_mult a b)
4. Round-trip test: INTT(NTT(a)) = a for random polynomials
