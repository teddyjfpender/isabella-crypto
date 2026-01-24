# Prompt ID: canon-algebra-zq

## Task

Create the Canon/Algebra/Zq.thy theory file - modular arithmetic and decoding infrastructure.

This theory provides the Z_q abstraction and the critical `dist0`/`decode_bit` machinery used in all LWE-based schemes.

## Note on Theory Structure

The step-loop provides the theory header automatically. Your steps output content for inside `begin...end`.

**IMPORTANT**: `mod_centered` is already defined in Prelude.thy. Do NOT redefine it.

## Step-Loop Invocation

```bash
./ralph/step-loop.sh --prompt canon-algebra-zq \
    --output-dir Canon \
    --theory-name Zq \
    --theory-path Algebra \
    --session Canon_Base \
    --imports 'Canon_Base.Prelude Canon_Base.ListVec' \
    --parent-session Canon_Base \
    --session-dir Canon
```

**Prerequisite**: ListVec must be completed first since Zq depends on it for vector operations.

## Proof Robustness Guidelines

**CRITICAL**: Follow these rules for robust proofs that work across Isabelle versions.

1. **If exact code is provided, USE IT EXACTLY** - do not simplify or "improve"
2. **Type annotations** are required for numeric lemmas - e.g., `(n::int)`
3. **Explicit case splits** for conditionals - use `proof (cases "condition")`
4. **Use `arith` for arithmetic** involving nat/int inequalities with div/mod
5. **Name intermediate facts** for readability and debugging
6. **AVOID `...` chaining** with `simp add: algebra_simps` on complex expressions - causes infinite loops
7. **Use explicit terms** in calculations rather than `...`

## Steps

### Step 1: Additional Centered Mod Lemmas

Note: `mod_centered` is already defined in Prelude. Add these additional lemmas.

**USE THIS EXACT CODE**:
```isabelle
lemma mod_centered_cong [mod_simp]:
  assumes "(q::int) > 0"
  shows "mod_centered x q mod q = x mod q"
proof (cases "x mod q > q div 2")
  case True
  have "mod_centered x q = x mod q - q"
    unfolding mod_centered_def Let_def using True by simp
  hence "mod_centered x q mod q = (x mod q - q) mod q"
    by simp
  also have "(x mod q - q) mod q = x mod q"
  proof -
    have "(x mod q - q) mod q = (x mod q + (-1) * q) mod q" by simp
    also have "... = x mod q mod q" using assms by (simp add: mod_mult_self2)
    also have "... = x mod q" by simp
    finally show ?thesis .
  qed
  finally show ?thesis .
next
  case False
  then show ?thesis
    unfolding mod_centered_def Let_def by simp
qed

lemma mod_centered_zero [mod_simp]:
  assumes "(q::int) > 0"
  shows "mod_centered 0 q = 0"
  unfolding mod_centered_def Let_def using assms by simp

lemma mod_centered_abs_bound:
  assumes "(q::int) > 0"
  shows "abs (mod_centered x q) <= q div 2"
proof (cases "x mod q > q div 2")
  case True
  have mc: "mod_centered x q = x mod q - q"
    unfolding mod_centered_def Let_def using True by simp
  have "x mod q < q" using assms by simp
  hence "x mod q - q < 0" by arith
  hence neg: "mod_centered x q < 0" using mc by simp
  have "x mod q - q > -(q div 2 + 1)"
  proof -
    have "x mod q > q div 2" using True by simp
    have "q div 2 - q >= -(q div 2 + 1)"
      by (simp add: div_plus_div_distrib_dvd_left)
    thus ?thesis using True by arith
  qed
  hence "mod_centered x q > -(q div 2 + 1)" using mc by simp
  hence "-(mod_centered x q) < q div 2 + 1" by arith
  hence "-(mod_centered x q) <= q div 2" by arith
  thus ?thesis using neg by simp
next
  case False
  have mc: "mod_centered x q = x mod q"
    unfolding mod_centered_def Let_def using False by simp
  have "x mod q >= 0" using assms by simp
  hence "mod_centered x q >= 0" using mc by simp
  moreover have "mod_centered x q <= q div 2" using mc False by simp
  ultimately show ?thesis by simp
qed
```

### Step 2: Vector Modular Operations

**USE THIS EXACT CODE**:
```isabelle
definition vec_mod :: "int_vec => int => int_vec" where
  "vec_mod v q = map (\<lambda>x. x mod q) v"

definition vec_mod_centered :: "int_vec => int => int_vec" where
  "vec_mod_centered v q = map (\<lambda>x. mod_centered x q) v"

lemma vec_mod_length [dim_simp]:
  "length (vec_mod v q) = length v"
  unfolding vec_mod_def by simp

lemma vec_mod_centered_length [dim_simp]:
  "length (vec_mod_centered v q) = length v"
  unfolding vec_mod_centered_def by simp

lemma vec_mod_nth:
  assumes "i < length v"
  shows "(vec_mod v q) ! i = (v ! i) mod q"
  unfolding vec_mod_def using assms by simp

lemma vec_mod_idemp [mod_simp]:
  assumes "(q::int) > 0"
  shows "vec_mod (vec_mod v q) q = vec_mod v q"
  unfolding vec_mod_def by (simp add: map_map comp_def)
```

### Step 3: Distance from Zero

This is the critical definition for decryption correctness.

**USE THIS EXACT CODE**:
```isabelle
definition dist0 :: "int => int => int" where
  "dist0 q x = abs (mod_centered x q)"

lemma dist0_nonneg [dist_simp]:
  "dist0 q x >= 0"
  unfolding dist0_def by simp

lemma dist0_bound [dist_simp]:
  assumes "(q::int) > 0"
  shows "dist0 q x <= q div 2"
  unfolding dist0_def using mod_centered_abs_bound[OF assms] by simp

lemma dist0_zero [dist_simp]:
  assumes "(q::int) > 0"
  shows "dist0 q 0 = 0"
  unfolding dist0_def mod_centered_zero[OF assms] by simp

lemma dist0_mod [dist_simp]:
  assumes "(q::int) > 0"
  shows "dist0 q (x mod q) = dist0 q x"
proof -
  have "mod_centered (x mod q) q = mod_centered x q"
    unfolding mod_centered_def Let_def by simp
  thus ?thesis unfolding dist0_def by simp
qed
```

### Step 4: Key Distance Lemma - Small Values

This lemma says: small values stay small after mod_centered.

**USE THIS EXACT CODE**:
```isabelle
lemma dist0_small:
  assumes q_pos: "(q::int) > 0"
  assumes x_small: "abs x < q div 2"
  assumes x_nonneg_or_neg: "x >= 0 \<or> x < 0"
  shows "dist0 q x = abs x"
proof (cases "x >= 0")
  case True
  hence x_eq: "x mod q = x"
    using x_small q_pos by simp
  have "x <= q div 2" using x_small True by arith
  hence not_gt: "\<not> (x mod q > q div 2)"
    using x_eq x_small True by arith
  have "mod_centered x q = x mod q"
    unfolding mod_centered_def Let_def using not_gt by simp
  hence "mod_centered x q = x" using x_eq by simp
  thus ?thesis unfolding dist0_def using True by simp
next
  case False
  hence x_neg: "x < 0" by simp
  have x_gt: "x > -q div 2 - 1" using x_small by arith
  have "x mod q = x + q"
  proof -
    have "x + q >= 0" using x_gt q_pos by arith
    moreover have "x + q < q" using x_neg by arith
    ultimately show ?thesis
      using q_pos by (simp add: mod_pos_pos_trivial)
  qed
  hence xmod_eq: "x mod q = x + q" .
  have "x + q > q div 2"
  proof -
    have "x > -(q div 2) - 1" using x_small by arith
    hence "x + q > q - q div 2 - 1" by arith
    have "q - q div 2 - 1 >= q div 2 - 1"
      using q_pos by arith
    thus ?thesis using x_small q_pos by arith
  qed
  hence gt_half: "x mod q > q div 2" using xmod_eq by simp
  have "mod_centered x q = x mod q - q"
    unfolding mod_centered_def Let_def using gt_half by simp
  hence "mod_centered x q = x" using xmod_eq by simp
  thus ?thesis unfolding dist0_def using x_neg by simp
qed
```

### Step 5: Bit Encoding and Decoding

**USE THIS EXACT CODE**:
```isabelle
definition encode_bit :: "int => bool => int" where
  "encode_bit q b = (if b then q div 2 else 0)"

definition decode_bit :: "int => int => bool" where
  "decode_bit q x = (dist0 q x > q div 4)"

lemma encode_bit_False:
  "encode_bit q False = 0"
  unfolding encode_bit_def by simp

lemma encode_bit_True:
  "encode_bit q True = q div 2"
  unfolding encode_bit_def by simp
```

### Step 6: Encoding/Decoding Correctness

**USE THIS EXACT CODE**:
```isabelle
lemma encode_decode_inverse:
  assumes q_gt: "(q::int) > 2"
  shows "decode_bit q (encode_bit q b) = b"
proof (cases b)
  case False
  have enc: "encode_bit q False = 0" by (simp add: encode_bit_def)
  have "dist0 q 0 = 0"
    unfolding dist0_def mod_centered_def Let_def using q_gt by simp
  hence "dist0 q (encode_bit q False) = 0" using enc by simp
  moreover have "q div 4 >= 0" using q_gt by simp
  ultimately have "\<not> (dist0 q (encode_bit q False) > q div 4)"
    by arith
  thus ?thesis unfolding decode_bit_def using False by simp
next
  case True
  have enc: "encode_bit q True = q div 2" by (simp add: encode_bit_def)
  have q4_pos: "q div 4 >= 0" using q_gt by simp
  have q2_pos: "q div 2 > 0" using q_gt by arith
  have half_bound: "q div 2 <= q div 2" by simp
  have half_mod: "(q div 2) mod q = q div 2"
    using q_gt q2_pos by simp
  have not_gt: "\<not> ((q div 2) mod q > q div 2)"
    using half_mod half_bound by simp
  have "mod_centered (q div 2) q = (q div 2) mod q"
    unfolding mod_centered_def Let_def using not_gt by simp
  hence mc_eq: "mod_centered (q div 2) q = q div 2"
    using half_mod by simp
  have "dist0 q (q div 2) = q div 2"
    unfolding dist0_def mc_eq using q2_pos by simp
  hence "dist0 q (encode_bit q True) = q div 2" using enc by simp
  moreover have "q div 2 > q div 4" using q_gt by arith
  ultimately have "dist0 q (encode_bit q True) > q div 4" by arith
  thus ?thesis unfolding decode_bit_def using True by simp
qed
```

### Step 7: Noisy Decoding - False Case

**USE THIS EXACT CODE**:
```isabelle
lemma decode_bit_small:
  assumes q_pos: "(q::int) > 0"
  assumes x_small: "abs x < q div 4"
  shows "decode_bit q x = False"
proof -
  have q4_le_q2: "q div 4 <= q div 2" using q_pos by arith
  have x_lt_half: "abs x < q div 2" using x_small q4_le_q2 by arith
  have "dist0 q x = abs x"
    by (rule dist0_small[OF q_pos x_lt_half]) simp
  hence "dist0 q x < q div 4" using x_small by simp
  thus ?thesis unfolding decode_bit_def by arith
qed
```

### Step 8: Noisy Decoding - True Case

**USE THIS EXACT CODE**:
```isabelle
lemma decode_bit_half_shift:
  assumes q_pos: "(q::int) > 0"
  assumes q_div4: "q mod 4 = 0"
  assumes x_small: "abs x < q div 4"
  shows "decode_bit q (x + q div 2) = True"
proof -
  have q4_pos: "q div 4 > 0" using q_pos q_div4 by arith
  have q2_eq: "q div 2 = 2 * (q div 4)"
    using q_div4 by arith
  have q2_pos: "q div 2 > 0" using q4_pos q2_eq by arith

  (* x + q div 2 is in range (q div 4, 3 * q div 4) *)
  have lb: "x + q div 2 > q div 4"
    using x_small q2_eq by arith
  have ub: "x + q div 2 < 3 * (q div 4)"
    using x_small q2_eq by arith

  (* This is in the positive part of (-q/2, q/2] after centering *)
  have in_range: "x + q div 2 >= 0 \<and> x + q div 2 < q"
  proof -
    have "x + q div 2 >= -(q div 4) + q div 2"
      using x_small by arith
    hence "x + q div 2 >= q div 4"
      using q2_eq by arith
    hence low: "x + q div 2 >= 0" using q4_pos by arith
    have "x + q div 2 < q div 4 + q div 2"
      using x_small by arith
    hence "x + q div 2 < 3 * (q div 4)"
      using q2_eq by arith
    hence high: "x + q div 2 < q"
      using q_div4 by arith
    show ?thesis using low high by simp
  qed

  have xmod_eq: "(x + q div 2) mod q = x + q div 2"
    using in_range q_pos by simp

  (* Determine if > q div 2 *)
  have le_half: "x + q div 2 <= q div 2"
    using x_small by arith

  have mc_eq: "mod_centered (x + q div 2) q = x + q div 2"
    unfolding mod_centered_def Let_def
    using xmod_eq le_half by simp

  have "dist0 q (x + q div 2) = abs (x + q div 2)"
    unfolding dist0_def mc_eq by simp

  have "abs (x + q div 2) >= q div 2 - abs x"
  proof (cases "x >= 0")
    case True
    hence "x + q div 2 >= 0" using q2_pos by arith
    hence "abs (x + q div 2) = x + q div 2" by simp
    also have "x + q div 2 >= q div 2 - abs x"
      using True by arith
    finally show ?thesis .
  next
    case False
    hence "x < 0" by simp
    hence "x + q div 2 < q div 2" by arith
    show ?thesis
    proof (cases "x + q div 2 >= 0")
      case True
      hence "abs (x + q div 2) = x + q div 2" by simp
      also have "x + q div 2 >= q div 2 + x" by simp
      also have "q div 2 + x = q div 2 - abs x"
        using `x < 0` by simp
      finally show ?thesis .
    next
      case False
      hence neg: "x + q div 2 < 0" by simp
      hence "abs (x + q div 2) = -(x + q div 2)" by simp
      also have "-(x + q div 2) = -x - q div 2"
        by arith
      also have "-x = abs x" using `x < 0` by simp
      finally have eq: "abs (x + q div 2) = abs x - q div 2"
        by arith
      (* But this contradicts in_range *)
      have "x + q div 2 >= 0" using in_range by simp
      hence False using neg by simp
      thus ?thesis by simp
    qed
  qed

  have "abs (x + q div 2) > q div 4"
  proof -
    have "q div 2 - abs x > q div 2 - q div 4"
      using x_small by arith
    hence "q div 2 - abs x > q div 4"
      using q2_eq by arith
    thus ?thesis using `abs (x + q div 2) >= q div 2 - abs x` by arith
  qed

  hence "dist0 q (x + q div 2) > q div 4"
    using `dist0 q (x + q div 2) = abs (x + q div 2)` by simp

  thus ?thesis unfolding decode_bit_def by simp
qed
```

### Step 9: Matrix-Vector Mod and Code Export

**USE THIS EXACT CODE**:
```isabelle
definition mat_vec_mult_mod :: "int_matrix => int_vec => int => int_vec" where
  "mat_vec_mult_mod A v q = vec_mod (mat_vec_mult A v) q"

lemma mat_vec_mult_mod_length [dim_simp]:
  "length (mat_vec_mult_mod A v q) = length A"
  unfolding mat_vec_mult_mod_def vec_mod_length mat_vec_mult_length by simp

export_code
  mod_centered vec_mod vec_mod_centered
  dist0 encode_bit decode_bit
  mat_vec_mult_mod
  in Haskell module_name "Canon.Algebra.Zq"
```

## Constraints

- Theory name: `Zq`
- Imports: Prelude (for mod_centered) and ListVec (for vector operations)
- No sorry/oops - all proofs must be complete
- All mod lemmas declared [mod_simp]
- All dist lemmas declared [dist_simp]
- All dimension lemmas declared [dim_simp]

## Proof Strategy Reference

| Goal Type | Recommended Tactic |
|-----------|-------------------|
| Definition unfolding | `unfolding foo_def by simp` |
| Case split on condition | `proof (cases "condition")` |
| Integer arithmetic with div | `by arith` |
| Using named fact | `using fact_name by simp` |
| Sum/product congruence | `by (intro sum.cong refl) simp` |
| Mod equivalence | `by (simp add: mod_simp)` |

## Key Insights

1. **dist0 uses abs of mod_centered** - this simplifies many proofs
2. **dist0_small** requires careful case analysis on sign of x
3. **decode_bit_half_shift** uses the `q mod 4 = 0` assumption to ensure q/2 is even
4. **Avoid `...` in chained calculations** - use explicit terms instead
5. **Type annotations `(q::int)` are essential** for numeric lemmas to work
