# Prompt ID: canon-prelude

## Task

Create the Canon/Prelude.thy theory file - foundational infrastructure for the Lattice Crypto Canon.

This theory provides:
- Named theorem collections for organized simp rules
- Declarations of existing HOL lemmas into those collections
- A few utility definitions

**Important**: Many mod/arithmetic lemmas already exist in HOL-Number_Theory. Don't re-prove them - just declare them into named_theorems.

## Note on Theory Structure

The step-loop provides the theory header automatically. Your steps output content for inside `begin...end`.

## Proof Robustness Guidelines

**CRITICAL**: Do not rely on `auto` or `simp` to magically solve complex goals. These tactics are non-deterministic and may fail across Isabelle versions.

1. **Use explicit case splits** for conditionals (`if-then-else`) - use `proof (cases "condition")`
2. **Type annotations are required** when working with numeric types - e.g., `(n::int)`
3. **Prefer `arith` over `auto`** for arithmetic goals involving `div`/`mod`
4. **Name intermediate facts** to make proofs more readable and debuggable
5. **If exact code is provided, use it exactly** - don't simplify or "improve" it

## Steps

### Step 1: Named Theorem Collections

Define named_theorems for collecting simp rules by category:

**USE THIS EXACT CODE**:
```isabelle
named_theorems mod_simp "modular arithmetic simplification rules"
named_theorems vec_simp "vector operation simplification rules"
named_theorems mat_simp "matrix operation simplification rules"
named_theorems dim_simp "dimension preservation rules"
named_theorems dist_simp "distance and decoding rules"
```

### Step 2: Declare Existing Mod Lemmas

The following lemmas already exist in HOL. Declare them into mod_simp:

**USE THIS EXACT CODE**:
```isabelle
declare mod_add_eq [mod_simp]
declare mod_diff_eq [mod_simp]
declare mod_mult_eq [mod_simp]
declare mod_mod_trivial [mod_simp]
```

**Note**: These lemma names are from HOL-Number_Theory. If a name doesn't exist in your Isabelle version (compilation error "Unknown fact"), delete that line.

### Step 3: Centered Mod Definition with Hardened Proof

Define centered modular reduction (maps to range around 0):

**USE THIS EXACT CODE** - the explicit case-split proof is required for robustness:
```isabelle
definition mod_centered :: "int => int => int" where
  "mod_centered x q = (let r = x mod q in if r > q div 2 then r - q else r)"

lemma mod_centered_range:
  assumes "q > 0"
  shows "mod_centered x q > -(q div 2 + 1)" and "mod_centered x q <= q div 2"
proof -
  let ?r = "x mod q"
  have r0: "0 <= ?r" and rq: "?r < q" using assms by simp_all
  have q2_nonneg: "0 <= q div 2" using assms by simp

  show "mod_centered x q > -(q div 2 + 1)"
  proof (cases "?r > q div 2")
    case False
    have "-(q div 2 + 1) < 0" using q2_nonneg by arith
    also have "0 <= ?r" using r0 by simp
    finally have "-(q div 2 + 1) < ?r" by simp
    then show ?thesis
      unfolding mod_centered_def Let_def
      using False by simp
  next
    case True
    have "q div 2 < ?r" using True by simp
    hence "?r - q > q div 2 - q" by arith
    have "q div 2 - q >= -(q div 2 + 1)"
    proof -
      have "q div 2 + (q div 2 + 1) >= q" by (simp add: div_plus_div_distrib_dvd_left)
      thus ?thesis by arith
    qed
    hence "?r - q > -(q div 2 + 1)" using True rq by arith
    then show ?thesis
      unfolding mod_centered_def Let_def
      using True by simp
  qed

  show "mod_centered x q <= q div 2"
  proof (cases "?r > q div 2")
    case False
    then show ?thesis
      unfolding mod_centered_def Let_def
      by simp
  next
    case True
    have "?r - q < 0" using rq by arith
    hence "?r - q <= q div 2" using q2_nonneg by arith
    then show ?thesis
      unfolding mod_centered_def Let_def
      using True by simp
  qed
qed
```

**Why explicit cases?** The `if-then-else` in `mod_centered` requires case analysis. Relying on `auto` to figure this out is fragile - it may work in one Isabelle version but fail in another.

### Step 4: Absolute Value Bounds

Prove that absolute value of mod result is bounded.

**USE THIS EXACT CODE** - type annotation `(n::int)` is required:
```isabelle
lemma abs_mod_less:
  assumes "(n::int) > 0"
  shows "abs (a mod n) < n"
proof -
  from assms have nonneg: "0 <= a mod n" by simp
  from assms have bound: "a mod n < n" by simp
  from nonneg have "abs (a mod n) = a mod n" by simp
  with bound show ?thesis by simp
qed
```

**Why type annotation?** Without `(n::int)`, Isabelle doesn't know which type's `mod` lemmas to apply. The simplifier needs this hint.

## Constraints

- Theory name: `Prelude`
- No sorry/oops - all proofs must be complete
- Keep it simple - this is infrastructure, not the main content
- **Use exact code when provided** - do not simplify or modify
- Use `=>` for function types in code (the step-loop handles ASCII)

## Proof Strategy Reference

| Goal Type | Recommended Tactic |
|-----------|-------------------|
| Simple arithmetic | `by simp` or `by arith` |
| Conditionals (if-then-else) | `proof (cases "condition")` |
| div/mod arithmetic | `by arith` (not `auto`) |
| Chained inequalities | Use `also/finally` pattern |
| Goals needing type info | Add type annotation to assumptions |

## Deliverable

A working Prelude.thy that:
1. Compiles with `isabelle build` without errors
2. Sets up named_theorems infrastructure
3. Has utility definitions with robust, explicit proofs
4. Uses no `sorry` or `oops`
