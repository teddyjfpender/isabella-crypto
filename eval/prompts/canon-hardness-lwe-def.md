# Prompt ID: canon-hardness-lwe-def

## Task

Create the Canon/Hardness/LWE_Def.thy theory file - Learning With Errors problem definition.

This theory provides the formal definition of the LWE problem, which is the security foundation for lattice-based cryptography. It defines the LWE sample generation and the Search/Decision variants of the problem.

**Key principle**: This theory defines the *problem*, not the *encryption scheme*. Regev PKE will be defined separately in Crypto/Regev_PKE.thy using these definitions.

## Note on Theory Structure

The step-loop provides the theory header automatically. Your steps output content for inside `begin...end`.

**IMPORTANT**:
- `inner_prod`, `mat_vec_mult`, `valid_vec`, `valid_matrix` are in ListVec.thy
- `vec_mod`, `dist0`, `all_bounded` are in Zq.thy and Norms.thy
- Do NOT redefine these functions

## Step-Loop Invocation

```bash
./ralph/step-loop.sh --prompt canon-hardness-lwe-def \
    --output-dir Canon \
    --theory-name LWE_Def \
    --theory-path Hardness \
    --session Canon_Hardness \
    --imports 'Canon_Base.Prelude Canon_Base.ListVec Canon_Base.Zq Canon_Base.Norms' \
    --parent-session Canon_Base \
    --session-dir Canon
```

**Prerequisites**: Prelude, ListVec, Zq, and Norms must be completed first.

## Proof Robustness Guidelines

**CRITICAL**: Follow these rules for robust proofs that work across Isabelle versions.

1. **If exact code is provided, USE IT EXACTLY** - do not simplify or "improve"
2. **Type annotations** are required for numeric lemmas - e.g., `(n::nat)`, `(q::int)`
3. **Explicit case splits** for conditionals - use `proof (cases "condition")`
4. **Use `arith` or `linarith`** for integer inequalities
5. **Name intermediate facts** for readability and debugging
6. **Record types**: use `\<lparr> field1 = v1, field2 = v2 \<rparr>` syntax
7. **Locale assumptions** should be minimal but sufficient

## Steps

### Step 1: LWE Parameters Record

Define a record to hold LWE parameters in a clean, reusable way.

**USE THIS EXACT CODE**:
```isabelle
text \<open>
  LWE Parameters:
  - n: dimension of secret vector s
  - m: number of LWE samples (rows of matrix A)
  - q: modulus (positive integer)
  - B_s: bound on secret coefficients (for short-secret variant)
  - B_e: bound on error coefficients
\<close>

record lwe_params =
  lwe_n :: nat
  lwe_m :: nat
  lwe_q :: int
  lwe_Bs :: int
  lwe_Be :: int

definition valid_lwe_params :: "lwe_params \<Rightarrow> bool" where
  "valid_lwe_params p = (
    lwe_n p > 0 \<and>
    lwe_m p > 0 \<and>
    lwe_q p > 1 \<and>
    lwe_Bs p >= 0 \<and>
    lwe_Be p >= 0)"

lemma valid_lwe_params_pos:
  assumes "valid_lwe_params p"
  shows "lwe_n p > 0" "lwe_m p > 0" "lwe_q p > 1"
  using assms unfolding valid_lwe_params_def by auto
```

### Step 2: LWE Instance Type

Define the structure of an LWE instance (A, b) where b = As + e mod q.

**USE THIS EXACT CODE**:
```isabelle
text \<open>
  An LWE instance consists of:
  - A: public matrix (m x n) over Z_q
  - b: public vector (length m) where b = As + e mod q

  The secret s and error e are not part of the instance - they are witnesses.
\<close>

record lwe_instance =
  lwe_A :: int_matrix
  lwe_b :: int_vec

definition valid_lwe_instance :: "lwe_params \<Rightarrow> lwe_instance \<Rightarrow> bool" where
  "valid_lwe_instance p inst = (
    valid_matrix (lwe_A inst) (lwe_m p) (lwe_n p) \<and>
    valid_vec (lwe_b inst) (lwe_m p))"
```

### Step 3: LWE Sample Generation

The core LWE operation: compute b = As + e mod q.

**USE THIS EXACT CODE**:
```isabelle
text \<open>
  Generate an LWE sample: given matrix A, secret s, and error e,
  compute b = A * s + e mod q.
\<close>

definition lwe_sample :: "int_matrix \<Rightarrow> int_vec \<Rightarrow> int_vec \<Rightarrow> int \<Rightarrow> int_vec" where
  "lwe_sample A s e q = vec_mod (vec_add (mat_vec_mult A s) e) q"

lemma lwe_sample_length:
  "length (lwe_sample A s e q) = length A"
  unfolding lwe_sample_def
  by (simp add: vec_mod_length vec_add_length mat_vec_mult_length min_def)

lemma lwe_sample_nth:
  assumes "i < length A" "i < length e"
  shows "(lwe_sample A s e q) ! i = (inner_prod (A ! i) s + e ! i) mod q"
proof -
  have "length (mat_vec_mult A s) = length A"
    by (simp add: mat_vec_mult_length)
  hence len_add: "length (vec_add (mat_vec_mult A s) e) = min (length A) (length e)"
    by (simp add: vec_add_length)
  have i_lt: "i < length (vec_add (mat_vec_mult A s) e)"
    using assms len_add by simp
  have "(lwe_sample A s e q) ! i = (vec_add (mat_vec_mult A s) e) ! i mod q"
    unfolding lwe_sample_def using i_lt by (simp add: vec_mod_nth)
  also have "(vec_add (mat_vec_mult A s) e) ! i = (mat_vec_mult A s) ! i + e ! i"
    using assms by (simp add: vec_add_def mat_vec_mult_length)
  also have "(mat_vec_mult A s) ! i = inner_prod (A ! i) s"
    using assms by (simp add: mat_vec_mult_nth)
  finally show ?thesis by simp
qed
```

### Step 4: Secret and Error Validity

Define what it means for secret and error vectors to be "small" (bounded).

**USE THIS EXACT CODE**:
```isabelle
text \<open>
  A valid secret vector has the right dimension and bounded coefficients.
  A valid error vector has the right dimension and bounded coefficients.
\<close>

definition valid_secret :: "lwe_params \<Rightarrow> int_vec \<Rightarrow> bool" where
  "valid_secret p s = (
    valid_vec s (lwe_n p) \<and>
    all_bounded s (lwe_Bs p))"

definition valid_error :: "lwe_params \<Rightarrow> int_vec \<Rightarrow> bool" where
  "valid_error p e = (
    valid_vec e (lwe_m p) \<and>
    all_bounded e (lwe_Be p))"

lemma valid_secret_length:
  "valid_secret p s \<Longrightarrow> length s = lwe_n p"
  unfolding valid_secret_def valid_vec_def by simp

lemma valid_secret_bounded:
  "valid_secret p s \<Longrightarrow> all_bounded s (lwe_Bs p)"
  unfolding valid_secret_def by simp

lemma valid_error_length:
  "valid_error p e \<Longrightarrow> length e = lwe_m p"
  unfolding valid_error_def valid_vec_def by simp

lemma valid_error_bounded:
  "valid_error p e \<Longrightarrow> all_bounded e (lwe_Be p)"
  unfolding valid_error_def by simp
```

### Step 5: LWE Instance Construction

Helper to construct a valid LWE instance from components.

**USE THIS EXACT CODE**:
```isabelle
definition make_lwe_instance :: "int_matrix \<Rightarrow> int_vec \<Rightarrow> int_vec \<Rightarrow> int \<Rightarrow> lwe_instance" where
  "make_lwe_instance A s e q = \<lparr> lwe_A = A, lwe_b = lwe_sample A s e q \<rparr>"

lemma make_lwe_instance_valid:
  assumes "valid_lwe_params p"
  assumes "valid_matrix A (lwe_m p) (lwe_n p)"
  assumes "valid_secret p s"
  assumes "valid_error p e"
  shows "valid_lwe_instance p (make_lwe_instance A s e (lwe_q p))"
proof -
  have "length (lwe_sample A s e (lwe_q p)) = length A"
    by (simp add: lwe_sample_length)
  also have "... = lwe_m p"
    using assms(2) by (simp add: valid_matrix_def)
  finally have b_len: "valid_vec (lwe_sample A s e (lwe_q p)) (lwe_m p)"
    by (simp add: valid_vec_def)
  show ?thesis
    unfolding valid_lwe_instance_def make_lwe_instance_def
    using assms(2) b_len by simp
qed
```

### Step 6: Search-LWE Problem Definition

The Search-LWE problem: given (A, b), find s such that b = As + e for small e.

**USE THIS EXACT CODE**:
```isabelle
text \<open>
  Search-LWE: Given an LWE instance (A, b), find the secret s.

  A solution is correct if there exists a small error e such that
  b = As + e mod q.
\<close>

definition is_search_lwe_solution :: "lwe_params \<Rightarrow> lwe_instance \<Rightarrow> int_vec \<Rightarrow> bool" where
  "is_search_lwe_solution p inst s = (
    valid_vec s (lwe_n p) \<and>
    (\<exists>e. valid_error p e \<and>
         lwe_b inst = lwe_sample (lwe_A inst) s e (lwe_q p)))"

text \<open>
  Alternative formulation: the "residual" b - As mod q should be small.
\<close>

definition lwe_residual :: "lwe_instance \<Rightarrow> int_vec \<Rightarrow> int \<Rightarrow> int_vec" where
  "lwe_residual inst s q = vec_mod (vec_sub (lwe_b inst) (mat_vec_mult (lwe_A inst) s)) q"

definition is_search_lwe_solution_alt :: "lwe_params \<Rightarrow> lwe_instance \<Rightarrow> int_vec \<Rightarrow> bool" where
  "is_search_lwe_solution_alt p inst s = (
    valid_vec s (lwe_n p) \<and>
    all_bounded (vec_mod_centered (lwe_residual inst s (lwe_q p)) (lwe_q p)) (lwe_Be p))"
```

### Step 7: Decision-LWE Problem Definition

The Decision-LWE problem: distinguish (A, As+e) from (A, random).

**USE THIS EXACT CODE**:
```isabelle
text \<open>
  Decision-LWE: Distinguish between:
  - Real: (A, b) where b = As + e for small s, e
  - Random: (A, b) where b is uniformly random

  We define predicates for "is a real LWE instance" and use these
  in security definitions.
\<close>

definition is_real_lwe_instance :: "lwe_params \<Rightarrow> lwe_instance \<Rightarrow> bool" where
  "is_real_lwe_instance p inst = (
    valid_lwe_instance p inst \<and>
    (\<exists>s e. valid_secret p s \<and> valid_error p e \<and>
           lwe_b inst = lwe_sample (lwe_A inst) s e (lwe_q p)))"

text \<open>
  A "witness" for a real LWE instance is the (s, e) pair.
\<close>

definition lwe_witness_valid :: "lwe_params \<Rightarrow> lwe_instance \<Rightarrow> int_vec \<Rightarrow> int_vec \<Rightarrow> bool" where
  "lwe_witness_valid p inst s e = (
    valid_secret p s \<and>
    valid_error p e \<and>
    lwe_b inst = lwe_sample (lwe_A inst) s e (lwe_q p))"

lemma real_lwe_has_witness:
  "is_real_lwe_instance p inst \<longleftrightarrow>
   valid_lwe_instance p inst \<and> (\<exists>s e. lwe_witness_valid p inst s e)"
  unfolding is_real_lwe_instance_def lwe_witness_valid_def by auto
```

### Step 8: LWE Locale for Dimension Tracking

A locale that packages all the LWE assumptions for cleaner proofs.

**USE THIS EXACT CODE**:
```isabelle
locale lwe_context =
  fixes p :: lwe_params
    and A :: int_matrix
    and s :: int_vec
    and e :: int_vec
  assumes params_ok: "valid_lwe_params p"
    and A_ok: "valid_matrix A (lwe_m p) (lwe_n p)"
    and s_ok: "valid_secret p s"
    and e_ok: "valid_error p e"
begin

abbreviation "n \<equiv> lwe_n p"
abbreviation "m \<equiv> lwe_m p"
abbreviation "q \<equiv> lwe_q p"
abbreviation "B_s \<equiv> lwe_Bs p"
abbreviation "B_e \<equiv> lwe_Be p"

lemma n_pos: "n > 0"
  using params_ok unfolding valid_lwe_params_def by simp

lemma m_pos: "m > 0"
  using params_ok unfolding valid_lwe_params_def by simp

lemma q_pos: "q > 1"
  using params_ok unfolding valid_lwe_params_def by simp

lemma len_A: "length A = m"
  using A_ok unfolding valid_matrix_def by simp

lemma len_s: "length s = n"
  using s_ok valid_secret_length by simp

lemma len_e: "length e = m"
  using e_ok valid_error_length by simp

lemma s_bounded: "all_bounded s B_s"
  using s_ok valid_secret_bounded by simp

lemma e_bounded: "all_bounded e B_e"
  using e_ok valid_error_bounded by simp

definition "b \<equiv> lwe_sample A s e q"

definition "inst \<equiv> \<lparr> lwe_A = A, lwe_b = b \<rparr>"

lemma b_length: "length b = m"
  unfolding b_def using lwe_sample_length len_A by simp

lemma inst_valid: "valid_lwe_instance p inst"
  unfolding inst_def valid_lwe_instance_def
  using A_ok b_length by (simp add: valid_vec_def)

lemma inst_is_real: "is_real_lwe_instance p inst"
  unfolding is_real_lwe_instance_def inst_def b_def
  using inst_valid s_ok e_ok
  unfolding inst_def valid_lwe_instance_def
  by auto

end
```

### Step 9: Code Export

**USE THIS EXACT CODE**:
```isabelle
export_code
  lwe_params.make valid_lwe_params
  lwe_n lwe_m lwe_q lwe_Bs lwe_Be
  lwe_instance.make valid_lwe_instance
  lwe_A lwe_b
  lwe_sample make_lwe_instance
  valid_secret valid_error
  is_search_lwe_solution lwe_residual
  is_real_lwe_instance lwe_witness_valid
  in Haskell module_name "Canon.Hardness.LWE_Def"
```

## Constraints

- Theory name: `LWE_Def`
- Session: `Canon_Hardness` (depends on `Canon_Base`)
- Imports: Prelude, ListVec, Zq, Norms
- No sorry/oops - all proofs must be complete
- Records use `\<lparr> ... \<rparr>` syntax
- All validity predicates should be checkable

## Proof Strategy Reference

| Goal Type | Recommended Tactic |
|-----------|-------------------|
| Record field access | `by simp` |
| Validity unfolding | `unfolding valid_foo_def by simp` |
| Existential intro | `by (intro exI) auto` |
| Length preservation | `by (simp add: dim_simp)` |
| Using locale facts | `using fact_name by simp` |

## Key Insights

1. **Separation of concerns**: LWE_Def defines the *problem*, not the *scheme*
2. **Parameters as record**: Clean packaging allows different instantiations
3. **Witness-based definitions**: `is_real_lwe_instance` uses existential witness
4. **Locale for proofs**: `lwe_context` packages assumptions for downstream use
5. **Two Search-LWE formulations**: Direct (find s,e) and residual-based (b - As is small)
6. **No encode/decode here**: Those are in Zq.thy for Regev_PKE to use

## Deliverable

A working LWE_Def.thy that:
1. Compiles as part of Canon_Hardness session
2. Defines LWE parameters and instance types
3. Provides `lwe_sample` for generating LWE instances
4. Defines Search-LWE and Decision-LWE problems
5. Has `lwe_context` locale for structured proofs
6. Exports to Haskell
