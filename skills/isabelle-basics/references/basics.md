# Isabelle/HOL Basics Reference

## Theory Files

Every Isabelle development is organized into **theory files** with the `.thy` extension. A theory file has this structure:

```isabelle
theory MyTheory
  imports Main
begin

(* Your definitions, lemmas, and proofs go here *)

end
```

### Theory Header

The header consists of:
- `theory Name` - must match the filename (MyTheory.thy)
- `imports` - list of theories to import

### Key Points

- Theory names must be valid identifiers (alphanumeric, underscores)
- The `begin` keyword starts the theory body
- The `end` keyword closes the theory
- Comments use `(* ... *)` or `\<comment> ...` for formal comments

## Imports

### Standard Library Imports

```isabelle
theory Example
  imports
    Main                    (* Standard HOL, includes most basics *)
    "HOL-Library.Code_Target_Numeral"  (* For efficient numeric code generation *)
    "HOL-Algebra.Ring"      (* Algebraic structures *)
    "HOL-Number_Theory.Number_Theory"  (* Number theory *)
begin
```

### Import Syntax

```isabelle
(* Single import *)
imports Main

(* Multiple imports *)
imports Main "HOL-Library.Multiset"

(* From AFP (Archive of Formal Proofs) *)
imports "Polynomial_Factorization.Polynomial_Factorization"
```

### Common Import Hierarchy

| Theory | Description |
|--------|-------------|
| `Main` | Standard HOL with lists, sets, arithmetic |
| `Complex_Main` | Adds complex numbers and analysis |
| `HOL-Library.*` | Extended library (Code_Target_Numeral, Multiset, etc.) |
| `HOL-Algebra.*` | Abstract algebra (groups, rings, fields) |
| `HOL-Number_Theory.*` | Number theory |
| `HOL-Analysis.*` | Real and complex analysis |

## Definitions

### Simple Definitions

```isabelle
(* Basic definition with type annotation *)
definition square :: "nat \<Rightarrow> nat" where
  "square n = n * n"

(* Definition without type (inferred) *)
definition double where
  "double n = n + n"

(* Multi-argument definition *)
definition add_three :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "add_three a b c = a + b + c"
```

### Definitions with Patterns

```isabelle
(* Using let expressions *)
definition compute_sum :: "nat list \<Rightarrow> nat" where
  "compute_sum xs = (let s = sum_list xs in s)"

(* Using if-then-else *)
definition safe_div :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "safe_div a b = (if b = 0 then 0 else a div b)"

(* Using case expressions *)
definition head_or_zero :: "nat list \<Rightarrow> nat" where
  "head_or_zero xs = (case xs of [] \<Rightarrow> 0 | (x # _) \<Rightarrow> x)"
```

### Abbreviations

Abbreviations are like definitions but unfold automatically:

```isabelle
(* Abbreviation - always expands in proofs *)
abbreviation is_positive :: "int \<Rightarrow> bool" where
  "is_positive n \<equiv> n > 0"

(* Compare to definition - must explicitly unfold *)
definition is_negative :: "int \<Rightarrow> bool" where
  "is_negative n = (n < 0)"
```

### Type Synonyms

```isabelle
(* Simple type synonym *)
type_synonym vector = "real list"

(* Parameterized type synonym *)
type_synonym 'a matrix = "'a list list"

(* Multiple parameters *)
type_synonym ('a, 'b) pair_list = "('a \<times> 'b) list"
```

## Lemmas and Theorems

### Basic Lemma Structure

```isabelle
lemma lemma_name:
  "statement to prove"
  proof_method

(* With explicit assumptions *)
lemma lemma_with_assumes:
  assumes "P x"
  shows "Q x"
  proof_method

(* Multiple assumptions *)
lemma multi_assume:
  assumes a1: "P x"
    and a2: "Q x"
  shows "R x"
  proof_method
```

### Lemma vs Theorem vs Corollary

```isabelle
(* All are equivalent, just semantic differences *)
lemma my_lemma: "True" by simp
theorem my_theorem: "True" by simp
corollary my_corollary: "True" by simp
proposition my_prop: "True" by simp
```

### Named Facts

```isabelle
lemma important_fact [simp]:  (* Add to simplifier *)
  "double n = n + n"
  unfolding double_def by simp

lemma another_fact [intro]:   (* Add as introduction rule *)
  "n > 0 \<Longrightarrow> n \<ge> 1"
  by simp
```

## Simple Proofs

### One-Line Proofs

```isabelle
lemma trivial: "True"
  by simp

lemma reflexive: "x = x"
  by simp

lemma arithmetic: "(2::nat) + 2 = 4"
  by simp
```

### Common Proof Methods

```isabelle
(* auto - combines simplification with classical reasoning *)
lemma auto_example: "A \<and> B \<longrightarrow> B \<and> A"
  by auto

(* simp - simplification only *)
lemma simp_example: "rev (rev xs) = xs"
  by simp

(* blast - tableau prover for first-order logic *)
lemma blast_example: "\<exists>x. P x \<Longrightarrow> \<not>(\<forall>x. \<not>P x)"
  by blast

(* force - combines auto with more aggressive tactics *)
lemma force_example: "x \<in> A \<inter> B \<longrightarrow> x \<in> A"
  by force

(* fastforce - faster but less complete than force *)
lemma fastforce_example: "x \<in> {1,2,3} \<longrightarrow> x > 0"
  by fastforce
```

### Unfolding Definitions

```isabelle
definition my_pred :: "nat \<Rightarrow> bool" where
  "my_pred n = (n > 5)"

(* Unfold definition before proving *)
lemma my_pred_10: "my_pred 10"
  unfolding my_pred_def by simp

(* Or use simp with add: *)
lemma my_pred_10': "my_pred 10"
  by (simp add: my_pred_def)
```

### Using Previous Results

```isabelle
lemma base_fact: "P x \<Longrightarrow> Q x"
  sorry (* Assume proved *)

lemma uses_base: "P x \<Longrightarrow> R x"
  using base_fact other_fact
  by auto

(* Or reference directly *)
lemma uses_base': "P x \<Longrightarrow> R x"
  by (auto dest: base_fact)
```

## Structured Proofs (Isar)

### Basic Isar Structure

```isabelle
lemma isar_example:
  assumes "A"
  shows "A \<or> B"
proof -
  from assms have "A" by simp
  thus "A \<or> B" by simp
qed
```

### Common Isar Keywords

```isabelle
lemma isar_keywords:
  assumes h: "P"
  shows "Q"
proof -
  have step1: "R"          (* Intermediate claim *)
    by auto
  from step1 have step2: "S"   (* Use previous fact *)
    by auto
  with h show "Q"          (* with = from this and *)
    by auto
qed
```

### Proof Cases

```isabelle
lemma case_example: "P \<or> Q \<Longrightarrow> Q \<or> P"
proof (cases "P")
  case True
  then show ?thesis by simp
next
  case False
  then show ?thesis by simp
qed
```

## Type System Basics

### Base Types

| Type | Description |
|------|-------------|
| `bool` | Booleans (True, False) |
| `nat` | Natural numbers (0, 1, 2, ...) |
| `int` | Integers (..., -1, 0, 1, ...) |
| `real` | Real numbers |
| `'a` | Type variable |

### Type Constructors

```isabelle
(* Lists *)
definition my_list :: "nat list" where "my_list = [1,2,3]"

(* Sets *)
definition my_set :: "nat set" where "my_set = {1,2,3}"

(* Pairs *)
definition my_pair :: "nat \<times> bool" where "my_pair = (1, True)"

(* Functions *)
definition my_fun :: "nat \<Rightarrow> nat" where "my_fun = (\<lambda>x. x + 1)"

(* Options *)
definition my_opt :: "nat option" where "my_opt = Some 5"
```

### Type Annotations

```isabelle
(* In terms *)
term "(5::nat)"
term "(\<lambda>x::int. x + 1)"

(* In definitions *)
definition typed_def :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "typed_def x y = x + y"

(* Inline type constraints *)
lemma "(\<forall>x::nat. x \<ge> 0)"
  by simp
```

## Logical Connectives

### Propositional Logic

| Symbol | ASCII | Meaning |
|--------|-------|---------|
| `\<and>` | `/\` | Conjunction (and) |
| `\<or>` | `\/` | Disjunction (or) |
| `\<longrightarrow>` | `-->` | Implication |
| `\<longleftrightarrow>` | `<-->` | Bi-implication (iff) |
| `\<not>` | `~` | Negation |

### Quantifiers

| Symbol | ASCII | Meaning |
|--------|-------|---------|
| `\<forall>` | `ALL` | Universal quantification |
| `\<exists>` | `EX` | Existential quantification |
| `\<nexists>` | | No existence (not exists) |

### Examples

```isabelle
lemma "(\<forall>x. P x) \<longrightarrow> P a"
  by auto

lemma "P a \<longrightarrow> (\<exists>x. P x)"
  by auto

lemma "\<not>(P \<and> \<not>P)"
  by auto
```

## Working with the Simplifier

### Adding Simp Rules

```isabelle
(* Declare as simp rule permanently *)
lemma my_simp [simp]: "double n = n + n"
  unfolding double_def by simp

(* Add temporarily in proof *)
lemma "double 5 = 10"
  by (simp add: double_def)

(* Delete simp rule temporarily *)
lemma "x = x"
  by (simp del: some_rule)
```

### Simplifier Tracing

```isabelle
(* In Isabelle/jEdit, use these to debug *)
using [[simp_trace]]
using [[simp_trace_depth_limit = 5]]
```

## Common Pitfalls

### 1. Matching Theory and Filename
```isabelle
(* File: MyTheory.thy *)
theory MyTheory  (* Must match! *)
  imports Main
begin
```

### 2. Type Inference Issues
```isabelle
(* This might infer wrong type *)
definition ambiguous where "ambiguous x = x + 1"

(* Better: explicit type *)
definition explicit :: "nat \<Rightarrow> nat" where
  "explicit x = x + 1"
```

### 3. Forgetting to Unfold Definitions
```isabelle
definition foo where "foo x = x > 0"

(* This fails: *)
lemma "foo 5" by simp  (* FAILS *)

(* This works: *)
lemma "foo 5" unfolding foo_def by simp
```

## Quick Reference

### Theory Template

```isabelle
theory MyTheory
  imports Main "HOL-Library.Code_Target_Numeral"
begin

section \<open>Definitions\<close>

definition my_function :: "nat \<Rightarrow> nat" where
  "my_function n = n * 2"

section \<open>Lemmas\<close>

lemma my_function_positive:
  "my_function n \<ge> 0"
  unfolding my_function_def by simp

lemma my_function_double:
  "my_function n = n + n"
  unfolding my_function_def by simp

end
```
