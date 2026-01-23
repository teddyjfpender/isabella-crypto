# Isabelle/HOL Proof Techniques Reference

## Proof Methods Overview

### Method Hierarchy (from simple to complex)

| Method | Best For | Power | Speed |
|--------|----------|-------|-------|
| `simp` | Equational reasoning, rewriting | Low | Fast |
| `auto` | First-order with simplification | Medium | Medium |
| `fastforce` | Classical + simplifier | Medium-High | Medium |
| `force` | Like fastforce, more complete | High | Slow |
| `blast` | Pure classical logic | High | Variable |
| `metis` | First-order with equality | High | Variable |
| `meson` | Pure first-order | Medium | Fast |
| `smt` | Decidable theories | High | Variable |

## The Simplifier (simp)

### Basic Usage

```isabelle
lemma "rev (rev xs) = xs"
  by simp

lemma "length (xs @ ys) = length xs + length ys"
  by simp
```

### Adding and Removing Simp Rules

```isabelle
(* Add rules for this proof *)
lemma example1: "my_fun x = x + 1"
  by (simp add: my_fun_def other_lemma)

(* Remove default rules *)
lemma example2: "x + 0 = x"
  by (simp del: add_0_right)

(* Both add and delete *)
lemma example3: "complex_term"
  by (simp add: needed_def del: problematic_rule)
```

### Only Use Specific Rules

```isabelle
(* Use only the listed rules *)
lemma "xs @ [] = xs"
  by (simp only: append_Nil2)

(* Empty simplifier, then add *)
lemma "rev [a] = [a]"
  by (simp only: rev.simps append.simps)
```

### Simp Modifiers

```isabelle
(* split - enable case splitting *)
lemma "P (if b then x else y)"
  by (simp split: if_splits)

(* cong - congruence rules *)
lemma "map f xs = map f xs"
  by (simp cong: map_cong)

(* Arithmetic simplification *)
lemma "(n::nat) + m = m + n"
  by (simp add: add.commute)
```

### Simplifier with Assumptions

```isabelle
lemma
  assumes "x = 5"
  shows "x + 1 = 6"
  using assms by simp

(* Or inline *)
lemma "x = 5 \<Longrightarrow> x + 1 = 6"
  by simp
```

## Auto Method

### Basic Usage

```isabelle
(* auto combines simp with classical reasoning *)
lemma "A \<and> B \<longrightarrow> B \<and> A"
  by auto

lemma "\<exists>x. P x \<longrightarrow> (\<forall>x. P x)"
  by auto

lemma "x \<in> A \<inter> B \<longleftrightarrow> x \<in> A \<and> x \<in> B"
  by auto
```

### Auto Modifiers

```isabelle
(* intro - introduction rules *)
lemma "\<exists>x. x = (0::nat)"
  by (auto intro: exI)

(* dest - destruction rules *)
lemma "P \<and> Q \<Longrightarrow> P"
  by (auto dest: conjunct1)

(* elim - elimination rules *)
lemma "A \<or> B \<Longrightarrow> C \<or> B \<or> A"
  by (auto elim: disjE)

(* Combined *)
lemma complex_goal
  by (auto simp: def1 def2 intro: rule1 dest: rule2 split: option.splits)
```

### Controlling Auto's Depth

```isabelle
(* Limit search depth *)
lemma "complex_goal"
  apply (auto 4 3)  (* intro depth 4, elim depth 3 *)
```

## Classical Reasoners

### blast

Pure tableau prover, no simplification:

```isabelle
(* Good for propositional/first-order logic *)
lemma "(\<forall>x. P x \<longrightarrow> Q x) \<longrightarrow> (\<forall>x. P x) \<longrightarrow> (\<forall>x. Q x)"
  by blast

lemma "\<not>(\<exists>x. \<forall>y. P x y \<longleftrightarrow> \<not>P y y)"
  by blast

(* With extra rules *)
lemma "example"
  by (blast intro: rule1 dest: rule2)
```

### force and fastforce

Combine classical reasoning with simplifier:

```isabelle
(* fastforce - faster but less complete *)
lemma "x \<in> {1,2,3} \<Longrightarrow> x > 0"
  by fastforce

(* force - slower but more thorough *)
lemma "complex_set_goal"
  by force

(* With modifiers *)
lemma "goal"
  by (fastforce simp: defs intro: rules)
```

## Induction

### Structural Induction

```isabelle
(* Over lists *)
lemma length_append: "length (xs @ ys) = length xs + length ys"
  by (induction xs) auto

(* Over natural numbers *)
lemma "sum_upto n = n * (n + 1) div 2"
  by (induction n) auto

(* Over custom datatypes *)
lemma "size_tree t \<ge> 0"
  by (induction t) auto
```

### Specifying Induction Variable

```isabelle
(* When there are multiple possible variables *)
lemma "P xs ys"
  by (induction xs) auto  (* Induct on xs *)

lemma "P xs ys"
  by (induction ys) auto  (* Induct on ys *)
```

### Induction with Arbitrary Variables

```isabelle
(* Generalize over certain variables *)
lemma rev_append: "rev (xs @ ys) = rev ys @ rev xs"
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  then show ?case by simp
qed

(* With arbitrary *)
lemma "length (rev xs) = length xs"
  by (induction xs arbitrary: ) auto
```

### Simultaneous Induction

```isabelle
lemma even_odd:
  "even' n = (n mod 2 = 0)"
  "odd' n = (n mod 2 = 1)"
  by (induction n) auto
```

### Computation Induction

```isabelle
(* Induction following function definition *)
lemma "fib n + fib (Suc n) = fib (Suc (Suc n))"
  by (induction n rule: fib.induct) auto
```

### Strong Induction

```isabelle
lemma strong_induction:
  "(\<And>n. (\<forall>m < n. P m) \<Longrightarrow> P n) \<Longrightarrow> P n"
  by (rule nat_less_induct)

(* Using measure induction *)
lemma "P (xs::'a list)"
  by (induction xs rule: measure_induct_rule[of length]) auto
```

## Case Analysis

### cases Tactic

```isabelle
(* Boolean cases *)
lemma "(if b then P else Q) \<longrightarrow> P \<or> Q"
  by (cases b) auto

(* Datatype cases *)
lemma "xs \<noteq> [] \<longrightarrow> hd xs # tl xs = xs"
  by (cases xs) auto

(* Natural number cases *)
lemma "n = 0 \<or> n > 0"
  by (cases n) auto
```

### Case Analysis in Isar

```isabelle
lemma disjunction_commute: "A \<or> B \<Longrightarrow> B \<or> A"
proof (cases A)
  case True
  then show ?thesis by simp
next
  case False
  assume "A \<or> B"
  with False have "B" by simp
  then show ?thesis by simp
qed
```

### Option and Sum Types

```isabelle
lemma "x = None \<or> (\<exists>v. x = Some v)"
  by (cases x) auto

lemma "(\<forall>l. x \<noteq> Left l) \<longrightarrow> (\<exists>r. x = Right r)"
  by (cases x) auto
```

## Isar Structured Proofs

### Basic Structure

```isabelle
lemma my_lemma:
  assumes h1: "P"
    and h2: "Q"
  shows "R"
proof -
  from h1 have step1: "S" by auto
  from step1 h2 have step2: "T" by auto
  from step2 show "R" by auto
qed
```

### Proof Keywords

| Keyword | Meaning |
|---------|---------|
| `proof -` | Start proof with no initial method |
| `proof (method)` | Start proof applying method first |
| `have` | Prove intermediate fact |
| `hence` | Same as `then have` |
| `show` | Prove the goal |
| `thus` | Same as `then show` |
| `from` | Use facts |
| `with` | Use facts with `this` |
| `using` | Add facts to proof |
| `then` | Chain previous fact |
| `this` | The previous fact |
| `?thesis` | The current goal |

### Proof Blocks

```isabelle
lemma "A \<and> B \<longrightarrow> B \<and> A"
proof
  assume ab: "A \<and> B"
  show "B \<and> A"
  proof
    from ab show "B" by simp
    from ab show "A" by simp
  qed
qed
```

### Obtain and Existence

```isabelle
lemma "\<exists>x. P x \<Longrightarrow> Q"
proof -
  assume "\<exists>x. P x"
  then obtain x where px: "P x" by auto
  from px show "Q" sorry
qed
```

### Let and Define

```isabelle
lemma "P"
proof -
  let ?x = "some_term"
  define y where "y = other_term"
  have "?x = y" unfolding y_def sorry
  then show "P" sorry
qed
```

## Specialized Methods

### metis - Resolution with Equality

```isabelle
lemma "(\<forall>x. P x \<longrightarrow> Q x) \<Longrightarrow> P a \<Longrightarrow> Q a"
  by (metis)

(* With specific facts *)
lemma "conclusion"
  by (metis fact1 fact2 fact3)
```

### smt - SMT Solver Integration

```isabelle
(* Requires SMT solver setup *)
lemma "x + y = y + x"
  by (smt)

lemma "(n::int) > 0 \<Longrightarrow> n * n > 0"
  by (smt)
```

### arith - Linear Arithmetic

```isabelle
lemma "((x::nat) + y = y + x)"
  by arith

lemma "(a::int) < b \<Longrightarrow> b < c \<Longrightarrow> a < c"
  by arith
```

### presburger - Presburger Arithmetic

```isabelle
lemma "\<exists>x::int. 2 * x = y \<or> 2 * x + 1 = y"
  by presburger
```

## Debugging Proofs

### Apply Style (for Debugging)

```isabelle
lemma "complex_goal"
  apply (induction xs)
   apply simp            (* Base case *)
  apply (simp add: IH)   (* Inductive case *)
  done
```

### Showing Subgoals

```isabelle
lemma "goal"
  apply auto
  (* Check remaining subgoals in output *)
```

### Simplifier Tracing

```isabelle
(* See what the simplifier is doing *)
using [[simp_trace]]
using [[simp_trace_depth_limit = 10]]

lemma "complex"
  by simp
```

### Finding Theorems

```isabelle
(* Search for theorems *)
find_theorems "_ @ _ = _"
find_theorems name: "append"
find_theorems "length" "map"
```

### Try Methods

```isabelle
(* Try various methods *)
try
try0

(* Sledgehammer - external provers *)
sledgehammer
```

## Rule Application

### rule Tactic

```isabelle
(* Apply a specific rule *)
lemma "A \<and> B"
  apply (rule conjI)  (* Creates two subgoals: A and B *)
```

### erule - Elimination Rule

```isabelle
lemma "A \<and> B \<Longrightarrow> B"
  apply (erule conjE)  (* Eliminates conjunction *)
  apply assumption
  done
```

### drule - Destruction Rule

```isabelle
lemma "A \<and> B \<Longrightarrow> A"
  apply (drule conjunct1)
  apply assumption
  done
```

### frule - Forward Rule (Non-destructive)

```isabelle
lemma "P x \<Longrightarrow> P x \<and> True"
  apply (frule someRule)  (* Keeps original assumption *)
```

## Proof Patterns

### Split on Definition

```isabelle
definition pred :: "nat \<Rightarrow> bool" where
  "pred n = (n > 0)"

lemma "pred (Suc n)"
  unfolding pred_def by simp
```

### Introduce Then Eliminate

```isabelle
lemma "A \<longrightarrow> A"
proof
  assume "A"
  then show "A" .
qed
```

### Chain of Equations

```isabelle
lemma "a + b + c = c + b + a"
proof -
  have "a + b + c = (a + b) + c" by simp
  also have "... = c + (a + b)" by simp
  also have "... = c + (b + a)" by simp
  also have "... = c + b + a" by simp
  finally show ?thesis .
qed
```

### Contradiction

```isabelle
lemma "P \<Longrightarrow> \<not>\<not>P"
proof
  assume "P" "\<not>P"
  then show False by simp
qed
```

## Common Patterns

### Proving Equality by Antisymmetry

```isabelle
lemma "A = B"
proof (rule equalityI)
  show "A \<subseteq> B" by auto
next
  show "B \<subseteq> A" by auto
qed
```

### Proving Existence

```isabelle
lemma "\<exists>x. P x"
proof
  show "P witness" by auto
qed

(* Or directly *)
lemma "\<exists>x. x = (0::nat)"
  by (intro exI) simp
```

### Universal to Specific

```isabelle
lemma "P a"
  using universal_fact[of a]  (* Instantiate \<forall>x. P x *)
  by simp
```

## Complete Example

```isabelle
theory Proofs_Example
  imports Main
begin

fun sum_list :: "nat list \<Rightarrow> nat" where
  "sum_list [] = 0"
| "sum_list (x # xs) = x + sum_list xs"

(* Simple proof *)
lemma sum_list_append:
  "sum_list (xs @ ys) = sum_list xs + sum_list ys"
  by (induction xs) auto

(* Isar proof *)
lemma sum_list_rev:
  "sum_list (rev xs) = sum_list xs"
proof (induction xs)
  case Nil
  show ?case by simp
next
  case (Cons x xs)
  have "sum_list (rev (x # xs)) = sum_list (rev xs @ [x])"
    by simp
  also have "... = sum_list (rev xs) + sum_list [x]"
    by (simp add: sum_list_append)
  also have "... = sum_list xs + x"
    using Cons.IH by simp
  also have "... = sum_list (x # xs)"
    by simp
  finally show ?case .
qed

end
```
