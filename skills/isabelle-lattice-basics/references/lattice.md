# Isabelle/HOL Lattice Theory Reference

## Lattice Fundamentals

### What is a Lattice?

A **lattice** is a partially ordered set where every pair of elements has:
- A **meet** (greatest lower bound, infimum, ⊓)
- A **join** (least upper bound, supremum, ⊔)

### Isabelle's Lattice Type Classes

Isabelle provides a hierarchy of order-related type classes:

```
order (partial order)
  └── semilattice_inf (has meet)
  └── semilattice_sup (has join)
       └── lattice (has both)
            └── distrib_lattice (distributive)
            └── bounded_lattice (has top and bot)
                 └── complete_lattice
                      └── complete_distrib_lattice
```

## Partial Orders

### Basic Partial Order

```isabelle
class order = ord +
  assumes less_le_not_le: "x < y \<longleftrightarrow> x \<le> y \<and> \<not> (y \<le> x)"
  assumes order_refl: "x \<le> x"
  assumes order_trans: "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
  assumes order_antisym: "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
```

### Working with Partial Orders

```isabelle
(* Reflexivity *)
lemma "x \<le> (x::'a::order)"
  by simp

(* Transitivity *)
lemma "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> (z::'a::order)"
  by (rule order_trans)

(* Antisymmetry *)
lemma "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = (y::'a::order)"
  by (rule order_antisym)
```

### Defining Custom Orders

```isabelle
(* Order on pairs (lexicographic) *)
instantiation prod :: (order, order) order
begin
  definition less_eq_prod :: "('a \<times> 'b) \<Rightarrow> ('a \<times> 'b) \<Rightarrow> bool" where
    "less_eq_prod p q \<longleftrightarrow> fst p < fst q \<or> (fst p = fst q \<and> snd p \<le> snd q)"
  definition less_prod :: "('a \<times> 'b) \<Rightarrow> ('a \<times> 'b) \<Rightarrow> bool" where
    "less_prod p q \<longleftrightarrow> p \<le> q \<and> \<not> q \<le> p"
  instance by standard (auto simp: less_eq_prod_def less_prod_def)
end
```

## Semilattices

### Semilattice with Infimum (Meet)

```isabelle
class semilattice_inf = order +
  fixes inf :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<sqinter>" 70)
  assumes inf_le1: "x \<sqinter> y \<le> x"
  assumes inf_le2: "x \<sqinter> y \<le> y"
  assumes inf_greatest: "x \<le> y \<Longrightarrow> x \<le> z \<Longrightarrow> x \<le> y \<sqinter> z"
```

### Semilattice with Supremum (Join)

```isabelle
class semilattice_sup = order +
  fixes sup :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<squnion>" 65)
  assumes sup_ge1: "x \<le> x \<squnion> y"
  assumes sup_ge2: "y \<le> x \<squnion> y"
  assumes sup_least: "y \<le> x \<Longrightarrow> z \<le> x \<Longrightarrow> y \<squnion> z \<le> x"
```

### Meet and Join Properties

```isabelle
(* Commutativity *)
lemma "x \<sqinter> y = y \<sqinter> (x::'a::semilattice_inf)"
  by (simp add: inf.commute)

lemma "x \<squnion> y = y \<squnion> (x::'a::semilattice_sup)"
  by (simp add: sup.commute)

(* Associativity *)
lemma "(x \<sqinter> y) \<sqinter> z = x \<sqinter> (y \<sqinter> (z::'a::semilattice_inf))"
  by (simp add: inf.assoc)

(* Idempotence *)
lemma "x \<sqinter> x = (x::'a::semilattice_inf)"
  by simp

lemma "x \<squnion> x = (x::'a::semilattice_sup)"
  by simp
```

## Lattices

### Lattice Type Class

```isabelle
class lattice = semilattice_inf + semilattice_sup
```

### Absorption Laws

```isabelle
(* x ⊓ (x ⊔ y) = x *)
lemma inf_sup_absorb: "x \<sqinter> (x \<squnion> y) = (x::'a::lattice)"
  by (simp add: inf_absorb1)

(* x ⊔ (x ⊓ y) = x *)
lemma sup_inf_absorb: "x \<squnion> (x \<sqinter> y) = (x::'a::lattice)"
  by (simp add: sup_absorb1)
```

### Order from Lattice Operations

```isabelle
(* The partial order can be derived from meet or join *)
lemma "x \<le> y \<longleftrightarrow> x \<sqinter> y = (x::'a::lattice)"
  by (simp add: le_iff_inf)

lemma "x \<le> y \<longleftrightarrow> x \<squnion> y = (y::'a::lattice)"
  by (simp add: le_iff_sup)
```

## Bounded Lattices

### Top and Bottom Elements

```isabelle
class bounded_lattice_bot = lattice +
  fixes bot :: 'a ("\<bottom>")
  assumes bot_least: "\<bottom> \<le> x"

class bounded_lattice_top = lattice +
  fixes top :: 'a ("\<top>")
  assumes top_greatest: "x \<le> \<top>"

class bounded_lattice = bounded_lattice_bot + bounded_lattice_top
```

### Working with Bounds

```isabelle
(* Bottom is identity for join *)
lemma "\<bottom> \<squnion> x = (x::'a::bounded_lattice_bot)"
  by simp

(* Top is identity for meet *)
lemma "\<top> \<sqinter> x = (x::'a::bounded_lattice_top)"
  by simp

(* Annihilation *)
lemma "\<bottom> \<sqinter> x = (\<bottom>::'a::bounded_lattice_bot)"
  by simp

lemma "\<top> \<squnion> x = (\<top>::'a::bounded_lattice_top)"
  by simp
```

## Distributive Lattices

### Definition

```isabelle
class distrib_lattice = lattice +
  assumes sup_inf_distrib1: "x \<squnion> (y \<sqinter> z) = (x \<squnion> y) \<sqinter> (x \<squnion> z)"
```

### Equivalent Formulations

```isabelle
(* In a distributive lattice, these are equivalent: *)
lemma "x \<squnion> (y \<sqinter> z) = (x \<squnion> y) \<sqinter> (x \<squnion> (z::'a::distrib_lattice))"
  by simp

lemma "x \<sqinter> (y \<squnion> z) = (x \<sqinter> y) \<squnion> (x \<sqinter> (z::'a::distrib_lattice))"
  by (simp add: inf_sup_distrib1)
```

### Boolean Algebras (Complemented Distributive Lattice)

```isabelle
class boolean_algebra = distrib_lattice + bounded_lattice +
  fixes uminus :: "'a \<Rightarrow> 'a" ("- _" [81] 80)
  assumes inf_compl_bot: "x \<sqinter> - x = \<bottom>"
  assumes sup_compl_top: "x \<squnion> - x = \<top>"
```

## Complete Lattices

### Definition

```isabelle
class complete_lattice = lattice + bounded_lattice +
  fixes Inf :: "'a set \<Rightarrow> 'a" ("\<Sqinter>")
  fixes Sup :: "'a set \<Rightarrow> 'a" ("\<Squnion>")
  assumes Inf_lower: "x \<in> A \<Longrightarrow> \<Sqinter>A \<le> x"
  assumes Inf_greatest: "(\<And>x. x \<in> A \<Longrightarrow> z \<le> x) \<Longrightarrow> z \<le> \<Sqinter>A"
  assumes Sup_upper: "x \<in> A \<Longrightarrow> x \<le> \<Squnion>A"
  assumes Sup_least: "(\<And>x. x \<in> A \<Longrightarrow> x \<le> z) \<Longrightarrow> \<Squnion>A \<le> z"
```

### Infinite Meet and Join

```isabelle
(* Meet of empty set is top *)
lemma "Inf {} = (\<top>::'a::complete_lattice)"
  by simp

(* Join of empty set is bottom *)
lemma "Sup {} = (\<bottom>::'a::complete_lattice)"
  by simp

(* Binary operations as special cases *)
lemma "Inf {x, y} = x \<sqinter> (y::'a::complete_lattice)"
  by simp

lemma "Sup {x, y} = x \<squnion> (y::'a::complete_lattice)"
  by simp
```

### Fixed Point Theorems

```isabelle
(* Knaster-Tarski: monotone function has least fixed point *)
theorem lfp_unfold:
  assumes "mono f"
  shows "lfp f = f (lfp f)"
  using assms by (simp add: lfp_fixpoint)

(* And greatest fixed point *)
theorem gfp_unfold:
  assumes "mono f"
  shows "gfp f = f (gfp f)"
  using assms by (simp add: gfp_fixpoint)
```

## Common Lattice Instances

### Power Set Lattice

```isabelle
(* Sets form a complete lattice *)
lemma "A \<sqinter> B = A \<inter> (B::'a set)"
  by simp

lemma "A \<squnion> B = A \<union> (B::'a set)"
  by simp

lemma "\<Sqinter>S = \<Inter>(S::('a set) set)"
  by simp

lemma "\<Squnion>S = \<Union>(S::('a set) set)"
  by simp

lemma "\<bottom> = ({}::'a set)"
  by simp

lemma "\<top> = (UNIV::'a set)"
  by simp
```

### Function Lattice (Pointwise)

```isabelle
(* Functions to a lattice form a lattice (pointwise) *)
lemma "(f \<sqinter> g) x = f x \<sqinter> (g x::'b::lattice)"
  by (simp add: inf_fun_def)

lemma "(f \<squnion> g) x = f x \<squnion> (g x::'b::lattice)"
  by (simp add: sup_fun_def)
```

### Product Lattice

```isabelle
(* Pairs with componentwise operations *)
lemma "(a, b) \<sqinter> (c, d) = (a \<sqinter> c, b \<sqinter> (d::'b::lattice))"
  by (simp add: inf_prod_def)

lemma "(a, b) \<squnion> (c, d) = (a \<squnion> c, b \<squnion> (d::'b::lattice))"
  by (simp add: sup_prod_def)
```

### Natural Numbers with Divisibility

```isabelle
(* Divisibility lattice on nat *)
definition dvd_lattice :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
  "dvd_lattice m n \<longleftrightarrow> m dvd n"

(* GCD is meet, LCM is join *)
lemma "gcd m n = Lattice.inf m (n::nat)"
  by simp  (* With appropriate instantiation *)

lemma "lcm m n = Lattice.sup m (n::nat)"
  by simp
```

## Lattice Homomorphisms

### Definition

```isabelle
definition lattice_hom :: "('a::lattice \<Rightarrow> 'b::lattice) \<Rightarrow> bool" where
  "lattice_hom f \<longleftrightarrow>
     (\<forall>x y. f (x \<sqinter> y) = f x \<sqinter> f y) \<and>
     (\<forall>x y. f (x \<squnion> y) = f x \<squnion> f y)"
```

### Properties

```isabelle
lemma lattice_hom_mono:
  assumes "lattice_hom f"
  shows "x \<le> y \<Longrightarrow> f x \<le> f y"
proof -
  assume "x \<le> y"
  then have "x \<sqinter> y = x" by (simp add: le_iff_inf)
  with assms have "f x \<sqinter> f y = f x"
    by (simp add: lattice_hom_def)
  then show "f x \<le> f y" by (simp add: le_iff_inf)
qed
```

## Integer Lattices (Z^n)

### Lattice Points

For cryptographic applications, we work with integer lattices:

```isabelle
(* Z^n represented as int lists of fixed length *)
type_synonym int_vec = "int list"

definition is_lattice_vec :: "nat \<Rightarrow> int_vec \<Rightarrow> bool" where
  "is_lattice_vec n v = (length v = n)"

(* Lattice spanned by basis vectors *)
definition lattice_span :: "int_vec list \<Rightarrow> int_vec set" where
  "lattice_span basis = {v. \<exists>coeffs. length coeffs = length basis \<and>
                              v = fold (\<lambda>(c,b) acc. map2 (+) acc (map ((*) c) b))
                                       (zip coeffs basis) (replicate (length (hd basis)) 0)}"
```

### Basis Operations

```isabelle
(* Vector addition in Z^n *)
definition vec_add :: "int_vec \<Rightarrow> int_vec \<Rightarrow> int_vec" where
  "vec_add v w = map2 (+) v w"

(* Scalar multiplication *)
definition vec_scale :: "int \<Rightarrow> int_vec \<Rightarrow> int_vec" where
  "vec_scale c v = map ((*) c) v"

(* Zero vector *)
definition vec_zero :: "nat \<Rightarrow> int_vec" where
  "vec_zero n = replicate n 0"
```

## Defining Custom Lattices

### Complete Example

```isabelle
theory My_Lattice
  imports Main
begin

(* Three-element lattice: Bot < Mid < Top *)
datatype three = Bot | Mid | Top

instantiation three :: order
begin
  definition less_eq_three :: "three \<Rightarrow> three \<Rightarrow> bool" where
    "x \<le> y = (x = Bot \<or> y = Top \<or> x = y)"
  definition less_three :: "three \<Rightarrow> three \<Rightarrow> bool" where
    "x < y = (x \<le> y \<and> x \<noteq> y)"
  instance by standard (auto simp: less_eq_three_def less_three_def)
end

instantiation three :: lattice
begin
  definition inf_three :: "three \<Rightarrow> three \<Rightarrow> three" where
    "x \<sqinter> y = (case (x, y) of
                 (Bot, _) \<Rightarrow> Bot | (_, Bot) \<Rightarrow> Bot
               | (Mid, _) \<Rightarrow> y | (_, Mid) \<Rightarrow> x
               | (Top, Top) \<Rightarrow> Top)"
  definition sup_three :: "three \<Rightarrow> three \<Rightarrow> three" where
    "x \<squnion> y = (case (x, y) of
                 (Top, _) \<Rightarrow> Top | (_, Top) \<Rightarrow> Top
               | (Mid, _) \<Rightarrow> y | (_, Mid) \<Rightarrow> x
               | (Bot, Bot) \<Rightarrow> Bot)"
  instance by standard (auto simp: inf_three_def sup_three_def less_eq_three_def
                        split: three.splits)
end

instantiation three :: bounded_lattice
begin
  definition bot_three :: three where "\<bottom> = Bot"
  definition top_three :: three where "\<top> = Top"
  instance by standard (auto simp: bot_three_def top_three_def less_eq_three_def)
end

end
```

## Lattice Theory in HOL-Algebra

### Abstract Lattice Locale

```isabelle
imports "HOL-Algebra.Lattice"

locale lattice =
  fixes L (structure)
  assumes sup_closed: "\<lbrakk>x \<in> carrier L; y \<in> carrier L\<rbrakk> \<Longrightarrow> x \<squnion>\<^bsub>L\<^esub> y \<in> carrier L"
  assumes inf_closed: "\<lbrakk>x \<in> carrier L; y \<in> carrier L\<rbrakk> \<Longrightarrow> x \<sqinter>\<^bsub>L\<^esub> y \<in> carrier L"
  (* ... additional axioms *)
```

### Working with Locales

```isabelle
context lattice
begin

lemma meet_comm: "x \<in> carrier L \<Longrightarrow> y \<in> carrier L \<Longrightarrow> x \<sqinter>\<^bsub>L\<^esub> y = y \<sqinter>\<^bsub>L\<^esub> x"
  by (rule inf_commute)

end
```

## Key Lemmas for Cryptographic Applications

```isabelle
(* Sublattice property *)
lemma sublattice_closed:
  assumes "S \<subseteq> carrier L"
    and "\<forall>x \<in> S. \<forall>y \<in> S. x \<sqinter>\<^bsub>L\<^esub> y \<in> S"
    and "\<forall>x \<in> S. \<forall>y \<in> S. x \<squnion>\<^bsub>L\<^esub> y \<in> S"
  shows "sublattice S L"
  using assms by (auto simp: sublattice_def)

(* Lattice isomorphism preserves structure *)
lemma lattice_iso_preserves:
  assumes "lattice_iso f L M"
  shows "f (x \<sqinter>\<^bsub>L\<^esub> y) = f x \<sqinter>\<^bsub>M\<^esub> f y"
    and "f (x \<squnion>\<^bsub>L\<^esub> y) = f x \<squnion>\<^bsub>M\<^esub> f y"
  using assms by (auto simp: lattice_iso_def)
```
