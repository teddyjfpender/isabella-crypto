# Isabelle/HOL Algebra Reference

## Overview

Isabelle provides algebraic structures through:
1. **Type classes** - For structures on types (e.g., `ring`, `field`)
2. **HOL-Algebra** - Locales with explicit carriers (more flexible)

## Groups

### Group Type Class

```isabelle
class group_add = minus + uminus + zero +
  assumes add_assoc: "(a + b) + c = a + (b + c)"
  assumes add_0: "0 + a = a"
  assumes left_minus: "- a + a = 0"
```

### Group in HOL-Algebra

```isabelle
imports "HOL-Algebra.Group"

record 'a monoid =
  carrier :: "'a set"
  mult :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<otimes>\<index>" 70)
  one :: 'a ("\<one>\<index>")

record 'a group = "'a monoid" +
  inv :: "'a \<Rightarrow> 'a"

locale group =
  fixes G (structure)
  assumes m_closed: "\<lbrakk>x \<in> carrier G; y \<in> carrier G\<rbrakk> \<Longrightarrow> x \<otimes> y \<in> carrier G"
  assumes m_assoc: "\<lbrakk>x \<in> carrier G; y \<in> carrier G; z \<in> carrier G\<rbrakk>
                    \<Longrightarrow> (x \<otimes> y) \<otimes> z = x \<otimes> (y \<otimes> z)"
  assumes one_closed: "\<one> \<in> carrier G"
  assumes l_one: "x \<in> carrier G \<Longrightarrow> \<one> \<otimes> x = x"
  assumes inv_closed: "x \<in> carrier G \<Longrightarrow> inv x \<in> carrier G"
  assumes l_inv: "x \<in> carrier G \<Longrightarrow> inv x \<otimes> x = \<one>"
```

### Working with Groups

```isabelle
context group
begin

lemma r_one: "x \<in> carrier G \<Longrightarrow> x \<otimes> \<one> = x"
  by (metis l_inv l_one m_assoc m_closed inv_closed one_closed)

lemma r_inv: "x \<in> carrier G \<Longrightarrow> x \<otimes> inv x = \<one>"
  by (metis l_inv l_one m_assoc m_closed inv_closed one_closed r_one)

lemma inv_inv: "x \<in> carrier G \<Longrightarrow> inv (inv x) = x"
  by (metis inv_closed l_inv l_one m_assoc r_inv)

end
```

### Cyclic Groups

```isabelle
definition cyclic_group :: "'a \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> 'a group" where
  "cyclic_group gen op n = \<lparr>
     carrier = {op gen k | k. k < n},
     mult = \<lambda>x y. op (op x y) (n - 1),
     one = gen,
     inv = \<lambda>x. op gen (n - index x)
   \<rparr>"

(* Z_n as additive group *)
definition Z_n :: "nat \<Rightarrow> nat group" where
  "Z_n n = \<lparr>
     carrier = {0..<n},
     mult = \<lambda>x y. (x + y) mod n,
     one = 0,
     inv = \<lambda>x. (n - x) mod n
   \<rparr>"
```

### Group Homomorphisms

```isabelle
definition group_hom :: "('a, 'b) group_scheme \<Rightarrow> ('c, 'd) group_scheme \<Rightarrow>
                        ('a \<Rightarrow> 'c) \<Rightarrow> bool" where
  "group_hom G H f \<longleftrightarrow>
     f ` carrier G \<subseteq> carrier H \<and>
     (\<forall>x \<in> carrier G. \<forall>y \<in> carrier G. f (x \<otimes>\<^bsub>G\<^esub> y) = f x \<otimes>\<^bsub>H\<^esub> f y)"

lemma group_hom_one:
  assumes "group G" "group H" "group_hom G H f"
  shows "f \<one>\<^bsub>G\<^esub> = \<one>\<^bsub>H\<^esub>"
  using assms by (auto simp: group_hom_def)
```

## Rings

### Ring Type Class

```isabelle
class ring = comm_monoid_add + monoid_mult +
  assumes distrib_right: "(a + b) * c = a * c + b * c"
  assumes distrib_left: "a * (b + c) = a * b + a * c"
```

### Ring in HOL-Algebra

```isabelle
imports "HOL-Algebra.Ring"

record 'a ring = "'a monoid" +
  zero :: 'a ("\<zero>\<index>")
  add :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<oplus>\<index>" 65)
  a_inv :: "'a \<Rightarrow> 'a" ("\<ominus>\<index> _" [81] 80)

locale ring =
  fixes R (structure)
  assumes ring_axioms: (* ... axioms ... *)
```

### Commutative Rings

```isabelle
locale cring = ring +
  assumes m_comm: "\<lbrakk>x \<in> carrier R; y \<in> carrier R\<rbrakk> \<Longrightarrow> x \<otimes> y = y \<otimes> x"
```

### Integer Ring

```isabelle
(* Integers form a ring *)
interpretation int_ring: cring "\<lparr>
  carrier = UNIV,
  mult = (*),
  one = 1,
  zero = 0,
  add = (+),
  a_inv = uminus
\<rparr>"
  by standard auto
```

### Ring Homomorphisms

```isabelle
definition ring_hom :: "('a, 'b) ring_scheme \<Rightarrow> ('c, 'd) ring_scheme \<Rightarrow>
                       ('a \<Rightarrow> 'c) \<Rightarrow> bool" where
  "ring_hom R S f \<longleftrightarrow>
     f ` carrier R \<subseteq> carrier S \<and>
     f \<one>\<^bsub>R\<^esub> = \<one>\<^bsub>S\<^esub> \<and>
     (\<forall>x \<in> carrier R. \<forall>y \<in> carrier R. f (x \<oplus>\<^bsub>R\<^esub> y) = f x \<oplus>\<^bsub>S\<^esub> f y) \<and>
     (\<forall>x \<in> carrier R. \<forall>y \<in> carrier R. f (x \<otimes>\<^bsub>R\<^esub> y) = f x \<otimes>\<^bsub>S\<^esub> f y)"
```

## Fields

### Field Type Class

```isabelle
class field = comm_ring_1 + inverse +
  assumes field_inverse: "a \<noteq> 0 \<Longrightarrow> inverse a * a = 1"
  assumes field_divide: "divide a b = a * inverse b"
```

### Field in HOL-Algebra

```isabelle
locale field = cring +
  assumes field_Units: "carrier R - {\<zero>} \<subseteq> Units R"

(* Units = invertible elements *)
definition Units :: "('a, 'b) ring_scheme \<Rightarrow> 'a set" where
  "Units R = {a \<in> carrier R. \<exists>b \<in> carrier R. a \<otimes>\<^bsub>R\<^esub> b = \<one>\<^bsub>R\<^esub>}"
```

### Finite Fields

```isabelle
(* GF(p) - prime field *)
definition GF :: "nat \<Rightarrow> nat ring" where
  "GF p = \<lparr>
     carrier = {0..<p},
     mult = \<lambda>x y. (x * y) mod p,
     one = 1,
     zero = 0,
     add = \<lambda>x y. (x + y) mod p,
     a_inv = \<lambda>x. (p - x) mod p
   \<rparr>"

lemma GF_field:
  assumes "prime p"
  shows "field (GF p)"
  using assms by (auto simp: GF_def field_def cring_def)
```

### Field Extensions

```isabelle
(* GF(p^n) as quotient of polynomial ring *)
definition GF_ext :: "nat \<Rightarrow> nat \<Rightarrow> int list \<Rightarrow> int list ring" where
  "GF_ext p n irred_poly = poly_quotient_ring (GF p) irred_poly"
```

## Polynomial Rings

### Polynomial Representation

```isabelle
(* Polynomials as coefficient lists (lowest degree first) *)
type_synonym 'a poly = "'a list"

(* Degree *)
definition degree :: "'a::zero poly \<Rightarrow> nat" where
  "degree p = (if p = [] \<or> (\<forall>c \<in> set p. c = 0) then 0 else length p - 1)"

(* Leading coefficient *)
definition lead_coeff :: "'a::zero poly \<Rightarrow> 'a" where
  "lead_coeff p = (if p = [] then 0 else last p)"
```

### Polynomial Operations

```isabelle
(* Addition *)
fun poly_add :: "'a::ring_1 poly \<Rightarrow> 'a poly \<Rightarrow> 'a poly" where
  "poly_add [] q = q"
| "poly_add p [] = p"
| "poly_add (a # as) (b # bs) = (a + b) # poly_add as bs"

(* Multiplication *)
fun poly_mult :: "'a::ring_1 poly \<Rightarrow> 'a poly \<Rightarrow> 'a poly" where
  "poly_mult [] _ = []"
| "poly_mult (a # as) q = poly_add (map ((*) a) q) (0 # poly_mult as q)"

(* Scalar multiplication *)
definition poly_scale :: "'a::ring_1 \<Rightarrow> 'a poly \<Rightarrow> 'a poly" where
  "poly_scale c p = map ((*) c) p"
```

### Polynomial Ring in HOL-Algebra

```isabelle
imports "HOL-Algebra.Polynomial"

(* Univariate polynomial ring over R *)
abbreviation UP :: "('a, 'b) ring_scheme \<Rightarrow> 'a list ring" where
  "UP R \<equiv> univ_poly R"

(* Key operations *)
term "poly_add R"   (* Addition in UP R *)
term "poly_mult R"  (* Multiplication in UP R *)
term "X\<^bsub>R\<^esub>"        (* Indeterminate X *)

(* UP R is a ring when R is a ring *)
lemma UP_ring: "ring R \<Longrightarrow> ring (UP R)"
  by (rule univ_poly_is_ring)
```

### Polynomial Division

```isabelle
(* Division with remainder *)
function poly_divmod :: "'a::field poly \<Rightarrow> 'a poly \<Rightarrow> 'a poly \<times> 'a poly" where
  "poly_divmod p q =
     (if q = [] \<or> degree p < degree q
      then ([], p)
      else let c = lead_coeff p / lead_coeff q;
               d = degree p - degree q;
               term = replicate d 0 @ [c];
               p' = poly_sub p (poly_mult term q)
           in let (quot, rem) = poly_divmod p' q
              in (poly_add quot term, rem))"
  by pat_completeness auto
```

## Quotient Rings

### Ideals

```isabelle
definition ideal :: "('a, 'b) ring_scheme \<Rightarrow> 'a set \<Rightarrow> bool" where
  "ideal R I \<longleftrightarrow>
     I \<subseteq> carrier R \<and>
     \<zero>\<^bsub>R\<^esub> \<in> I \<and>
     (\<forall>a \<in> I. \<forall>b \<in> I. a \<oplus>\<^bsub>R\<^esub> b \<in> I) \<and>
     (\<forall>a \<in> I. \<ominus>\<^bsub>R\<^esub> a \<in> I) \<and>
     (\<forall>a \<in> I. \<forall>r \<in> carrier R. r \<otimes>\<^bsub>R\<^esub> a \<in> I)"

(* Principal ideal generated by element *)
definition principal_ideal :: "('a, 'b) ring_scheme \<Rightarrow> 'a \<Rightarrow> 'a set" where
  "principal_ideal R a = {r \<otimes>\<^bsub>R\<^esub> a | r. r \<in> carrier R}"
```

### Quotient Ring Construction

```isabelle
(* Equivalence classes *)
definition quot_equiv :: "('a, 'b) ring_scheme \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "quot_equiv R I a b \<longleftrightarrow> (\<exists>i \<in> I. a \<oplus>\<^bsub>R\<^esub> (\<ominus>\<^bsub>R\<^esub> b) = i)"

(* Quotient ring R/I *)
definition quotient_ring :: "('a, 'b) ring_scheme \<Rightarrow> 'a set \<Rightarrow> 'a set ring" where
  "quotient_ring R I = \<lparr>
     carrier = (carrier R) // (quot_equiv R I),
     mult = \<lambda>A B. {a \<otimes>\<^bsub>R\<^esub> b | a b. a \<in> A \<and> b \<in> B} // (quot_equiv R I),
     one = quot_equiv R I `` {\<one>\<^bsub>R\<^esub>},
     zero = I,
     add = \<lambda>A B. {a \<oplus>\<^bsub>R\<^esub> b | a b. a \<in> A \<and> b \<in> B} // (quot_equiv R I),
     a_inv = \<lambda>A. {\<ominus>\<^bsub>R\<^esub> a | a. a \<in> A}
   \<rparr>"

lemma quotient_ring_is_ring:
  assumes "ring R" "ideal R I"
  shows "ring (quotient_ring R I)"
  using assms sorry
```

### Polynomial Quotient Ring

```isabelle
(* Z_q[X] / (f(X)) - crucial for Ring-LWE *)
definition poly_quotient_ring ::
  "('a, 'b) ring_scheme \<Rightarrow> 'a poly \<Rightarrow> 'a poly ring" where
  "poly_quotient_ring R f = quotient_ring (UP R) (principal_ideal (UP R) f)"

(* Simplified: represent elements as polynomials of degree < deg(f) *)
definition poly_mod :: "'a::field poly \<Rightarrow> 'a poly \<Rightarrow> 'a poly" where
  "poly_mod p f = snd (poly_divmod p f)"

definition Rq :: "int \<Rightarrow> int poly \<Rightarrow> int poly ring" where
  "Rq q f = \<lparr>
     carrier = {p. degree p < degree f \<and> (\<forall>c \<in> set p. 0 \<le> c \<and> c < q)},
     mult = \<lambda>p1 p2. poly_mod (poly_mult p1 p2) f,
     one = [1],
     zero = [],
     add = \<lambda>p1 p2. map (\<lambda>c. c mod q) (poly_add p1 p2),
     a_inv = \<lambda>p. map (\<lambda>c. (-c) mod q) p
   \<rparr>"
```

### Cyclotomic Polynomial Rings

```isabelle
(* X^n + 1 for power-of-2 n *)
definition cyclotomic :: "nat \<Rightarrow> int poly" where
  "cyclotomic n = replicate n 0 @ [1, 1]"

(* Ring used in Ring-LWE: Z_q[X]/(X^n + 1) *)
definition Rq_cyclotomic :: "int \<Rightarrow> nat \<Rightarrow> int poly ring" where
  "Rq_cyclotomic q n = Rq q (cyclotomic n)"

(* Multiplication in this ring (negacyclic convolution) *)
definition negacyclic_mult :: "int poly \<Rightarrow> int poly \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> int poly" where
  "negacyclic_mult p1 p2 n q =
     (let prod = poly_mult p1 p2;
          high = drop n prod;
          low = take n prod @ replicate (n - length (take n prod)) 0
      in map (\<lambda>c. c mod q) (poly_sub low (high @ replicate (n - length high) 0)))"
```

## Module Theory

### R-Modules

```isabelle
locale module =
  fixes R :: "('a, 'r) ring_scheme" (structure)
    and M :: "('b, 'm) module_scheme" (structure)
  assumes scalar_mult_closed:
    "\<lbrakk>r \<in> carrier R; m \<in> carrier M\<rbrakk> \<Longrightarrow> r \<cdot>\<^bsub>M\<^esub> m \<in> carrier M"
  assumes smult_assoc:
    "\<lbrakk>r \<in> carrier R; s \<in> carrier R; m \<in> carrier M\<rbrakk>
     \<Longrightarrow> (r \<otimes>\<^bsub>R\<^esub> s) \<cdot>\<^bsub>M\<^esub> m = r \<cdot>\<^bsub>M\<^esub> (s \<cdot>\<^bsub>M\<^esub> m)"
  (* ... more axioms ... *)
```

### Free Modules (Vector Spaces over Rings)

```isabelle
(* R^n as free module *)
definition free_module :: "('a, 'b) ring_scheme \<Rightarrow> nat \<Rightarrow> 'a list module" where
  "free_module R n = \<lparr>
     carrier = {v. length v = n \<and> set v \<subseteq> carrier R},
     add = map2 (\<oplus>\<^bsub>R\<^esub>),
     zero = replicate n \<zero>\<^bsub>R\<^esub>,
     smult = \<lambda>r v. map (\<otimes>\<^bsub>R\<^esub> r) v
   \<rparr>"
```

## Chinese Remainder Theorem

### CRT for Rings

```isabelle
(* Ring isomorphism for coprime ideals *)
theorem chinese_remainder_rings:
  assumes "ring R" "ideal R I" "ideal R J"
    and "I \<oplus>\<^bsub>R\<^esub> J = carrier R"  (* Coprime ideals *)
  shows "R / (I \<inter> J) \<cong> (R / I) \<times> (R / J)"
  sorry
```

### CRT for Polynomials

```isabelle
(* Useful for NTT-based multiplication *)
theorem crt_poly:
  assumes "coprime f g"
  shows "R[X]/(f \<cdot> g) \<cong> R[X]/f \<times> R[X]/g"
  sorry

(* For cyclotomic: X^n + 1 splits in Z_q when q = 1 (mod 2n) *)
lemma cyclotomic_splits:
  assumes "prime q" "q mod (2 * n) = 1"
  shows "\<exists>roots. length roots = n \<and>
         cyclotomic n = prod_list (map (\<lambda>r. [-r, 1]) roots) in Z_q"
  sorry
```

## Complete Example

```isabelle
theory Algebra_Example
  imports Main "HOL-Algebra.Ring" "HOL-Algebra.Polynomial"
begin

section \<open>Polynomial Ring Z_q[X]/(X^n + 1)\<close>

type_synonym zq_poly = "int list"

definition zq_poly_carrier :: "int \<Rightarrow> nat \<Rightarrow> zq_poly set" where
  "zq_poly_carrier q n = {p. length p \<le> n \<and> (\<forall>c \<in> set p. 0 \<le> c \<and> c < q)}"

fun normalize :: "int \<Rightarrow> zq_poly \<Rightarrow> zq_poly" where
  "normalize q p = map (\<lambda>c. c mod q) p"

fun poly_add_zq :: "zq_poly \<Rightarrow> zq_poly \<Rightarrow> int \<Rightarrow> zq_poly" where
  "poly_add_zq [] q _ = q"
| "poly_add_zq p [] _ = p"
| "poly_add_zq (a#as) (b#bs) q = ((a + b) mod q) # poly_add_zq as bs q"

(* Negacyclic reduction: X^n = -1 *)
fun reduce_cyclotomic :: "zq_poly \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> zq_poly" where
  "reduce_cyclotomic p n q =
     (if length p \<le> n then p
      else let low = take n p;
               high = drop n p;
               sub = map2 (\<lambda>l h. (l - h) mod q) low (high @ replicate (n - length high) 0)
           in reduce_cyclotomic sub n q)"

section \<open>Ring Properties\<close>

lemma poly_add_comm:
  "poly_add_zq p1 p2 q = poly_add_zq p2 p1 q"
  by (induction p1 p2 rule: poly_add_zq.induct) (auto simp: add.commute)

lemma poly_add_assoc:
  "poly_add_zq (poly_add_zq p1 p2 q) p3 q =
   poly_add_zq p1 (poly_add_zq p2 p3 q) q"
  by (induction p1 p2 arbitrary: p3 rule: poly_add_zq.induct)
     (auto simp: mod_add_left_eq mod_add_right_eq add.assoc)

end
```
