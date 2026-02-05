(*
  Rq_AFP_Bridge.thy - Specification layer for R_q = Z_q[X]/(X^n+1)

  This theory provides a clean algebraic specification of quotient ring operations
  using Isabelle's polynomial mod over finite fields. This makes the
  "multiplication respects reduction" lemmas trivial via standard mod_mult_*_eq facts.

  The key insight: over a field, polynomial remainder satisfies:
    (A * B) mod P = ((A mod P) * (B mod P)) mod P
  which is exactly what ring_mult_ring_mod_right/left need.
*)

theory Rq_AFP_Bridge
  imports
    Main
    "HOL-Computational_Algebra.Polynomial_Factorial"
begin

text \<open>
  We work with polynomials over an arbitrary field. The key facts we need:
  - mod_mult_right_eq: (a * b) mod m = (a * (b mod m)) mod m
  - mod_mult_left_eq: (a * b) mod m = ((a mod m) * b) mod m
  - degree_mod_less: degree (p mod q) < degree q (when q \<noteq> 0)

  These are standard for Euclidean domains (which includes polynomials over fields).
\<close>

type_synonym ipoly = "int list"

text \<open>
  Locale for quotient ring specification.
  - n is the degree of the cyclotomic polynomial X^n + 1
  - 'a is a field type (we use field_char_0 for generality)
\<close>

locale rq_poly_spec =
  fixes n :: nat
  fixes dummy :: "'a::{field, idom_divide}"
begin

text \<open>The modulus polynomial X^n + 1.\<close>
definition modulus_poly :: "'a poly" where
  "modulus_poly = Polynomial.monom 1 n + 1"

text \<open>Basic properties of the modulus polynomial.\<close>

lemma modulus_poly_deg[simp]:
  assumes "n > 0"
  shows "degree modulus_poly = n"
proof -
  have deg_le: "degree (Polynomial.monom (1::'a) n + 1) \<le> n"
    by (rule degree_le) (simp add: assms)
  have coeff_n: "coeff (Polynomial.monom (1::'a) n + 1) n \<noteq> 0"
    using assms by simp
  have deg_ge: "n \<le> degree (Polynomial.monom (1::'a) n + 1)"
    using coeff_n by (rule le_degree)
  from deg_le deg_ge show ?thesis
    unfolding modulus_poly_def by simp
qed

lemma modulus_poly_neq_0[simp]:
  assumes "n > 0"
  shows "modulus_poly \<noteq> (0 :: 'a poly)"
proof
  assume "modulus_poly = (0 :: 'a poly)"
  hence "coeff modulus_poly n = 0"
    by simp
  moreover have "coeff modulus_poly n = 1"
    unfolding modulus_poly_def using assms by simp
  ultimately show False by simp
qed

lemma degree_mod_lt_n:
  assumes "n > 0"
  shows "degree ((p :: 'a poly) mod modulus_poly) < n"
proof -
  have "degree (p mod modulus_poly) < degree modulus_poly \<or> p mod modulus_poly = 0"
    using degree_mod_less[of modulus_poly p] assms by auto
  then show ?thesis
    using assms by (auto simp: modulus_poly_deg)
qed

text \<open>
  THE KEY LEMMAS: multiplication respects reduction mod X^n+1.
  These follow directly from mod_mult_right_eq / mod_mult_left_eq
  which are standard for Euclidean domains.
\<close>

lemma poly_mult_mod_right:
  assumes "n > 0"
  shows "((A :: 'a poly) * (B mod modulus_poly)) mod modulus_poly = (A * B) mod modulus_poly"
  by (simp add: mod_mult_right_eq)

lemma poly_mult_mod_left:
  assumes "n > 0"
  shows "(((A :: 'a poly) mod modulus_poly) * B) mod modulus_poly = (A * B) mod modulus_poly"
  by (simp add: mod_mult_left_eq)

text \<open>The classic quotient ring property: both operands can be reduced first.\<close>
lemma poly_mult_mod_both:
  assumes "n > 0"
  shows "(((A :: 'a poly) mod modulus_poly) * (B mod modulus_poly)) mod modulus_poly =
         (A * B) mod modulus_poly"
  by (simp add: mod_mult_eq)

text \<open>Commutativity comes for free from polynomial multiplication.\<close>
lemma poly_mult_comm:
  "((A :: 'a poly) * B) mod modulus_poly = (B * A) mod modulus_poly"
  by (simp add: mult.commute)

text \<open>Distributivity also follows from polynomial ring laws.\<close>
lemma poly_mult_add_right:
  "((A :: 'a poly) * (B + C)) mod modulus_poly =
   ((A * B) mod modulus_poly + (A * C) mod modulus_poly) mod modulus_poly"
  by (simp add: distrib_left mod_add_eq)

lemma poly_mult_add_left:
  "(((A :: 'a poly) + B) * C) mod modulus_poly =
   ((A * C) mod modulus_poly + (B * C) mod modulus_poly) mod modulus_poly"
  by (simp add: distrib_right mod_add_eq)

end

text \<open>
  Summary:
  - rq_poly_spec provides the key algebraic facts at the polynomial level
  - poly_mult_mod_right / poly_mult_mod_left are the "multiplication respects reduction" lemmas
  - poly_mult_comm is free
  - poly_mult_add_right / poly_mult_add_left are distributivity

  To use these with int list polynomials:
  1. Define a lifting function: int list \<Rightarrow> 'a poly (where 'a is Z_q as a field)
  2. Prove your list-based ring_mod is equivalent to polynomial mod
  3. Transfer the lemmas

  For a prime q, use ('q::prime_card) mod_ring from Berlekamp_Zassenhaus.Finite_Field
  or define your own finite field type.
\<close>

text \<open>
  Alternative approach: work directly with int polynomials and explicit mod q.
  This avoids needing a type-level field but requires more manual bookkeeping.
\<close>

locale rq_int_spec =
  fixes n :: nat
  fixes q :: int
  assumes n_pos: "n > 0"
  assumes q_pos: "q > 1"
begin

text \<open>Lift int list to int poly.\<close>
definition lift_int_poly :: "ipoly \<Rightarrow> int poly" where
  "lift_int_poly xs = Poly xs"

text \<open>The modulus polynomial X^n + 1 over integers.\<close>
definition modulus_int :: "int poly" where
  "modulus_int = Polynomial.monom 1 n + 1"

text \<open>Coefficient-wise mod q.\<close>
definition coeff_mod :: "int poly \<Rightarrow> int poly" where
  "coeff_mod p = Poly (map (\<lambda>i. poly.coeff p i mod q) [0..<Suc (degree p)])"

text \<open>
  Note: Over integers (not a field), polynomial division is more complex.
  The clean approach is to work over Z_q as a field, then pull back.

  For now, we document that the key algebraic facts (mod_mult_*_eq)
  hold at the field level and can be transferred via lifting.
\<close>

end

text \<open>
  The main insight for solving ring_mult_ring_mod_right/left:

  Your list-based ring_mod implements "reduce mod X^n+1" by folding coefficients.
  At the polynomial level, this is just: p mod (X^n + 1).

  Once you establish:
    lift (ring_mod xs n) = (lift xs) mod modulus_poly

  Then ring_mult_ring_mod_right becomes:

    ring_mult a (ring_mod b n) n q
    = unlift ((lift a * lift (ring_mod b n)) mod modulus_poly) mod_coeff q
    = unlift ((lift a * (lift b mod modulus_poly)) mod modulus_poly) mod_coeff q
    = unlift ((lift a * lift b) mod modulus_poly) mod_coeff q    [by mod_mult_right_eq]
    = ring_mult a b n q

  This is the proof pattern that eliminates your sorries.
\<close>

end
