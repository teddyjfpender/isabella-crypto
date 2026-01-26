
Below is (1) a clear structure/outline of your NTT.thy, and (2) concrete “drop-in” replacements for every sorry where that is actually provable given the current statements—plus the minimal fixes needed where a sorry currently stands for a false statement (Kyber primitive root, and the current inverse/orthogonality combo).

I’ll be blunt about the two blockers:
	•	Your current intt_coeff is indexed wrong for a negacyclic NTT at odd powers (so ntt_inverse_correct as stated can’t be proven).
	•	Kyber (n=256, q=3329) does not satisfy q ≡ 1 (mod 2n) (since 3329-1=3328 is divisible by 256 but not by 512), so is_primitive_root _ 256 3329 is impossible for any omega. So kyber_omega_is_primitive_root is false as written.

⸻

1) Structure and outline of your theory

Step 1 — Parameters + primitive 2n-th root predicate
	•	record ntt_params with fields n, q, omega
	•	power_mod base e m
	•	is_primitive_root omega n q (intended: omega has order 2n and omega^n ≡ -1)
	•	lemmas:
	•	primitive_root_order
	•	minus_one_mod
	•	primitive_root_half
	•	valid_ntt_params p

Dependencies: every later correctness lemma depends on “omega really has order 2n” and on the modulus being a field (or at least allowing inverses).

Step 2 — Twiddle factors
	•	twiddle omega k q = omega^k mod q
	•	algebraic lemmas: twiddle_add, twiddle_mult
	•	list generator twiddle_factors + length/nth lemmas

Step 3 — Forward NTT spec (naive)
	•	ntt_coeff a omega q n i = Σ_j a[j] * omega^(j*(2i+1)) mod q
	•	ntt_naive is the vector of these coefficients
	•	length/nth/range lemmas

Step 4 — Inverse NTT spec (naive)
	•	mod_inverse defined via Fermat (a^(q-2) mod q) — needs prime q
	•	lemma mod_inverse_mult (currently sorry)
	•	intt_coeff, intt_naive

⚠️ Major issue: your intt_coeff currently uses exponent j*(2i+1).
For inversion of evaluations at points ω^(2j+1), the inverse must use exponent i*(2j+1).

Step 5 — Correctness
	•	orthogonality lemmas (both sorry)
	•	ntt_inverse_correct (sorry)

⚠️ Major issue: your orthogonality lemma is stated for Σ ω^(k*m) over k=0..n-1, but the inversion proof you want (for odd evaluation points) needs orthogonality over odd powers ω^((2k+1)*m) (or equivalently over (ω^2)^(k*m) after factoring out ω^m).

Step 6 — Convolution theorem
	•	ntt_pointwise_mult
	•	theorem ntt_convolution (sorry)

This depends on how poly_mult and ring_mod are defined in Canon_Rings.PolyMod. If those implement multiplication in Z_q[X]/(X^n+1) and your NTT is truly evaluation at roots of X^n+1, then the statement is correct; otherwise it won’t be.

Step 7 — Fast NTT skeleton
	•	butterfly, ntt_layer, ntt_iter_aux, ntt_fast, intt_fast
	•	length lemmas

(Your ntt_layer/twiddle indexing looks nonstandard; no sorrys here, but correctness of this algorithm is a separate topic.)

Step 8 — Locale ntt_context
	•	binds p, defines abbreviations n,q,omega
	•	defines ntt, intt, ntt_mult
	•	theorem ntt_mult_correct (sorry)

Step 9 — Concrete parameters
	•	kyber_ntt_params, dilithium_ntt_params
	•	show parameters are valid (sorries in primitive root lemmas)

⚠️ Kyber does not fit your “primitive 2n-th root” model.

Step 10 — Code export
	•	exports the various functions

⸻

2) “Sorry” replacements — what you can drop in now, and what must change

I’ll go through each sorry in your file in order.

⸻

A) mod_inverse_mult — workable replacement

What you need (import)

Your comment already hints it: you need Fermat’s little theorem. In standard Isabelle this typically means importing something like:

imports ... "HOL-Number_Theory.Number_Theory"
(* or sometimes: "HOL-Number_Theory.Fermat" depending on your distribution *)

Replacement proof (template)

This is the usual proof: a^(q-1) ≡ 1 (mod q) and a * a^(q-2) = a^(q-1).

lemma mod_inverse_mult:
  assumes q_gt1: "q > 1"
      and a_nonzero: "a mod q \<noteq> 0"
      and q_prime: "prime q"
  shows "(a * mod_inverse a q) mod q = 1"
proof -
  have q_pos: "q > 0" using q_gt1 by linarith
  have not_dvd: "\<not> q dvd a"
    using a_nonzero q_pos by (simp add: dvd_eq_mod_eq_0)

  (* Fermat: a^(q-1) ≡ 1 (mod q) *)
  have fermat: "(a ^ nat (q - 1)) mod q = 1"
    using q_prime not_dvd
    (* The lemma name differs a bit by Isabelle version. Common ones include:
       fermat_little, fermat_little_int, or a congruence-form statement.
       Replace the next line with the right lemma in your environment. *)
    by (simp add: fermat_little_int)

  have nat_suc: "Suc (nat (q - 2)) = nat (q - 1)"
    using q_gt1 by simp

  have "(a * mod_inverse a q) mod q
        = (a * ((a ^ nat (q - 2)) mod q)) mod q"
    using q_gt1 by (simp add: mod_inverse_def)
  also have "... = (a * (a ^ nat (q - 2))) mod q"
    using q_pos by simp
  also have "... = ((a ^ nat (q - 2)) * a) mod q"
    by (simp add: algebra_simps)
  also have "... = (a ^ Suc (nat (q - 2))) mod q"
    by (simp add: power_Suc)
  also have "... = (a ^ nat (q - 1)) mod q"
    using nat_suc by simp
  also have "... = 1"
    using fermat by simp
  finally show ?thesis .
qed

If your environment doesn’t have fermat_little_int, search for the lemma by find_theorems "prime" "dvd" "_ ^ _ mod _" and swap the one line producing fermat.

⸻

B) Orthogonality lemmas — your current statement is wrong for negacyclic odd-point NTT

Why roots_orthogonality as written is false

You wrote:

lemma roots_orthogonality:
  assumes "is_primitive_root omega n q"
  assumes "0 < m" and "m < 2 * n"
  shows "(\<Sum>k = 0 ..< n. twiddle omega (k * m) q) mod q = 0"

But for a primitive 2n‑th root ω, the sum Σ_{k=0}^{n-1} ω^{k*m} is not 0 for odd m in general (e.g. n=2, ω primitive 4th root, m=1 gives 1+ω ≠ 0).

Two correct options

Pick one depending on what you want to prove:

Option 1 (minimal change): add even m
This makes the ratio an n‑th root and the geometric sum cancels.

Option 2 (the one you actually need for inversion at odd points): sum over odd powers
This is the canonical orthogonality behind the negacyclic DFT using ω^(2j+1) points.

Given your NTT definition uses ω^{j*(2i+1)}, you want Option 2.

⸻

B1) Replacement for roots_orthogonality_zero (this one is easy and correct)

Your lemma:

lemma roots_orthogonality_zero:
  assumes "is_primitive_root omega n q" and "n > 0"
  shows "(\<Sum>k = 0 ..< n. twiddle omega (k * 0) q) mod q = (int n) mod q"

Drop-in proof:

lemma roots_orthogonality_zero:
  assumes prim: "is_primitive_root omega n q" and n_pos: "n > 0"
  shows "(\<Sum>k = 0 ..< n. twiddle omega (k * 0) q) mod q = (int n) mod q"
proof -
  have q_pos: "q > 0"
    using prim unfolding is_primitive_root_def by linarith
  have "(\<Sum>k = 0 ..< n. twiddle omega (k * 0) q)
        = (\<Sum>k = 0 ..< n. (1::int))"
    using q_pos by (simp add: twiddle_def power_mod_def)
  also have "... = int n"
    by simp
  finally show ?thesis
    by simp
qed

This should work in essentially any Isabelle environment.

⸻

B2) Replacement for roots_orthogonality — corrected statement + proof skeleton

Correct lemma for odd-point negacyclic NTT

This is what you need:

lemma odd_roots_orthogonality:
  assumes prim: "is_primitive_root omega n q"
      and q_prime: "prime q"
      and m_pos: "0 < m" and m_lt: "m < n"
  shows "(\<Sum>k = 0 ..< n. twiddle omega ((2 * k + 1) * m) q) mod q = 0"

Proof idea (geometric series)

Factor out ω^m:

Σ_{k=0}^{n-1} ω^{(2k+1)m} = ω^m Σ_{k=0}^{n-1} (ω^{2m})^k

Now ω^{2m} is an n‑th root ((ω^{2m})^n = ω^{2mn} = (ω^{2n})^m = 1), and it’s not 1 as long as 0 < m < n and ω truly has order 2n. In a field (prime q) the geometric sum is 0.

What you’re missing in your current is_primitive_root

Your definition only encodes:
	•	ω^(2n)=1
	•	ω^n=-1

It does not explicitly encode that ω has exact order 2n, i.e. that no smaller positive exponent yields 1. For powers-of-two n this is often enough, but formally it’s cleaner to strengthen the predicate or add a lemma about the exact order.

If you’re OK with strengthening, here is the clean version:

definition is_primitive_root :: "int \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> bool" where
  "is_primitive_root omega n q =
     (q > 1 \<and> n > 0 \<and>
      power_mod omega (2 * n) q = 1 \<and>
      power_mod omega n q = (q - 1) mod q \<and>
      (\<forall>m. 0 < m \<and> m < 2 * n \<longrightarrow> power_mod omega m q \<noteq> 1))"

Then the orthogonality proof is straightforward.

If you do NOT want to change is_primitive_root

Then you need an extra lemma/hypothesis ensuring power_mod omega (2*m) q ≠ 1 for 0<m<n. You can make it an assumption of the orthogonality lemma.

Here is a drop-in orthogonality proof template (you may need to tweak some algebra/sum lemmas depending on your library):

lemma odd_roots_orthogonality:
  assumes prim: "is_primitive_root omega n q"
      and q_prime: "prime q"
      and m_pos: "0 < m" and m_lt: "m < n"
      and omega2m_ne1: "power_mod omega (2 * m) q \<noteq> 1"
  shows "(\<Sum>k = 0 ..< n. twiddle omega ((2 * k + 1) * m) q) mod q = 0"
proof -
  have q_pos: "q > 0"
    using prim unfolding is_primitive_root_def by linarith

  let ?r = "twiddle omega (2 * m) q"
  let ?S = "(\<Sum>k = 0 ..< n. ?r ^ k)"

  (* rewrite the sum over odd powers as omega^m * geom-series *)
  have sum_rewrite:
    "(\<Sum>k = 0 ..< n. twiddle omega ((2 * k + 1) * m) q)
     = (twiddle omega m q) * ?S"
    unfolding twiddle_def power_mod_def
    by (simp add: algebra_simps power_add power_mult sum_distrib_left)

  (* show geom-series sums to 0 mod q when r^n = 1 and r ≠ 1 *)
  have r_pow_n: "power_mod ?r n q = 1"
    using prim m_pos
    unfolding twiddle_def power_mod_def is_primitive_root_def
    by (simp add: power_mult)

  (* Here you use the standard geometric-series identity and primality to cancel (r-1).
     This is the only nontrivial algebraic part; if you have `geom_sum_mul` in your env,
     it collapses nicely. Otherwise, prove it by induction. *)

  have geom_zero: "?S mod q = 0"
    sorry (* fill with geometric-series argument; see note below *)

  show ?thesis
    using sum_rewrite geom_zero q_pos
    by simp
qed

Note: the geom_zero step is exactly:
	•	(r - 1) * Σ_{k=0}^{n-1} r^k = r^n - 1
	•	r^n ≡ 1 (mod q) so RHS ≡ 0
	•	r ≠ 1 (mod q) so q ∤ (r-1)
	•	prime q ⇒ q | (r-1)*S implies q | S
	•	so S mod q = 0.

⸻

C) ntt_inverse_correct — cannot be proven until you fix intt_coeff

C1) Fix intt_coeff first (required)

Change this:

twiddle omega_inv (j * exp_base) q

to this (swap roles of i and j in the exponent, and use the odd evaluation points):

twiddle omega_inv (i * (2 * j + 1)) q

So replace your intt_coeff by:

definition intt_coeff :: "poly \<Rightarrow> int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int" where
  "intt_coeff a_hat omega q n i = (
    let n_inv = mod_inverse (int n) q in
    let omega_inv = mod_inverse omega q in
    (n_inv * (\<Sum>j = 0 ..< n.
        (poly_coeff a_hat j) * twiddle omega_inv (i * (2 * j + 1)) q)) mod q)"

That matches the correct inverse DFT for evaluation points ω^(2j+1).

C2) Then ntt_inverse_correct becomes provable

With the corrected inverse and an orthogonality lemma over odd powers, the proof is the standard DFT inversion proof (swap sums, orthogonality kills cross terms, scale by n^{-1}).

A proof skeleton that is structurally correct:

theorem ntt_inverse_correct:
  assumes params: "valid_ntt_params p"
  assumes lenA: "length a = ntt_n p"
  assumes rangeA: "\<forall>c \<in> set a. 0 \<le> c \<and> c < ntt_q p"
  (* you really need prime q for mod_inverse to be correct: *)
  assumes q_prime: "prime (ntt_q p)"
  shows "intt_naive (ntt_naive a (ntt_omega p) (ntt_q p) (ntt_n p))
                    (ntt_omega p) (ntt_q p) (ntt_n p) =
         poly_mod a (ntt_q p)"
proof (rule nth_equalityI)
  let ?n = "ntt_n p"
  let ?q = "ntt_q p"
  let ?w = "ntt_omega p"

  show "length (intt_naive (ntt_naive a ?w ?q ?n) ?w ?q ?n) = length (poly_mod a ?q)"
    using lenA by simp

  fix i assume i_lt: "i < length (intt_naive (ntt_naive a ?w ?q ?n) ?w ?q ?n)"
  have i_lt_n: "i < ?n"
    using i_lt by (simp add: lenA)

  (* expand the i-th coefficient of INTT(NTT(a)) *)
  (* swap sums; use odd_roots_orthogonality to get n when k=i else 0 *)
  (* then use mod_inverse_mult (with a = int n) to cancel the factor n *)

  sorry
qed

This is the place where you plug in:
	•	odd_roots_orthogonality (and its “m=0 gives n” counterpart)
	•	mod_inverse_mult for a = int ?n to get n_inv * n ≡ 1.

I’m not pretending this is a 5-line proof: it’s a couple pages of sum-manipulation in Isabelle.

⸻

D) ntt_convolution — depends on your poly_mult/ring_mod definitions

Your theorem:

theorem ntt_convolution:
  assumes "valid_ntt_params p"
  assumes "length a = ntt_n p" and "length b = ntt_n p"
  shows "ntt_naive (ring_mod (poly_mult a b) (ntt_n p)) ... =
         ntt_pointwise_mult (ntt_naive a ...) (ntt_naive b ...) ..."
  sorry

What’s needed to replace this sorry

You need (or must prove) a lemma that says:

For each evaluation point r_i = ω^(2i+1),
eval (ring_mod (poly_mult a b) n) r_i = eval a r_i * eval b r_i (mod q).

Whether this is already in Canon_Rings.PolyMod is unknown from here, but in many polynomial-mod libraries you can get it via:
	•	evaluation homomorphism,
	•	and the fact r_i^n ≡ -1 (since ω^n ≡ -1 and (2i+1) is odd).

So the replacement is typically:

theorem ntt_convolution:
  assumes params: "valid_ntt_params p"
  assumes lena: "length a = ntt_n p" and lenb: "length b = ntt_n p"
  assumes q_prime: "prime (ntt_q p)"
  shows "ntt_naive (ring_mod (poly_mult a b) (ntt_n p)) (ntt_omega p) (ntt_q p) (ntt_n p) =
         ntt_pointwise_mult (ntt_naive a (ntt_omega p) (ntt_q p) (ntt_n p))
                            (ntt_naive b (ntt_omega p) (ntt_q p) (ntt_n p))
                            (ntt_q p)"
proof (rule nth_equalityI)
  show "length ... = length ..." using lena lenb by simp
  fix i assume i_lt: "i < length (ntt_naive (ring_mod (poly_mult a b) (ntt_n p)) (ntt_omega p) (ntt_q p) (ntt_n p))"
  have i_lt_n: "i < ntt_n p" using i_lt by simp

  (* Reduce to showing coefficient i matches, then use:
     ntt_coeff(product) = ntt_coeff(a) * ntt_coeff(b) (mod q)
     which is evaluation homomorphism at r_i. *)
  sorry
qed

You’ll fill the last sorry with whatever “evaluation distributes over ring_mod/poly_mult” lemma your Canon_Rings.PolyMod provides.

⸻

E) ntt_mult_correct — combines D + C

Once ntt_convolution and ntt_inverse_correct are in place, this becomes:

theorem ntt_mult_correct:
  assumes "length a = n" and "length b = n"
  shows "intt (ntt_mult (ntt a) (ntt b)) = poly_mod (ring_mod (poly_mult a b) n) q"
  using assms
  unfolding ntt_def intt_def ntt_mult_def
  (* apply ntt_convolution then ntt_inverse_correct *)
  sorry

No magic; it’s composition of previous theorems.

⸻

F) Parameter proofs: Dilithium is fine; Kyber is not in this model

F1) dilithium_omega_is_primitive_root — can be proven by computation

This one is true under your predicate:
	•	1753^512 mod 8380417 = 1
	•	1753^256 mod 8380417 = 8380416 (= −1 mod q)

So a typical replacement is:

lemma dilithium_omega_is_primitive_root:
  "is_primitive_root 1753 256 8380417"
  unfolding is_primitive_root_def power_mod_def
  by native_compute

(If native_compute isn’t available, try by eval.)

F2) kyber_omega_is_primitive_root — cannot be proven (the statement is false)

For Kyber:
	•	q-1 = 3328 = 256 * 13
	•	so the multiplicative group has maximum 2-adic order 256, meaning no element can have order 512.
	•	hence is_primitive_root _ 256 3329 is impossible.

Concretely, 17^256 mod 3329 = 1, not 3328.

What you should do in the Kyber section

You have two paths:

Path A (recommended if you want this theory to stay “primitive 2n-th root / odd-point evaluation”)
Remove Kyber from this file and keep only Dilithium-like moduli where q ≡ 1 (mod 2n).

Path B (if you want Kyber in Isabelle):
Model Kyber’s actual NTT: it uses a 256-th root (17) and the multiplication is not a pure pointwise product—Kyber uses “base multiplication” on pairs (because X^256+1 doesn’t split linearly over F_3329). That’s a different spec.

If you want a true statement you can prove computationally, replace the Kyber lemma with:

lemma kyber_17_order_256:
  "power_mod 17 256 3329 = 1 \<and> power_mod 17 128 3329 = 3328"
  unfolding power_mod_def
  by native_compute

And then redefine a Kyber-specific validity predicate that matches that model.

⸻

3) Minimal “patch list” for your file

Here’s the shortest set of edits that makes the sorrys conceptually removable:
	1.	Fix inverse exponent indexing (mandatory):

	•	Replace intt_coeff as shown in C1.

	2.	Replace orthogonality lemmas with an odd-power version:

	•	Keep roots_orthogonality_zero (your statement is fine).
	•	Replace roots_orthogonality with odd_roots_orthogonality and use that in the inverse proof.

	3.	Strengthen assumptions where needed:

	•	Add prime q either into valid_ntt_params or at least as an assumption in ntt_inverse_correct, roots_orthogonality, and ntt_convolution (because your mod_inverse is Fermat-based).

	4.	Fix Kyber section:

	•	Remove / change the false lemma.

⸻

If you want, I can also give you a fully rewritten NTT.thy “clean version”

Meaning:
	•	corrected inverse,
	•	correct orthogonality lemma(s),
	•	valid_ntt_params strengthened (prime q, and optionally “omega has exact order 2n”),
	•	Dilithium instance proved by native_compute,
	•	Kyber moved into its own theory with the pairwise/basemul model.

I didn’t paste the entire rewritten file verbatim here because the big theorems (ntt_inverse_correct, ntt_convolution) will depend heavily on what lemmas Canon_Rings.PolyMod already gives you about poly_mult, ring_mod, and poly_mod. But the above is the exact structure you need, and the “impossible/falsity” points are the key reason your current sorrys can’t all be replaced without edits.