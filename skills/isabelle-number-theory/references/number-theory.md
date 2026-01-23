# Isabelle/HOL Number Theory Reference

## Modular Arithmetic

### Basic Operations

```isabelle
(* Modulo operation *)
value "(17::int) mod 5"   (* Result: 2 *)
value "(-3::int) mod 5"   (* Result: 2 (Isabelle uses floored division) *)

(* Division *)
value "(17::int) div 5"   (* Result: 3 *)

(* Key properties *)
lemma "(a + b) mod n = ((a mod n) + (b mod n)) mod n"
  by (simp add: mod_add_eq)

lemma "(a * b) mod n = ((a mod n) * (b mod n)) mod n"
  by (simp add: mod_mult_eq)

lemma "(a mod n) mod n = a mod n"
  by simp
```

### Modular Arithmetic in Z_n

```isabelle
(* Define Z_n operations *)
definition add_mod :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "add_mod n a b = (a + b) mod n"

definition mult_mod :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "mult_mod n a b = (a * b) mod n"

definition sub_mod :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "sub_mod n a b = (a + n - b mod n) mod n"

definition neg_mod :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "neg_mod n a = (n - a mod n) mod n"
```

### Properties of mod

```isabelle
(* Division algorithm *)
lemma div_mod_decomp: "(a::int) = (a div n) * n + (a mod n)"
  by simp

(* Range of mod *)
lemma mod_range: "n > 0 \<Longrightarrow> 0 \<le> (a::int) mod n \<and> a mod n < n"
  by simp

(* Congruence *)
definition cong :: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> bool" ("_ \<equiv> _ '(mod _')" [50,50,50] 50) where
  "a \<equiv> b (mod n) \<longleftrightarrow> n dvd (a - b)"

lemma cong_mod: "a \<equiv> b (mod n) \<longleftrightarrow> a mod n = b mod n"
  by (auto simp: cong_def dvd_eq_mod_eq_0)
```

## Greatest Common Divisor

### GCD Basics

```isabelle
(* Built-in gcd *)
value "gcd (12::nat) 8"   (* Result: 4 *)
value "gcd (35::int) 14"  (* Result: 7 *)

(* Key properties *)
lemma "gcd a b = gcd b a"
  by (simp add: gcd.commute)

lemma "gcd (gcd a b) c = gcd a (gcd b c)"
  by (simp add: gcd.assoc)

lemma "gcd a 0 = a"
  by simp

lemma "gcd a a = a"
  by simp

(* Bezout's identity *)
lemma bezout: "\<exists>s t. gcd a b = s * a + t * b"
  by (rule bezout_int)
```

### Euclidean Algorithm

```isabelle
(* Recursive GCD (already defined, but for illustration) *)
fun my_gcd :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "my_gcd a 0 = a"
| "my_gcd a b = my_gcd b (a mod b)"

lemma my_gcd_correct: "my_gcd a b = gcd a b"
  by (induction a b rule: my_gcd.induct) auto
```

### Extended Euclidean Algorithm

```isabelle
(* Returns (g, s, t) where g = gcd(a,b) = s*a + t*b *)
fun extended_gcd :: "int \<Rightarrow> int \<Rightarrow> int \<times> int \<times> int" where
  "extended_gcd a 0 = (a, 1, 0)"
| "extended_gcd a b =
     (let (g, s, t) = extended_gcd b (a mod b)
      in (g, t, s - (a div b) * t))"

lemma extended_gcd_correct:
  assumes "b \<ge> 0"
  shows "let (g, s, t) = extended_gcd a b in
         g = gcd a b \<and> g = s * a + t * b"
  using assms by (induction a b rule: extended_gcd.induct) auto

(* Usage example *)
value "extended_gcd 35 15"  (* Result: (5, 1, -2) since 5 = 1*35 + (-2)*15 *)
```

### Coprimality

```isabelle
(* Definition *)
definition coprime' :: "int \<Rightarrow> int \<Rightarrow> bool" where
  "coprime' a b \<longleftrightarrow> gcd a b = 1"

(* Built-in coprime *)
lemma "coprime a b \<longleftrightarrow> gcd a b = 1"
  by (simp add: coprime_iff_gcd_eq_1)

(* Key properties *)
lemma "coprime a b \<Longrightarrow> coprime a c \<Longrightarrow> coprime a (b * c)"
  by (simp add: coprime_mult_right_iff)

lemma "prime p \<Longrightarrow> \<not>(p dvd a) \<Longrightarrow> coprime p a"
  by (simp add: prime_imp_coprime)
```

## Modular Inverse

### Computing Inverses

```isabelle
(* Modular inverse using extended GCD *)
definition mod_inverse :: "int \<Rightarrow> int \<Rightarrow> int option" where
  "mod_inverse a n =
     (if gcd a n = 1
      then let (_, s, _) = extended_gcd a n in Some (s mod n)
      else None)"

lemma mod_inverse_correct:
  assumes "gcd a n = 1" "n > 0"
  shows "the (mod_inverse a n) * a mod n = 1"
  using assms by (auto simp: mod_inverse_def Let_def)

(* Alternative: power-based for prime modulus *)
definition mod_inverse_prime :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "mod_inverse_prime a p = (a ^ (p - 2)) mod p"
```

### Inverse Properties

```isabelle
lemma inverse_unique:
  assumes "a * b mod n = 1" "a * c mod n = 1" "n > 0"
  shows "b mod n = c mod n"
  using assms by (metis mod_mult_right_eq mult.commute mult.left_neutral)

lemma inverse_mult:
  assumes "gcd a n = 1" "gcd b n = 1"
  shows "mod_inverse (a * b) n =
         Some ((the (mod_inverse a n) * the (mod_inverse b n)) mod n)"
  using assms sorry
```

## Prime Numbers

### Primality

```isabelle
(* Built-in prime predicate *)
lemma "prime (7::nat)"
  by eval

lemma "\<not> prime (9::nat)"
  by eval

(* Definition *)
lemma prime_def_alt: "prime p \<longleftrightarrow> p > 1 \<and> (\<forall>m. m dvd p \<longrightarrow> m = 1 \<or> m = p)"
  by (simp add: prime_nat_iff)
```

### Prime Testing

```isabelle
(* Trial division *)
fun is_prime_trial :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
  "is_prime_trial n k =
     (if k * k > n then True
      else if n mod k = 0 then False
      else is_prime_trial n (k + 1))"

definition is_prime :: "nat \<Rightarrow> bool" where
  "is_prime n = (n > 1 \<and> is_prime_trial n 2)"

lemma is_prime_correct: "n > 1 \<Longrightarrow> is_prime n = prime n"
  sorry (* Requires careful proof *)
```

### Prime Factorization

```isabelle
(* Prime factors *)
definition prime_factors :: "nat \<Rightarrow> nat set" where
  "prime_factors n = {p. prime p \<and> p dvd n}"

(* Fundamental theorem of arithmetic *)
lemma prime_factorization_exists:
  "n > 0 \<Longrightarrow> \<exists>f. n = prod f (prime_factors n)"
  sorry
```

## Fermat's Little Theorem

### Statement

```isabelle
theorem fermat_little:
  assumes "prime p" "\<not>(p dvd a)"
  shows "a ^ (p - 1) mod p = 1"
  using assms by (simp add: fermat_theorem)

(* Consequence for inverse *)
corollary fermat_inverse:
  assumes "prime p" "\<not>(p dvd a)"
  shows "a * (a ^ (p - 2)) mod p = 1"
  using assms fermat_little
  by (metis Suc_diff_Suc diff_Suc_1 mod_mult_right_eq mult.commute
            power_Suc prime_gt_1_nat)
```

### Application: Fast Modular Exponentiation

```isabelle
(* Square-and-multiply *)
fun fast_exp_mod :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "fast_exp_mod _ 0 _ = 1"
| "fast_exp_mod b e m =
     (let half = fast_exp_mod b (e div 2) m;
          sq = (half * half) mod m
      in if even e then sq else (sq * b) mod m)"

lemma fast_exp_mod_correct:
  "m > 0 \<Longrightarrow> fast_exp_mod b e m = (b ^ e) mod m"
  by (induction b e m rule: fast_exp_mod.induct)
     (auto simp: Let_def power_even_eq power_odd_eq mod_mult_eq)
```

## Euler's Theorem

### Euler's Totient Function

```isabelle
(* phi(n) = count of k < n coprime to n *)
definition euler_phi :: "nat \<Rightarrow> nat" where
  "euler_phi n = card {k \<in> {1..n}. gcd k n = 1}"

(* Properties *)
lemma phi_prime: "prime p \<Longrightarrow> euler_phi p = p - 1"
  by (simp add: euler_phi_def) sorry

lemma phi_prime_power: "prime p \<Longrightarrow> euler_phi (p^k) = p^k - p^(k-1)"
  sorry

lemma phi_mult: "coprime m n \<Longrightarrow> euler_phi (m * n) = euler_phi m * euler_phi n"
  sorry
```

### Euler's Theorem Statement

```isabelle
theorem euler_theorem:
  assumes "coprime a n" "n > 0"
  shows "a ^ (euler_phi n) mod n = 1"
  using assms by (simp add: euler_theorem)
```

## Chinese Remainder Theorem

### CRT Statement

```isabelle
theorem chinese_remainder:
  assumes "coprime m n"
  shows "\<exists>!x \<in> {0..<m*n}. x mod m = a mod m \<and> x mod n = b mod n"
  using assms by (rule chinese_remainder_unique)
```

### CRT Construction

```isabelle
(* Compute x such that x = a (mod m) and x = b (mod n) *)
definition crt :: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int" where
  "crt a m b n =
     (let (_, s, t) = extended_gcd m n in
      (a * t * n + b * s * m) mod (m * n))"

lemma crt_correct:
  assumes "coprime m n" "m > 0" "n > 0"
  shows "crt a m b n mod m = a mod m \<and> crt a m b n mod n = b mod n"
  using assms by (auto simp: crt_def Let_def) sorry
```

### CRT for Multiple Moduli

```isabelle
(* Generalized CRT *)
fun crt_list :: "(int \<times> int) list \<Rightarrow> int" where
  "crt_list [] = 0"
| "crt_list [(a, m)] = a mod m"
| "crt_list ((a, m) # (b, n) # rest) = crt_list ((crt a m b n, m * n) # rest)"

lemma crt_list_correct:
  assumes "pairwise_coprime (map snd eqs)"
  shows "\<forall>(a, m) \<in> set eqs. crt_list eqs mod m = a mod m"
  sorry
```

### CRT Isomorphism

```isabelle
(* Z_{mn} ≅ Z_m × Z_n when gcd(m,n) = 1 *)
definition crt_iso :: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<times> int" where
  "crt_iso m n x = (x mod m, x mod n)"

definition crt_iso_inv :: "int \<Rightarrow> int \<Rightarrow> int \<times> int \<Rightarrow> int" where
  "crt_iso_inv m n (a, b) = crt a m b n"

lemma crt_iso_bijective:
  assumes "coprime m n" "m > 0" "n > 0"
  shows "bij_betw (crt_iso m n) {0..<m*n} ({0..<m} \<times> {0..<n})"
  using assms sorry
```

## Number-Theoretic Transform (NTT)

### Primitive Roots

```isabelle
(* Primitive root mod n *)
definition primitive_root :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
  "primitive_root g n \<longleftrightarrow>
     g > 0 \<and> coprime g n \<and>
     (\<forall>k. 0 < k \<and> k < euler_phi n \<longrightarrow> g ^ k mod n \<noteq> 1) \<and>
     g ^ (euler_phi n) mod n = 1"

(* Existence *)
lemma primitive_root_exists_prime:
  assumes "prime p"
  shows "\<exists>g. primitive_root g p"
  sorry
```

### NTT for Ring Operations

```isabelle
(* NTT: transform polynomial to point-value representation *)
definition ntt :: "nat \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> nat list" where
  "ntt n q coeffs =
     (let omega = primitive_nth_root n q in
      map (\<lambda>i. fold (\<lambda>(j, c) acc. (acc + c * omega^(i*j)) mod q)
                     (zip [0..<n] coeffs) 0)
          [0..<n])"

(* Inverse NTT *)
definition intt :: "nat \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> nat list" where
  "intt n q vals =
     (let omega_inv = mod_inverse_prime (primitive_nth_root n q) q;
          n_inv = mod_inverse_prime n q in
      map (\<lambda>c. (c * n_inv) mod q)
          (ntt n q (map (\<lambda>i. fold (\<lambda>(j, v) acc. (acc + v * omega_inv^(i*j)) mod q)
                                   (zip [0..<n] vals) 0)
                        [0..<n])))"

(* NTT multiplication is pointwise *)
lemma ntt_convolution:
  "ntt n q (poly_mult_mod p1 p2 n q) =
   map2 (\<lambda>a b. (a * b) mod q) (ntt n q p1) (ntt n q p2)"
  sorry
```

## Quadratic Residues

### Definition

```isabelle
definition quadratic_residue :: "int \<Rightarrow> int \<Rightarrow> bool" where
  "quadratic_residue a n \<longleftrightarrow> (\<exists>x. x^2 mod n = a mod n)"

(* Legendre symbol for prime p *)
definition legendre :: "int \<Rightarrow> int \<Rightarrow> int" where
  "legendre a p =
     (if p dvd a then 0
      else if quadratic_residue a p then 1
      else -1)"
```

### Euler's Criterion

```isabelle
theorem euler_criterion:
  assumes "prime p" "p > 2"
  shows "legendre a p = a ^ ((p - 1) div 2) mod p"
  sorry
```

## Complete Example

```isabelle
theory Number_Theory_Example
  imports Main "HOL-Number_Theory.Number_Theory" "HOL-Library.Code_Target_Numeral"
begin

section \<open>RSA Key Generation Helpers\<close>

definition generate_rsa_modulus :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "generate_rsa_modulus p q = p * q"

definition generate_rsa_totient :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "generate_rsa_totient p q = (p - 1) * (q - 1)"

definition rsa_public_exponent :: "nat" where
  "rsa_public_exponent = 65537"

definition rsa_private_exponent :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "rsa_private_exponent p q =
     nat (the (mod_inverse (int rsa_public_exponent)
                           (int (generate_rsa_totient p q))))"

section \<open>RSA Operations\<close>

definition rsa_encrypt :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "rsa_encrypt n e m = fast_exp_mod m e n"

definition rsa_decrypt :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "rsa_decrypt n d c = fast_exp_mod c d n"

section \<open>Correctness\<close>

theorem rsa_correct:
  assumes "prime p" "prime q" "p \<noteq> q"
    and "m < p * q"
    and "gcd rsa_public_exponent ((p-1)*(q-1)) = 1"
  shows "rsa_decrypt (p*q) (rsa_private_exponent p q)
                     (rsa_encrypt (p*q) rsa_public_exponent m) = m"
  using assms sorry

section \<open>Code Export\<close>

export_code
  fast_exp_mod extended_gcd mod_inverse
  rsa_encrypt rsa_decrypt
  in Haskell module_name RSA

end
```
