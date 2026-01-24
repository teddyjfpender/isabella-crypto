# Isabelle/HOL Lattice Cryptography Reference

## Overview of Lattice Cryptography

Lattice-based cryptography relies on the hardness of certain computational problems on lattices. Key advantages:
- Believed to be **post-quantum secure**
- Worst-case to average-case reductions exist
- Enables advanced primitives (FHE, attribute-based encryption)

## Fundamental Lattice Problems

### Shortest Vector Problem (SVP)

Find the shortest non-zero vector in a lattice.

```isabelle
theory Lattice_Problems
  imports Main "HOL-Library.Code_Target_Numeral"
begin

type_synonym int_vec = "int list"

(* Euclidean norm squared (avoiding reals for now) *)
definition norm_sq :: "int_vec \<Rightarrow> int" where
  "norm_sq v = sum_list (map (\<lambda>x. x * x) v)"

(* SVP: find shortest non-zero vector *)
definition svp_solution :: "int_vec list \<Rightarrow> int_vec \<Rightarrow> bool" where
  "svp_solution basis v = (
     v \<noteq> replicate (length v) 0 \<and>
     v \<in> lattice_span basis \<and>
     (\<forall>u \<in> lattice_span basis. u \<noteq> replicate (length u) 0 \<longrightarrow>
        norm_sq v \<le> norm_sq u))"

end
```

### Approximate SVP (SVP_gamma)

Find a non-zero vector within factor gamma of the shortest.

```isabelle
definition svp_gamma_solution :: "real \<Rightarrow> int_vec list \<Rightarrow> int_vec \<Rightarrow> bool" where
  "svp_gamma_solution gamma basis v = (
     v \<noteq> replicate (length v) 0 \<and>
     v \<in> lattice_span basis \<and>
     (\<exists>u \<in> lattice_span basis. u \<noteq> replicate (length u) 0 \<and>
        norm_sq v \<le> gamma^2 * norm_sq u))"
```

### Closest Vector Problem (CVP)

Find the lattice point closest to a target.

```isabelle
definition cvp_solution :: "int_vec list \<Rightarrow> int_vec \<Rightarrow> int_vec \<Rightarrow> bool" where
  "cvp_solution basis target v = (
     v \<in> lattice_span basis \<and>
     (\<forall>u \<in> lattice_span basis.
        norm_sq (vec_sub target v) \<le> norm_sq (vec_sub target u)))"

definition vec_sub :: "int_vec \<Rightarrow> int_vec \<Rightarrow> int_vec" where
  "vec_sub v w = map2 (-) v w"
```

## Short Integer Solution (SIS)

### Problem Definition

Given random matrix A, find short non-zero x such that Ax = 0 (mod q).

```isabelle
type_synonym int_matrix = "int list list"

(* Matrix-vector multiplication mod q *)
definition mat_vec_mult_mod :: "int_matrix \<Rightarrow> int_vec \<Rightarrow> int \<Rightarrow> int_vec" where
  "mat_vec_mult_mod A x q = map (\<lambda>row. sum_list (map2 (*) row x) mod q) A"

(* SIS instance *)
record sis_instance =
  sis_n :: nat      (* rows *)
  sis_m :: nat      (* columns *)
  sis_q :: int      (* modulus *)
  sis_beta :: int   (* bound on solution norm *)
  sis_A :: int_matrix

(* SIS solution predicate *)
definition is_sis_solution :: "sis_instance \<Rightarrow> int_vec \<Rightarrow> bool" where
  "is_sis_solution inst x = (
     length x = sis_m inst \<and>
     x \<noteq> replicate (sis_m inst) 0 \<and>
     mat_vec_mult_mod (sis_A inst) x (sis_q inst) = replicate (sis_n inst) 0 \<and>
     norm_sq x \<le> (sis_beta inst)^2)"
```

### SIS Hardness Assumption

```isabelle
(* SIS advantage of adversary A *)
definition sis_advantage ::
  "(sis_instance \<Rightarrow> int_vec option) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> int \<Rightarrow> real" where
  "sis_advantage adversary n m q beta =
     measure_pmf.prob (sis_game adversary n m q beta) {True}"

(* SIS assumption: advantage is negligible *)
definition sis_secure :: "nat \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> int \<Rightarrow> bool" where
  "sis_secure n m q beta = (\<forall>ppt_adv.
     negligible (\<lambda>k. sis_advantage ppt_adv (n k) (m k) (q k) (beta k)))"
```

## Learning With Errors (LWE)

### Problem Definition

Given (A, b = As + e mod q) where e is small error, find s.

```isabelle
(* Discrete Gaussian-like error (simplified) *)
definition small_error :: "int \<Rightarrow> int set" where
  "small_error bound = {e. \<bar>e\<bar> \<le> bound}"

(* LWE instance *)
record lwe_instance =
  lwe_n :: nat       (* secret dimension *)
  lwe_m :: nat       (* number of samples *)
  lwe_q :: int       (* modulus *)
  lwe_sigma :: real  (* error parameter *)
  lwe_A :: int_matrix
  lwe_b :: int_vec

(* LWE distribution: (A, As + e mod q) *)
definition lwe_sample ::
  "nat \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> int_vec \<Rightarrow> int_vec \<Rightarrow> int_matrix \<times> int_vec" where
  "lwe_sample n m q s e =
     (let A = random_matrix n m q in
      (A, map (\<lambda>i. (inner_prod (A ! i) s + (e ! i)) mod q) [0..<m]))"

(* Search-LWE: find secret s *)
definition search_lwe_solution :: "lwe_instance \<Rightarrow> int_vec \<Rightarrow> bool" where
  "search_lwe_solution inst s = (
     length s = lwe_n inst \<and>
     (\<exists>e. length e = lwe_m inst \<and>
          (\<forall>i < lwe_m inst. \<bar>e ! i\<bar> \<le> lwe_sigma inst) \<and>
          lwe_b inst = mat_vec_mult_mod (lwe_A inst) s (lwe_q inst)
                       +\<^sub>v e mod\<^sub>v (lwe_q inst)))"
```

### Decision LWE

Distinguish LWE samples from uniform.

```isabelle
(* Decision-LWE: distinguish (A, As+e) from (A, u) *)
definition decision_lwe_advantage ::
  "(int_matrix \<times> int_vec \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> real \<Rightarrow> real" where
  "decision_lwe_advantage distinguisher n m q sigma =
     \<bar>Pr[b \<leftarrow> coin;
         A \<leftarrow> random_matrix n m q;
         s \<leftarrow> random_vec n q;
         e \<leftarrow> gaussian_vec m sigma;
         u \<leftarrow> random_vec m q;
         let b' = distinguisher (A, if b then A*s+e else u) in
         return (b = b')]
      - 1/2\<bar>"

(* LWE assumption *)
definition lwe_secure :: "nat \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> real \<Rightarrow> bool" where
  "lwe_secure n m q sigma = (\<forall>ppt_dist.
     negligible (\<lambda>k. decision_lwe_advantage ppt_dist (n k) (m k) (q k) (sigma k)))"
```

### LWE-Based Encryption (Regev's Scheme)

Regev's scheme is a foundational lattice-based PKE, secure under the LWE assumption.

#### Parameters
- **n**: Security parameter (dimension of secret vector)
- **q**: Prime modulus (polynomial in n, typically q = poly(n))
- **N**: Number of LWE samples (rows of A, typically N ≥ (n+1) log q)
- **χ**: Error distribution (discrete Gaussian with small σ)

#### Algorithms

**KeyGen**:
1. s ← ℤ_q^n (uniform random secret)
2. A ← ℤ_q^(N×n) (uniform random matrix)
3. e ← χ^N (error vector)
4. b = A·s + e (mod q)
5. pk = (A, b), sk = s

**Encrypt(pk, m ∈ {0,1})**:
1. r ← {0,1}^N (random binary vector)
2. u = A^T · r (mod q) ∈ ℤ_q^n
3. v = b^T · r + ⌊q/2⌋ · m (mod q) ∈ ℤ_q
4. ct = (u, v)

**Decrypt(sk, ct)**:
1. d = v - s^T · u (mod q)
2. m = 1 if |d - q/2| < |d|, else m = 0

#### Correctness Analysis

Decryption computes:
```
d = v - s^T · u
  = (b^T · r + ⌊q/2⌋ · m) - s^T · (A^T · r)
  = ((As + e)^T · r + ⌊q/2⌋ · m) - s^T · A^T · r
  = e^T · r + ⌊q/2⌋ · m
```

**Correctness condition**: |e^T · r| < ⌊q/4⌋

Since r ∈ {0,1}^N (at most N ones) and e has small entries bounded by B:
- |e^T · r| ≤ N · B
- Correctness requires: N · B < q/4

#### Isabelle Formalization Pattern

```isabelle
theory LWE_Encryption
  imports Main "HOL-Library.Code_Target_Numeral"
begin

type_synonym int_vec = "int list"
type_synonym int_matrix = "int list list"

(* Vector operations *)
definition inner_prod :: "int_vec \<Rightarrow> int_vec \<Rightarrow> int" where
  "inner_prod u v = sum_list (map2 (*) u v)"

definition mat_transpose_vec_mult :: "int_matrix \<Rightarrow> int_vec \<Rightarrow> int_vec" where
  "mat_transpose_vec_mult A r = map (\<lambda>col. inner_prod col r) (transpose A)"

(* Encoding: 0 ↦ 0, 1 ↦ ⌊q/2⌋ *)
definition encode_bit :: "int \<Rightarrow> bool \<Rightarrow> int" where
  "encode_bit q b = (if b then q div 2 else 0)"

(* Decoding: closer to 0 → False, closer to q/2 → True *)
definition decode_bit :: "int \<Rightarrow> int \<Rightarrow> bool" where
  "decode_bit q d = (let d' = d mod q in
                     \<bar>d' - q div 2\<bar> < \<bar>d'\<bar>)"

(* Key and ciphertext records *)
record lwe_public_key =
  pk_A :: int_matrix
  pk_b :: int_vec

record lwe_secret_key =
  sk_s :: int_vec

record lwe_ciphertext =
  ct_u :: int_vec
  ct_v :: int

(* Encryption: pk, modulus q, random r, bit m → ciphertext *)
definition lwe_encrypt :: "lwe_public_key \<Rightarrow> int \<Rightarrow> int_vec \<Rightarrow> bool \<Rightarrow> lwe_ciphertext" where
  "lwe_encrypt pk q r m =
     (let u = map (\<lambda>x. x mod q) (mat_transpose_vec_mult (pk_A pk) r);
          v = (inner_prod (pk_b pk) r + encode_bit q m) mod q
      in \<lparr> ct_u = u, ct_v = v \<rparr>)"

(* Decryption: sk, modulus q, ciphertext → bit *)
definition lwe_decrypt :: "lwe_secret_key \<Rightarrow> int \<Rightarrow> lwe_ciphertext \<Rightarrow> bool" where
  "lwe_decrypt sk q ct =
     (let d = (ct_v ct - inner_prod (sk_s sk) (ct_u ct)) mod q
      in decode_bit q d)"

(* Correctness theorem (requires error bound assumption) *)
theorem lwe_correctness:
  assumes pk_valid: "pk_b pk = map (\<lambda>x. x mod q) (vec_add (mat_vec_mult (pk_A pk) (sk_s sk)) e)"
    and error_bound: "\<bar>inner_prod e r\<bar> < q div 4"
    and q_positive: "q > 2"
  shows "lwe_decrypt sk q (lwe_encrypt pk q r m) = m"
  (* Proof expands definitions and uses error_bound *)
  sorry

end
```

#### Parameter Selection for Correctness

For correctness with probability 1 - δ:
- With N samples, r has at most N ones
- If e_i bounded by B (e.g., B = 6σ with discrete Gaussian)
- Need: N · B < q/4
- Example: n=512, N=1024, B=10 → need q > 4·1024·10 = 40960

Typical parameters (Regev original):
- q = Õ(n²) for security
- σ = 1/√(2π) · √n
- N = (n + 1)⌈log q⌉

## Ring-LWE (RLWE)

### Polynomial Rings

RLWE works over polynomial rings R_q = Z_q[X]/(f(X)).

```isabelle
(* Polynomial represented as coefficient list *)
type_synonym int_poly = "int list"

(* Polynomial ring modulus: typically X^n + 1 for power-of-2 n *)
definition cyclotomic_poly :: "nat \<Rightarrow> int_poly" where
  "cyclotomic_poly n = replicate n 0 @ [1, 1]"  (* X^n + 1 *)

(* Polynomial multiplication mod (X^n + 1, q) *)
definition poly_mult_mod :: "int_poly \<Rightarrow> int_poly \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> int_poly" where
  "poly_mult_mod p1 p2 n q = reduce_mod_cyclotomic (poly_mult p1 p2) n q"

definition reduce_mod_cyclotomic :: "int_poly \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> int_poly" where
  "reduce_mod_cyclotomic p n q =
     (let len = length p in
      if len \<le> n then map (\<lambda>c. c mod q) (p @ replicate (n - len) 0)
      else map (\<lambda>c. c mod q)
           (map2 (-) (take n p) (drop n p @ replicate (2*n - len) 0)))"
```

### RLWE Problem

```isabelle
record rlwe_instance =
  rlwe_n :: nat       (* polynomial degree *)
  rlwe_q :: int       (* coefficient modulus *)
  rlwe_sigma :: real  (* error parameter *)
  rlwe_a :: int_poly  (* public polynomial *)
  rlwe_b :: int_poly  (* b = a*s + e *)

(* RLWE sample *)
definition rlwe_sample :: "nat \<Rightarrow> int \<Rightarrow> int_poly \<Rightarrow> int_poly \<Rightarrow>
                          int_poly \<times> int_poly" where
  "rlwe_sample n q s e =
     (let a = random_poly n q in
      (a, poly_add_mod (poly_mult_mod a s n q) e n q))"

(* Decision-RLWE *)
definition decision_rlwe_advantage ::
  "(int_poly \<times> int_poly \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> real \<Rightarrow> real" where
  "decision_rlwe_advantage dist n q sigma =
     \<bar>Pr[rlwe_vs_uniform_game dist n q sigma] - 1/2\<bar>"
```

### RLWE-Based Encryption

```isabelle
(* RLWE Key Generation *)
definition rlwe_keygen :: "nat \<Rightarrow> int \<Rightarrow> real \<Rightarrow>
                          int_poly \<times> int_poly \<times> int_poly" where
  "rlwe_keygen n q sigma =
     (let a = random_poly n q;
          s = gaussian_poly n sigma;
          e = gaussian_poly n sigma;
          b = poly_add_mod (poly_mult_mod a s n q) e n q
      in (a, b, s))"

(* Encryption *)
definition rlwe_encrypt :: "int_poly \<Rightarrow> int_poly \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> int_poly \<Rightarrow> real \<Rightarrow>
                           int_poly \<times> int_poly" where
  "rlwe_encrypt a b n q msg sigma =
     (let r = ternary_poly n;  (* coefficients in {-1, 0, 1} *)
          e1 = gaussian_poly n sigma;
          e2 = gaussian_poly n sigma;
          u = poly_add_mod (poly_mult_mod a r n q) e1 n q;
          v = poly_add_mod (poly_add_mod (poly_mult_mod b r n q) e2 n q)
                           (scale_poly (q div 2) msg) n q
      in (u, v))"
```

## Module-LWE (MLWE)

Generalization using module lattices (used in Kyber/CRYSTALS).

```isabelle
type_synonym poly_vec = "int_poly list"
type_synonym poly_matrix = "int_poly list list"

record mlwe_instance =
  mlwe_n :: nat       (* polynomial degree *)
  mlwe_k :: nat       (* module rank *)
  mlwe_q :: int
  mlwe_sigma :: real
  mlwe_A :: poly_matrix
  mlwe_b :: poly_vec

definition mlwe_sample :: "nat \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> poly_vec \<Rightarrow> poly_vec \<Rightarrow>
                          poly_matrix \<times> poly_vec" where
  "mlwe_sample n k q s e =
     (let A = random_poly_matrix k k n q in
      (A, poly_vec_add (poly_mat_vec_mult A s n q) e n q))"
```

## Security Reductions

### SIS to SVP Reduction

```isabelle
(* Ajtai's reduction: SIS hardness from worst-case SVP *)
theorem sis_from_svp:
  assumes "svp_gamma_hard n (poly gamma)"
  shows "sis_secure n m q beta"
  (* Proof involves showing an efficient SIS solver
     implies efficient approximate SVP solver *)
  sorry
```

### LWE to GapSVP Reduction

```isabelle
(* Regev's reduction *)
theorem lwe_from_gapsvp:
  assumes "gapsvp_gamma_hard n"
    and "q \<ge> 2 * sqrt n / alpha"
    and "sigma = alpha * q"
  shows "lwe_secure n m q sigma"
  sorry
```

### Search to Decision LWE

```isabelle
(* For prime q, search-LWE reduces to decision-LWE *)
theorem search_to_decision_lwe:
  assumes "prime q"
  shows "search_lwe_advantage A n m q sigma \<le>
         n * decision_lwe_advantage D n m q sigma + negl"
  sorry
```

## Discrete Gaussian Distribution

### Definition

```isabelle
(* Discrete Gaussian probability *)
definition discrete_gaussian_prob :: "real \<Rightarrow> int \<Rightarrow> real" where
  "discrete_gaussian_prob sigma x =
     exp (- (real_of_int x)^2 / (2 * sigma^2)) /
     (\<Sum>z \<in> UNIV. exp (- (real_of_int z)^2 / (2 * sigma^2)))"

(* Discrete Gaussian as probability mass function *)
definition discrete_gaussian_pmf :: "real \<Rightarrow> int pmf" where
  "discrete_gaussian_pmf sigma =
     pmf_of_set_with_prob UNIV (discrete_gaussian_prob sigma)"
```

### Tail Bounds

```isabelle
(* Gaussian tail bound *)
lemma gaussian_tail_bound:
  assumes "t > 0"
  shows "Pr[x \<leftarrow> discrete_gaussian sigma. \<bar>x\<bar> > t * sigma] \<le> 2 * exp(-t^2/2)"
  sorry

(* Consequence: with high probability, error is bounded *)
lemma error_bounded_whp:
  assumes "sigma = alpha * q"
    and "t = omega(sqrt(log n))"
  shows "Pr[e \<leftarrow> gaussian_vec n sigma. norm e > t * sigma * sqrt n] = negl"
  sorry
```

## Cryptographic Constructions

### Lattice-Based Signature (GPV Framework)

```isabelle
(* GPV signature scheme *)
record gpv_params =
  gpv_n :: nat
  gpv_q :: int
  gpv_sigma :: real

definition gpv_keygen :: "gpv_params \<Rightarrow> int_matrix \<times> int_matrix" where
  "gpv_keygen params =
     (let (A, T) = trapdoor_gen (gpv_n params) (gpv_q params) in
      (A, T))"  (* pk = A, sk = trapdoor T *)

definition gpv_sign :: "int_matrix \<Rightarrow> int_matrix \<Rightarrow> gpv_params \<Rightarrow>
                       int_vec \<Rightarrow> int_vec" where
  "gpv_sign A T params msg =
     sample_pre A T (hash msg) (gpv_sigma params) (gpv_q params)"

definition gpv_verify :: "int_matrix \<Rightarrow> int_vec \<Rightarrow> int_vec \<Rightarrow>
                         gpv_params \<Rightarrow> bool" where
  "gpv_verify A msg sig params =
     (mat_vec_mult_mod A sig (gpv_q params) = hash msg \<and>
      norm_sq sig \<le> (gpv_sigma params * sqrt (gpv_n params))^2)"
```

### Key Encapsulation (Kyber-style)

```isabelle
definition kyber_encaps :: "poly_matrix \<Rightarrow> poly_vec \<Rightarrow> nat \<Rightarrow> int \<Rightarrow>
                           poly_vec \<times> poly_vec \<times> int_poly" where
  "kyber_encaps A t n q =
     (let r = ternary_poly_vec n;
          e1 = small_poly_vec n;
          e2 = small_poly n;
          u = poly_vec_add (poly_mat_vec_mult (transpose_poly_mat A) r n q) e1 n q;
          v = poly_add_mod (poly_add_mod (inner_prod_poly t r n q) e2 n q)
                           (encode_message msg) n q;
          K = hash (msg, u, v)
      in (u, v, K))"
```

## Parameter Selection

### Security Levels

```isabelle
(* NIST security levels *)
datatype security_level = Level1 | Level2 | Level3 | Level4 | Level5

(* Parameter sets for different security levels *)
definition lwe_params :: "security_level \<Rightarrow> nat \<times> nat \<times> int \<times> real" where
  "lwe_params level = (case level of
     Level1 \<Rightarrow> (512, 512, 3329, 3.2)
   | Level3 \<Rightarrow> (768, 768, 3329, 3.2)
   | Level5 \<Rightarrow> (1024, 1024, 3329, 3.2)
   | _ \<Rightarrow> (512, 512, 3329, 3.2))"
```

### Correctness vs Security Trade-off

```isabelle
(* Decryption failure probability *)
definition decrypt_failure_prob :: "nat \<Rightarrow> int \<Rightarrow> real \<Rightarrow> real" where
  "decrypt_failure_prob n q sigma =
     Pr[e \<leftarrow> sum_of_gaussians n sigma. \<bar>e\<bar> > q div 4]"

(* Security requires small sigma, correctness requires large q/sigma *)
lemma security_correctness_tradeoff:
  "decrypt_failure_prob n q sigma < delta \<longleftrightarrow>
   q > 4 * tail_bound_inverse delta * sigma * sqrt n"
  sorry
```

## Complete Theory Example

```isabelle
theory Lattice_Crypto_Example
  imports Main "HOL-Library.Code_Target_Numeral"
begin

section \<open>Basic Definitions\<close>

type_synonym int_vec = "int list"
type_synonym int_matrix = "int list list"

definition vec_add :: "int_vec \<Rightarrow> int_vec \<Rightarrow> int_vec" where
  "vec_add = map2 (+)"

definition vec_mod :: "int_vec \<Rightarrow> int \<Rightarrow> int_vec" where
  "vec_mod v q = map (\<lambda>x. x mod q) v"

definition mat_vec_mult :: "int_matrix \<Rightarrow> int_vec \<Rightarrow> int_vec" where
  "mat_vec_mult A x = map (\<lambda>row. sum_list (map2 (*) row x)) A"

section \<open>LWE Instance\<close>

record lwe_pk =
  pk_A :: int_matrix
  pk_b :: int_vec
  pk_q :: int

record lwe_sk =
  sk_s :: int_vec

definition lwe_encrypt_bit :: "lwe_pk \<Rightarrow> bool \<Rightarrow> int_vec \<Rightarrow> int_vec \<times> int" where
  "lwe_encrypt_bit pk bit r =
     (let u = vec_mod (mat_vec_mult (transpose (pk_A pk)) r) (pk_q pk);
          v = (sum_list (map2 (*) (pk_b pk) r) +
               (if bit then pk_q pk div 2 else 0)) mod (pk_q pk)
      in (u, v))"

definition lwe_decrypt_bit :: "lwe_sk \<Rightarrow> int \<Rightarrow> int_vec \<times> int \<Rightarrow> bool" where
  "lwe_decrypt_bit sk q ct =
     (let (u, v) = ct;
          d = (v - sum_list (map2 (*) (sk_s sk) u)) mod q
      in d > q div 4 \<and> d < 3 * q div 4)"

section \<open>Correctness\<close>

lemma lwe_correctness:
  assumes "pk_b pk = vec_mod (vec_add (mat_vec_mult (pk_A pk) (sk_s sk)) e) (pk_q pk)"
    and "\<forall>i < length e. \<bar>e ! i\<bar> < pk_q pk div 8"
    and "length r = length (pk_A pk)"
    and "\<forall>i < length r. r ! i \<in> {0, 1}"
  shows "lwe_decrypt_bit sk (pk_q pk) (lwe_encrypt_bit pk bit r) = bit"
  sorry  (* Requires careful analysis of error accumulation *)

end
```
