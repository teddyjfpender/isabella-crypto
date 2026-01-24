# Prompt ID: isabelle-lwe-regev-01

## Task

Create an Isabelle/HOL theory implementing Regev's LWE (Learning With Errors) public-key encryption scheme with complete proofs and Haskell code export.

## Web References

For additional context on the algorithms, you may fetch these URLs:

| Topic | URL |
|-------|-----|
| Simple LWE PKE Explanation | https://di-mgt.com.au/lattice-lwe-simple-pke.html |
| Regev's LWE Survey | https://cims.nyu.edu/~regev/papers/lwesurvey.pdf |
| Isabelle Code Generation | https://isabelle.in.tum.de/doc/codegen.pdf |
| HOL-Library Reference | https://isabelle.in.tum.de/library/HOL/HOL-Library/index.html |

## Background: Regev's LWE Encryption Scheme

Regev's scheme is a foundational lattice-based public-key encryption system secure under the LWE assumption.

### Parameters

- **n**: Security parameter (secret vector dimension)
- **q**: Modulus (prime, typically polynomial in n)
- **N**: Number of LWE samples (rows of matrix A, typically N ≥ (n+1) log q)
- **χ**: Error distribution over ℤ (typically discrete Gaussian with small standard deviation σ)

### Key Generation (KeyGen)

1. Sample secret vector: **s** ← ℤ_q^n uniformly at random
2. Sample public matrix: **A** ← ℤ_q^(N×n) uniformly at random
3. Sample error vector: **e** ← χ^N (each component from error distribution)
4. Compute: **b** = A·s + e (mod q)
5. Output: public key **pk** = (A, b), secret key **sk** = s

### Encryption (Encrypt)

To encrypt a single bit m ∈ {0, 1}:

1. Sample random binary vector: **r** ← {0,1}^N
2. Compute: **u** = A^T · r (mod q) — an n-dimensional vector
3. Compute: **v** = b^T · r + ⌊q/2⌋ · m (mod q) — a scalar
4. Output: ciphertext **ct** = (u, v)

### Decryption (Decrypt)

To decrypt ciphertext (u, v):

1. Compute: **d** = v - s^T · u (mod q)
2. Output: m = ⌈2d/q⌉ mod 2

Equivalently: if d is closer to 0 than to q/2, output 0; otherwise output 1.

### Correctness Analysis

The decryption recovers m because:
- d = v - s^T · u
- d = (b^T · r + ⌊q/2⌋ · m) - s^T · (A^T · r)
- d = (A·s + e)^T · r + ⌊q/2⌋ · m - s^T · A^T · r
- d = s^T · A^T · r + e^T · r + ⌊q/2⌋ · m - s^T · A^T · r
- d = e^T · r + ⌊q/2⌋ · m

**Correctness condition**: Decryption succeeds when |e^T · r| < ⌊q/4⌋

Since r ∈ {0,1}^N and e has small entries from χ, the error term e^T · r (a sum of at most N small error values) remains small with high probability.

## Requirements

### 1. Type Definitions

Define the following Isabelle types:

```
type_synonym int_vec = "int list"
type_synonym int_matrix = "int list list"
```

Define record types:
- `lwe_params`: n (dimension), q (modulus), num_samples (N)
- `lwe_public_key`: matrix A and vector b
- `lwe_secret_key`: secret vector s
- `lwe_ciphertext`: vector u and scalar v

### 2. Helper Functions

Implement with complete proofs:

- `vec_add :: int_vec ⇒ int_vec ⇒ int_vec` — component-wise addition
- `vec_mod :: int_vec ⇒ int ⇒ int_vec` — component-wise modular reduction
- `inner_prod :: int_vec ⇒ int_vec ⇒ int` — inner product (dot product)
- `mat_vec_mult :: int_matrix ⇒ int_vec ⇒ int_vec` — matrix-vector multiplication
- `transpose :: int_matrix ⇒ int_matrix` — matrix transpose
- `mat_transpose_vec_mult :: int_matrix ⇒ int_vec ⇒ int_vec` — A^T · v

### 3. Encryption Functions

Implement:

- `encode_bit :: int ⇒ bool ⇒ int` — encode bit: 0 ↦ 0, 1 ↦ ⌊q/2⌋
- `decode_bit :: int ⇒ int ⇒ bool` — decode by threshold: closer to 0 → False, closer to q/2 → True
- `lwe_encrypt :: lwe_public_key ⇒ int ⇒ int_vec ⇒ bool ⇒ lwe_ciphertext`
  - Takes pk, modulus q, random vector r, and bit m
  - Computes u = A^T · r (mod q) and v = b^T · r + encode(m) (mod q)
- `lwe_decrypt :: lwe_secret_key ⇒ int ⇒ lwe_ciphertext ⇒ bool`
  - Computes d = v - s · u (mod q)
  - Returns decode_bit q d

### 4. Correctness Lemmas

State and prove:

1. **encode_decode_inverse**: For valid q > 2:
   ```
   decode_bit q (encode_bit q b) = b
   ```

2. **decryption_error_term**: Show that decryption computes:
   ```
   d = e^T · r + encode_bit q m (mod q)
   ```
   where b = A·s + e

3. **correctness_condition** (may use sorry if complex):
   ```
   |e^T · r| < q div 4 ⟹ lwe_decrypt sk q (lwe_encrypt pk q r m) = m
   ```

### 5. Code Export

Export all functions to Haskell:
```
export_code
  vec_add vec_mod inner_prod
  mat_vec_mult transpose mat_transpose_vec_mult
  encode_bit decode_bit
  lwe_encrypt lwe_decrypt
  in Haskell module_name "Lattice.LWE_Regev"
```

## Constraints

- **Theory name**: Must be `LatticeCrypto` (to match session configuration)
- **Imports**: `Main` and `HOL-Library.Code_Target_Numeral`
- **No sorry**: All lemmas must have complete proofs (except the main correctness theorem if it requires probabilistic reasoning)
- **Modular arithmetic**: Use `mod` for all arithmetic to stay in ℤ_q

## Proof Hints

1. For `encode_decode_inverse`:
   - Use `unfolding encode_bit_def decode_bit_def`
   - Consider cases: b = True, b = False
   - Use arithmetic facts about q/2 and q/4

2. For vector operation lemmas:
   - Use `by (auto simp: vec_add_def)` patterns
   - Induction on list length for recursive properties

3. For transpose properties:
   - May need auxiliary lemmas about list indexing
   - `nth_map` and `length_map` are useful

## Example Parameter Instantiation

For testing, use toy parameters:
- n = 4 (dimension)
- q = 97 (prime modulus)
- N = 8 (samples)
- Error bound: σ ≤ 3 (so entries of e satisfy |e_i| ≤ 3·σ ≈ 9)

With these parameters and r ∈ {0,1}^8:
- |e^T · r| ≤ 8 · 9 = 72 < 97/4 ≈ 24? No, need larger q!
- Better: q = 401, then q/4 ≈ 100 > 72 ✓

## Deliverable

A complete Isabelle theory file that:
1. Compiles with `isabelle build -d . LatticeCrypto`
2. Contains NO `sorry` (except optionally for the probabilistic correctness bound)
3. Exports working Haskell code
4. Demonstrates the LWE encryption scheme structure

## Mathematical Reference

For bit m ∈ {0,1}, the scheme encrypts as:

```
Encryption(pk = (A, b), m):
  r ← {0,1}^N
  u ← A^T r (mod q)
  v ← ⟨b, r⟩ + ⌊q/2⌋ · m (mod q)
  return (u, v)

Decryption(sk = s, ct = (u, v)):
  d ← v - ⟨s, u⟩ (mod q)
  if d ∈ [−q/4, q/4) then return 0
  else return 1
```

The decryption threshold uses the fact that:
- If m = 0: d ≈ e^T r ≈ 0 (small noise)
- If m = 1: d ≈ e^T r + q/2 ≈ q/2 (biased toward q/2)
