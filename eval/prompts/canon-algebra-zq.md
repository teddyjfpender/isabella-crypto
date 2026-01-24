# Prompt ID: canon-algebra-zq

## Task

Create the Canon/Algebra/Zq.thy theory file - modular arithmetic and decoding infrastructure.

This theory provides the Z_q abstraction and the critical `dist0`/`decode_bit` machinery used in all LWE-based schemes.

## Note on Theory Structure

The step-loop provides the theory header automatically. Your steps output content for inside `begin...end`.

Note: For the final theory, imports will need adjustment to `"../Prelude" "../Linear/ListVec"`.

## Steps

### Step 1: Centered Modular Reduction

Define centered mod that maps to (-q/2, q/2]:

```isabelle
definition mod_centered :: "int ⇒ int ⇒ int" where
  "mod_centered x q = (let r = x mod q in if r > q div 2 then r - q else r)"
```

Prove properties:
1. `mod_centered_range`: `q > 0 ⟹ -(q div 2) ≤ mod_centered x q ∧ mod_centered x q ≤ q div 2`
2. `mod_centered_cong`: `mod_centered x q mod q = x mod q`
3. `mod_centered_zero`: `mod_centered 0 q = 0`

### Step 2: Vector Modular Operations

Define componentwise mod:

```isabelle
definition vec_mod :: "int_vec ⇒ int ⇒ int_vec" where
  "vec_mod v q = map (λx. x mod q) v"

definition vec_mod_centered :: "int_vec ⇒ int ⇒ int_vec" where
  "vec_mod_centered v q = map (λx. mod_centered x q) v"
```

Prove and declare [dim_simp]:
1. `vec_mod_length`: `length (vec_mod v q) = length v`
2. `vec_mod_centered_length`: `length (vec_mod_centered v q) = length v`

Prove [mod_simp]:
1. `vec_mod_idemp`: `vec_mod (vec_mod v q) q = vec_mod v q`
2. `vec_mod_add`: `vec_mod (vec_add u v) q = vec_mod (vec_add (vec_mod u q) (vec_mod v q)) q`

### Step 3: Distance from Zero in Z_q

**Critical for decryption correctness.**

Define `dist0` - the distance from 0 in the cyclic group Z_q:

```isabelle
definition dist0 :: "int ⇒ int ⇒ int" where
  "dist0 q x = (let x' = x mod q in min x' (q - x'))"
```

Alternative definition using centered:
```isabelle
definition dist0 :: "int ⇒ int ⇒ int" where
  "dist0 q x = |mod_centered x q|"
```

Prove [dist_simp]:
1. `dist0_nonneg`: `q > 0 ⟹ dist0 q x ≥ 0`
2. `dist0_bound`: `q > 0 ⟹ dist0 q x ≤ q div 2`
3. `dist0_zero`: `dist0 q 0 = 0`
4. `dist0_mod`: `dist0 q (x mod q) = dist0 q x`

### Step 4: Key Distance Lemmas for Decoding

These lemmas are essential for proving decryption correctness:

```isabelle
lemma dist0_small:
  assumes "q > 0" "|x| < q div 4"
  shows "dist0 q x = |x|"
```

```isabelle
lemma dist0_half_shift:
  assumes "q > 0" "q mod 4 = 0" "|x| < q div 4"
  shows "dist0 q (x + q div 2) = q div 2 - |x|"
```

The first says: small values stay small.
The second says: values near q/2 have distance close to q/2.

### Step 5: Bit Encoding and Decoding

Define the standard LWE bit encoding:

```isabelle
definition encode_bit :: "int ⇒ bool ⇒ int" where
  "encode_bit q b = (if b then q div 2 else 0)"

definition decode_bit :: "int ⇒ int ⇒ bool" where
  "decode_bit q x = (dist0 q x > q div 4)"
```

Interpretation:
- False (0) encodes to 0
- True (1) encodes to q/2
- Decoding: closer to 0 → False, closer to q/2 → True

### Step 6: Encoding/Decoding Correctness

Prove the round-trip property:

```isabelle
lemma encode_decode_inverse:
  assumes "q > 2"
  shows "decode_bit q (encode_bit q b) = b"
```

Proof: case split on b, use dist0_zero and dist0_half_shift.

### Step 7: Noisy Decoding Lemmas

Prove that decoding tolerates noise:

```isabelle
lemma decode_bit_small:
  assumes "q > 0" "q mod 4 = 0" "|x| < q div 4"
  shows "decode_bit q x = False"
```

```isabelle
lemma decode_bit_half_shift:
  assumes "q > 0" "q mod 4 = 0" "|x| < q div 4"
  shows "decode_bit q (x + q div 2) = True"
```

These say: if noise |x| < q/4, then:
- decode(0 + noise) = False
- decode(q/2 + noise) = True

### Step 8: Modular Inner Product Congruence

Prove that inner products respect mod:

```isabelle
lemma inner_prod_mod_cong:
  assumes "q > 0" "length v = length w"
  shows "inner_prod v w mod q = inner_prod (vec_mod v q) (vec_mod w q) mod q"
```

```isabelle
lemma inner_prod_mod_cong_right:
  assumes "q > 0" "length v = length w"
  shows "inner_prod v w mod q = inner_prod v (vec_mod w q) mod q"
```

### Step 9: Matrix-Vector Mod Operations

```isabelle
definition mat_vec_mult_mod :: "int_matrix ⇒ int_vec ⇒ int ⇒ int_vec" where
  "mat_vec_mult_mod A v q = vec_mod (mat_vec_mult A v) q"
```

Prove:
1. `mat_vec_mult_mod_length`: `length (mat_vec_mult_mod A v q) = length A`

### Step 10: Code Export

```isabelle
export_code
  mod_centered vec_mod vec_mod_centered
  dist0 encode_bit decode_bit
  mat_vec_mult_mod
  in Haskell module_name "Canon.Algebra.Zq"
```

## Constraints

- Theory name: `Zq`
- Imports Prelude and ListVec
- No sorry/oops
- dist0 and decode_bit lemmas are critical - must be proven completely
- All mod lemmas declared [mod_simp]
- All dist lemmas declared [dist_simp]

## Proof Hints

1. `dist0_small`: Split on sign of x, use mod properties
2. `dist0_half_shift`: The `q mod 4 = 0` assumption is key - it ensures q/2 is even
3. `encode_decode_inverse`: Direct case split, then arithmetic
4. For mod congruence lemmas, use induction on list length
5. Use `mod_add_eq` and `mod_mult_eq` from Number_Theory

## Mathematical Background

In LWE, we encode bits as:
- 0 → 0
- 1 → ⌊q/2⌋

Decryption computes d = v - ⟨s, u⟩ ≈ ⟨e, r⟩ + encode(m)

If the noise |⟨e,r⟩| < q/4, then:
- m = 0: d ≈ 0, distance from 0 is small → decode to 0
- m = 1: d ≈ q/2, distance from 0 is ≈ q/2 → decode to 1

## Deliverable

A working Zq.thy that:
1. Compiles with Canon_Base session
2. Provides dist0/decode_bit with complete proofs
3. Has the critical `dist0_small` and `dist0_half_shift` lemmas
4. Exports to Haskell
