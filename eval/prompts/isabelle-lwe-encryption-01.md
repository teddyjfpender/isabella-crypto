# Prompt ID: isabelle-lwe-encryption-01

## Task

Create an Isabelle/HOL theory implementing a simplified LWE (Learning With Errors) encryption scheme with Haskell export.

## Requirements

1. Define record types for:
   - `lwe_params`: n (dimension), q (modulus)
   - `lwe_secret_key`: secret vector s
   - `lwe_public_key`: matrix A and vector b = As + e

2. Implement:
   - `encode_bit`: Encode a bit as 0 or q/2
   - `decode_bit`: Decode by checking if value is closer to 0 or q/2
   - `lwe_encrypt`: Given public key (A, b) and bit m, compute (u, v) where u = A^T r and v = b · r + encode(m)
   - `lwe_decrypt`: Given secret key s and ciphertext (u, v), compute decode(v - s · u)

3. State (but don't need to prove) the correctness condition as a lemma

4. Export all functions to Haskell with module name `Lattice.LWE`

## Constraints

- Must compile with `isabelle build`
- Use the vector operations pattern (int list)
- Include `Code_Target_Numeral` for efficient export

## Technical Notes

- For simplicity, r can be a binary vector (0s and 1s)
- Decoding threshold: if |v - q/2| < q/4, output 1; else output 0
- Matrix-vector multiplication: each row dotted with vector

## Deliverable

Only the complete theory file content for a single `.thy` file.
