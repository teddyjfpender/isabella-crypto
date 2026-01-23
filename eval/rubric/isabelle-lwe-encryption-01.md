# Rubric for isabelle-lwe-encryption-01

## Pass Criteria

The submission passes if ALL of the following are true:

1. **Compiles**: The theory file compiles with `isabelle build` without errors
2. **Record Types**: Defines record types for params, secret key, and public key
3. **Encoding Functions**: `encode_bit` and `decode_bit` are defined
4. **Encryption**: `lwe_encrypt` takes public key, randomness, and message bit
5. **Decryption**: `lwe_decrypt` takes secret key and ciphertext
6. **Correctness Statement**: A lemma stating correctness conditions is present (proof optional)
7. **Code Export**: Contains `export_code` with Haskell target and `Lattice.LWE` module

## Fail Criteria

The submission fails if ANY of the following are true:

- Theory file has syntax errors
- Missing encryption or decryption function
- Encoding/decoding logic is fundamentally wrong
- No code export directive
- Missing record type definitions

## Partial Credit Notes

- Proving the correctness lemma is bonus (stating it is sufficient)
- Different approaches to the threshold in decoding are acceptable
- Using centered modular arithmetic vs standard is a design choice
- Additional utility functions (key generation, etc.) are welcome
- Simplifications (e.g., fixed parameters) are acceptable for this exercise
