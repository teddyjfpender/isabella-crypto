# Rubric for isabelle-lwe-short-secret-01

## Pass Criteria

The submission passes if ALL of the following are true:

1. **Compiles**: The theory file compiles with `isabelle build` without errors
2. **Type Definitions**: Defines types for vectors and matrices (e.g., `type_synonym int_vec = "int list"`)
3. **Record Types**: Defines record types for LWE instances and secrets
4. **Core Operations**: Implements at least:
   - Vector addition (`vec_add` or equivalent)
   - Vector subtraction (`vec_sub` or equivalent)
   - Vector-matrix multiplication (`vec_mat_mult` or equivalent)
   - Vector splitting (`split_vec` or equivalent)
5. **Reduction 1 Functions**: Implements the ssLWE → LWE reduction:
   - Instance transformation function
   - Secret transformation function
   - Recovery function
6. **Reduction 2 Functions**: Implements the LWE → ssLWE reduction:
   - Instance transformation function (may use `sorry` for matrix inversion details)
   - Secret transformation function
7. **Correctness Lemma**: At least one correctness lemma is stated for Reduction 1
8. **Code Export**: Contains `export_code` directive with Haskell target and appropriate module name

## Fail Criteria

The submission fails if ANY of the following are true:

- Theory file has syntax errors
- Missing required imports (`Main`, `Code_Target_Numeral`)
- No LWE-related type definitions
- Neither reduction is implemented
- No vector/matrix operations defined
- No `export_code` statement
- Code generation fails completely

## Scoring Rubric

### Core Implementation (60 points)

| Component | Points | Criteria |
|-----------|--------|----------|
| Type definitions | 8 | Vector and matrix types defined |
| Record types | 8 | LWE instance and secret records present |
| Vector operations | 12 | vec_add, vec_sub, vec_mod, inner_prod defined |
| Matrix operations | 12 | vec_mat_mult, mat_mat_mult, split operations defined |
| Reduction 1 functions | 10 | sslwe_to_lwe, secret transforms implemented |
| Reduction 2 functions | 10 | lwe_to_sslwe, secret transform implemented |

### Correctness Proofs (25 points)

| Component | Points | Criteria |
|-----------|--------|----------|
| Reduction 1 lemma statement | 5 | Correctness lemma for ssLWE → LWE stated |
| Reduction 1 proof | 10 | Proof complete (key algebraic steps shown) |
| Reduction 2 lemma | 5 | Correctness lemma for LWE → ssLWE stated |
| Reduction 2 proof | 5 | Partial proof or justified sorry |

### Code Export (15 points)

| Component | Points | Criteria |
|-----------|--------|----------|
| Haskell export | 5 | `export_code ... in Haskell` present and works |
| Module name | 5 | Appropriate module name (LWE_Short_Secret or similar) |
| Multi-language | 5 | Bonus: SML, OCaml, or Scala export also works |

## Partial Credit Notes

- **Reduction 2 complexity**: Using `sorry` for matrix inversion and the full algebraic derivation in Reduction 2 is acceptable; the key is correct structure
- **Reduction 1 priority**: Reduction 1 is simpler and should have a complete proof; Reduction 2 proofs are bonus
- **Naming flexibility**: Different function names are acceptable as long as the intent is clear
- **Distribution handling**: The "shortness" predicate may be abstract or simplified
- **Row vs column vectors**: Either convention is acceptable if consistent

## Bonus Points

- Complete proofs for both reductions without any `sorry` (+10)
- Algebraic derivation showing z₀ = (-e₁)^T·A_ss + e₀ step by step (+5)
- Example instantiation demonstrating both reductions (+5)
- Parameter relationship lemma (m+n samples → m samples) proved (+5)
- Distribution lemmas (s+r uniform when r uniform) stated (+3)

## Key Mathematical Checkpoints

The grader should verify these key mathematical relationships are captured:

### Reduction 1 (ssLWE → LWE)
- [ ] y' = y + r^T·A formula present
- [ ] s' = s + r relationship captured
- [ ] Error e unchanged in transformation
- [ ] Recovery s = s' - r implemented

### Reduction 2 (LWE → ssLWE)
- [ ] Matrix split A = [A₀|B] structure used
- [ ] Noisy secret estimate s̃ = y₁·B⁻¹ computed
- [ ] Output z₀ = y₀ - s̃·A₀ formula present
- [ ] New secret is -e₁ (the error portion)
- [ ] New error is e₀ (the first error portion)
- [ ] Sample count requirement (m+n → m) documented
