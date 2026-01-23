# Rubric for isabelle-polynomial-ring-01

## Pass Criteria

The submission passes if ALL of the following are true:

1. **Compiles**: The theory file compiles with `isabelle build` without errors
2. **Polynomial Representation**: Uses `int list` or similar for polynomials
3. **Operations Defined**: All required operations present:
   - `poly_add` - polynomial addition
   - `poly_mult` - polynomial multiplication (naive or otherwise)
   - `poly_mod_cyclotomic` - reduction modulo X^n + 1
   - `ring_mult` - combined multiply and reduce
   - `coeff_mod` - coefficient-wise modular reduction
4. **Lemma Present**: At least one algebraic property is stated and proved
5. **Code Export**: Contains `export_code` with Haskell target
6. **Module Name**: Uses `Lattice.Polynomial` or similar naming

## Fail Criteria

The submission fails if ANY of the following are true:

- Theory file has syntax errors or doesn't compile
- Polynomial operations are fundamentally incorrect (e.g., wrong addition logic)
- Missing cyclotomic reduction (this is the key operation for RLWE)
- No code export directive
- Code generation fails

## Partial Credit Notes

- Using FFT/NTT for multiplication instead of naive is acceptable (and better)
- Different proof strategies are acceptable
- Helper functions are encouraged
- Handling of edge cases (empty polynomials) may vary
