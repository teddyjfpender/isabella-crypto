# Rubric for isabelle-sis-normal-form-01

## Pass Criteria

The submission passes if ALL of the following are true:

1. **Compiles**: The theory file compiles with `isabelle build` without errors
2. **Type Definitions**: Defines types for vectors and matrices (e.g., `type_synonym int_vec = "int list"`)
3. **Record Types**: Defines record types for SIS instances (at minimum: matrix and target vector fields)
4. **Core Vector/Matrix Operations**: Implements at least:
   - Vector addition (`vec_add` or equivalent)
   - Vector mod reduction (`vec_mod` or equivalent)
   - Matrix-vector multiplication (`mat_vec_mult` or equivalent)
   - Identity matrix construction or inline equivalent
5. **Solution Predicates**: Defines predicates for both SIS and nfSIS solutions
6. **Reduction Functions**: Implements both reduction directions:
   - `nfsis_to_sis` or equivalent (Direction A: transform nfSIS instance to SIS)
   - `sis_to_nfsis` or equivalent (Direction B: transform SIS instance to nfSIS)
7. **Correctness Lemma**: At least one correctness lemma is stated (proof may use `sorry` if complex)
8. **Code Export**: Contains `export_code` directive with Haskell target and `Lattice.SIS_Normal_Form` or similar module name

## Fail Criteria

The submission fails if ANY of the following are true:

- Theory file has syntax errors
- Missing required imports (`Main`, `Code_Target_Numeral`)
- No SIS-related type definitions
- Both reduction directions are missing
- No solution predicate is defined
- No `export_code` statement
- Code generation fails completely

## Scoring Rubric

### Core Implementation (60 points)

| Component | Points | Criteria |
|-----------|--------|----------|
| Type definitions | 10 | Vector and matrix types defined |
| Record types | 10 | SIS and nfSIS instance records present |
| Vector operations | 10 | vec_add, vec_mod, mat_vec_mult defined and correct |
| Matrix operations | 10 | Identity matrix, concatenation, or splitting defined |
| Solution predicates | 10 | Both is_sis_solution and is_nf_sis_solution defined |
| Reduction functions | 10 | Both nfsis_to_sis and sis_to_nfsis implemented |

### Correctness Proofs (25 points)

| Component | Points | Criteria |
|-----------|--------|----------|
| Lemma statements | 5 | At least 2 correctness lemmas stated |
| Direction A proof | 10 | Proof complete (or partial with clear sorry) |
| Direction B proof | 10 | Proof complete (or partial with clear sorry) |

### Code Export (15 points)

| Component | Points | Criteria |
|-----------|--------|----------|
| Haskell export | 5 | `export_code ... in Haskell` present and works |
| Module name | 5 | Appropriate module name (SIS-related) |
| Multi-language | 5 | Bonus: SML, OCaml, or Scala export also works |

## Partial Credit Notes

- **Sorry usage**: Using `sorry` for matrix inversion internals is acceptable; using it for the main reduction correctness is partial credit
- **Naming flexibility**: Different function names are acceptable (e.g., `systematic_to_general` vs `nfsis_to_sis`)
- **Matrix inversion**: The inverse computation may be underspecified or use assumptions; the key is the reduction structure
- **Extra content**: Additional helper lemmas, examples, or documentation are welcome
- **Simplified model**: Using lists instead of more sophisticated matrix representations is fine

## Bonus Points

- Complete proofs without any `sorry` (+10)
- Both reduction directions fully proved with algebraic steps shown (+5)
- Example instantiation with concrete parameters that demonstrates the reduction (+5)
- Property lemmas about vector/matrix operations (associativity, etc.) (+5)
