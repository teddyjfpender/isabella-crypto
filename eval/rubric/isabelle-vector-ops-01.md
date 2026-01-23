# Rubric for isabelle-vector-ops-01

## Pass Criteria

The submission passes if ALL of the following are true:

1. **Compiles**: The theory file compiles with `isabelle build` without errors
2. **Type Alias**: Defines a type for integer vectors (e.g., `type_synonym intvec = "int list"`)
3. **Operations Defined**: All five operations are defined:
   - `vec_add`
   - `vec_sub`
   - `inner_product`
   - `scalar_mult`
   - `vec_mod`
4. **Lemma Present**: At least one lemma is stated and proved
5. **Code Export**: Contains `export_code` directive with Haskell target
6. **Module Name**: Haskell module name is `Lattice.Vector` or similar

## Fail Criteria

The submission fails if ANY of the following are true:

- Theory file has syntax errors
- Missing required imports (`Main`, `Code_Target_Numeral`)
- Any of the five operations is missing
- No lemma is present
- No `export_code` statement
- Code generation fails

## Partial Credit Notes

- Minor naming differences are acceptable (e.g., `vector_add` vs `vec_add`)
- Additional helper functions are acceptable
- Additional lemmas beyond the minimum are good
- Using `definition` vs `fun` vs `primrec` is acceptable as long as it compiles
