# Prompt ID: isabelle-vector-ops-01

## Task

Create an Isabelle/HOL theory file that defines basic vector operations for lattice cryptography and exports them to Haskell.

## Requirements

1. Define a type alias for integer vectors (as `int list`)
2. Implement the following operations:
   - `vec_add`: Element-wise addition of two vectors
   - `vec_sub`: Element-wise subtraction
   - `inner_product`: Dot product of two vectors
   - `scalar_mult`: Multiply all elements by a scalar
   - `vec_mod`: Apply modular reduction to all elements

3. Prove at least one basic lemma (e.g., `vec_add` is commutative)

4. Export all functions to Haskell with module name `Lattice.Vector`

## Constraints

- Must compile with `isabelle build`
- Use `Code_Target_Numeral` for efficient integer code generation
- Theory should import `Main` and `"HOL-Library.Code_Target_Numeral"`
- No external dependencies beyond HOL-Library

## Technical Notes

- Use `primrec` or `fun` for recursive definitions
- Use `zip` from List library for pairwise operations
- Integer modulo in Isabelle is `mod` (works with negative numbers)

## Deliverable

Only the complete theory file content for a single `.thy` file.
