# Prompt ID: isabelle-polynomial-ring-01

## Task

Create an Isabelle/HOL theory that implements polynomial arithmetic in the ring Z_q[X]/(X^n + 1), which is fundamental for Ring-LWE cryptography.

## Requirements

1. Represent polynomials as coefficient lists (`int list`)
2. Implement:
   - `poly_add`: Add two polynomials
   - `poly_mult`: Naive polynomial multiplication
   - `poly_mod_cyclotomic`: Reduce modulo (X^n + 1)
   - `ring_mult`: Full multiplication in Z_q[X]/(X^n + 1) (multiply then reduce)
   - `coeff_mod`: Apply coefficient modulo q

3. Prove that `poly_add` is associative or commutative

4. Export to Haskell with module name `Lattice.Polynomial`

## Constraints

- Must compile with `isabelle build`
- Use efficient definitions suitable for code generation
- Handle edge cases (empty lists, different length polynomials)

## Technical Notes

- For (X^n + 1) reduction: if degree >= n, subtract coefficient at position i from position (i - n)
- Polynomial multiplication: convolve coefficient lists
- Remember: in Z_q[X]/(X^n + 1), X^n = -1

## Deliverable

Only the complete theory file content for a single `.thy` file.
