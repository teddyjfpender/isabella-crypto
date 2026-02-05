# LaZer Formalization Gaps (Repo Sweep)

Date: 2026-02-05
Branch context: `codex/feat/LaZer`

## Scope

This document captures what is still required to realize the stated goal:

1. Formal Isabelle theories as source-of-truth.
2. Code generation to Haskell/OCaml.
3. Deterministic comparison against LaZer for overlapping ring/module operations.

## Baseline Verified in This Sweep

- `Canon` session currently builds locally (`isabelle build -D Canon`).
- No remaining `sorry` placeholders in `Canon/**/*.thy`.
- Test harness now includes optional deterministic LaZer comparison suite:
  - `tests/scripts/lazer_adapter.py`
  - `tests/src/lazer-comparison.test.ts`
  - `tests/package.json` script `test:lazer`
- `npm test` passes with LaZer tests skip-safe when bindings are unavailable.

## Remaining Gaps (Prioritized)

### P0: Trust Boundary Between Spec and Implementation

Problem:
- `Canon/Rings/Rq_AFP_Bridge.thy` proves clean polynomial-mod lemmas at the spec layer.
- Core executable list-based operations still rely on implementation lemmas and assumptions.
- There is no end-to-end refinement theorem connecting spec semantics to exported implementation semantics.

Required:
- Add refinement lemmas showing list-level `ring_mod` / `ring_mult` are extensionally equal to the polynomial quotient-ring spec on bounded inputs.
- Replace assumption-heavy algebraic downstream proofs with proved consequences from that refinement.

Acceptance:
- A theorem chain from spec lemmas to executable `ring_mult`-level statements, with no additional algebraic axioms in downstream theories.

### P0: Sigma Protocol Semantics Still Structural

Problem:
- `Canon/ZK/Sigma_Base.thy` has structural completeness, but extractor/simulator definitions are placeholders (`Some z_diff`, simplified simulator).
- This is enough for scaffolding but not enough for LaZer-grade extraction/HVZK claims.

Required:
- Define and prove the actual extractor semantics (with explicit invertibility preconditions).
- Strengthen HVZK statements beyond structural verifier acceptance.
- Add precise statement of what is and is not guaranteed by each theorem.

Acceptance:
- Soundness/extraction theorem with explicit preconditions.
- HVZK theorem tied to simulator distribution assumptions.

### P0: Generation Pipeline Needs a Verifiable Path

Problem:
- `generate.sh` still contains fallback stub generation logic.
- This weakens confidence that produced Haskell/OCaml artifacts are exclusively from Isabelle `export_code`.

Required:
- Remove/disable non-verified fallback stubs for production generation path.
- Enforce fail-fast when expected export artifacts are missing.
- Document exactly which Isabelle constants are exported per language.

Acceptance:
- `./generate.sh` either produces exported code from Isabelle or fails.
- No synthetic fallback modules in the production path.

### P1: LaZer Comparison Coverage Is Narrow

Problem:
- Current harness validates deterministic ring multiplication and matrix-vector multiplication only.

Required:
- Expand fixture schema and tests to cover:
  - challenge-weight/ternary constraints where overlap exists,
  - module-scale identities used by Sigma/ModuleLWE,
  - edge-case coefficient ranges near reduction boundaries.

Acceptance:
- Deterministic regression set exercising all operations consumed by the near-term LaZer-facing interfaces.

### P1: CI Integration for LaZer Checks

Problem:
- LaZer suite is intentionally optional and currently skip-safe in CI.

Required:
- Add a dedicated optional CI job that runs when LaZer bindings are available (self-hosted or prebuilt image).
- Keep default public CI deterministic and non-flaky.

Acceptance:
- One CI path that actually executes `test:lazer` with real LaZer bindings.

## Recommended Next Sequence

1. Prove spec/impl refinement in `Canon/Rings` and remove downstream multiplication axioms.
2. Harden `Sigma_Base` extractor/simulator semantics with explicit assumptions.
3. Make `generate.sh` fail-fast and export-only.
4. Extend LaZer deterministic fixtures and enable optional CI execution path.
