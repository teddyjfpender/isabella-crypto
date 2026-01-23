# Evaluation Harness Rationale

## Purpose

This harness evaluates the effectiveness of Isabelle/HOL skills for lattice cryptography code generation. It measures whether an agent, given appropriate skills and prompts, can produce:

1. **Valid Isabelle theories** that compile without errors
2. **Correct formalizations** that capture the intended mathematical concepts
3. **Exportable code** that generates working Haskell implementations

## Design Principles

### Deterministic Verification

Unlike subjective code review, our verification is objective:
- **Compiles or doesn't**: `isabelle build` returns 0 or non-zero
- **Exports or doesn't**: Haskell files are generated or not
- **Proofs complete or don't**: Isabelle rejects incomplete proofs

### Isolated Environments

Each evaluation runs in its own work directory with:
- Fresh Isabelle project structure
- No cross-contamination between runs
- Reproducible from prompt + skill combination

### Structured Output

All outputs are machine-readable:
- `run.json`: Execution metadata
- `verify.json`: Verification results
- `steps.jsonl`: Step-by-step log

## Verification Pipeline

```
┌─────────────────────────────────────────────────────────────┐
│                         PIPELINE                             │
├─────────────────────────────────────────────────────────────┤
│                                                              │
│  ┌──────────┐   ┌──────────┐   ┌──────────┐   ┌──────────┐  │
│  │ Scaffold │ → │  Prompt  │ → │  Agent   │ → │ Extract  │  │
│  │ Project  │   │  Build   │   │  Run     │   │  Code    │  │
│  └──────────┘   └──────────┘   └──────────┘   └──────────┘  │
│                                                     │        │
│                                                     ▼        │
│  ┌──────────┐   ┌──────────┐   ┌──────────┐   ┌──────────┐  │
│  │ Collect  │ ← │  Export  │ ← │  Build   │ ← │  Check   │  │
│  │ Haskell  │   │  Code    │   │  Proofs  │   │  Syntax  │  │
│  └──────────┘   └──────────┘   └──────────┘   └──────────┘  │
│                                                              │
└─────────────────────────────────────────────────────────────┘
```

## Metrics

### Primary Metrics

- **Compile Rate**: % of generated theories that compile
- **Export Rate**: % that successfully export to Haskell
- **Full Pass Rate**: % that pass all verification steps

### Secondary Metrics

- **Build Time**: How long Isabelle takes to verify
- **Proof Completeness**: Whether all lemmas are proved (vs. `sorry`)
- **Code Quality**: Generated Haskell compiles and type-checks

## Skill Effectiveness

Compare runs with and without skills:

```bash
# Baseline (no skills)
./run-prompt.sh --prompt isabelle-lwe-01 --disable-skills

# With relevant skill
./run-prompt.sh --prompt isabelle-lwe-01 --skill isabelle-lattice-crypto
```

A skill is effective if it increases pass rates on relevant prompts.

## Future Directions

1. **Property Testing**: Use QuickCheck on generated Haskell
2. **Proof Obligations**: Track `sorry` usage and proof completeness
3. **Performance Benchmarks**: Compare generated code efficiency
4. **Cross-validation**: Test generated code against reference implementations
