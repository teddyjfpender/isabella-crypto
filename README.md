# Isabella

**Isab**elle + Latt**ice** Cryptography = **Isabella**

Formally verified lattice-based cryptography in Isabelle/HOL with executable Haskell code generation.

## Overview

This repository contains:

- **Isabelle Theories**: Formal proofs and definitions for lattice-based cryptography
- **Haskell Library**: Generated and hand-written Haskell code for lattice crypto primitives
- **Skills**: Agent skills for writing Isabelle theories
- **Evaluation Harness**: Scripts for testing and validating Isabelle code generation
- **Ralph Loop**: Iterative orchestrator for generating valid proofs

## Prerequisites

- [Isabelle](https://isabelle.in.tum.de/) (2024 or later)
- [GHC](https://www.haskell.org/ghc/) and [Cabal](https://www.haskell.org/cabal/)
- Python 3.8+
- AI CLI tool:
  - [OpenAI Codex CLI](https://github.com/openai/codex) (default)
  - Or [Claude Code CLI](https://github.com/anthropics/claude-code)

### Installing Isabelle (macOS)

```bash
brew install --cask isabelle
```

Or download from https://isabelle.in.tum.de/installation.html

### Installing Codex CLI

```bash
npm install -g @openai/codex
```

## Project Structure

```
isabella-crypto/
├── isabelle/               # Isabelle theories
│   ├── ROOT               # Session configuration
│   └── theories/          # Theory files
│       ├── Lattice_Basics.thy
│       ├── Polynomial_Ring.thy
│       └── LWE.thy
├── haskell/               # Haskell library
│   ├── cabal.project
│   └── lattice-crypto/
│       ├── lattice-crypto.cabal
│       └── src/
├── skills/                # Agent skills for Isabelle
│   ├── isabelle-basics/
│   ├── isabelle-proofs/
│   ├── isabelle-code-generation/
│   ├── isabelle-lattice-crypto/
│   └── ...
├── eval/                  # Evaluation harness
│   ├── run-prompt.sh      # Single-shot runner
│   ├── verify.sh          # Isabelle verification
│   ├── scaffold.sh        # Project scaffolding
│   ├── debug.sh           # Debugging workflow
│   └── prompts/           # Test prompts
├── ralph/                 # Ralph loop orchestrator
│   ├── isabella-loop.sh   # Main iterative runner
│   ├── ralph-work.yaml    # Work phase config
│   └── ralph-review.yaml  # Review phase config
└── dist/                  # Packaged skills
```

## Quick Start

### Building Isabelle Theories

```bash
cd isabelle
isabelle build -d . -v LatticeCrypto
```

### Exporting Haskell Code

```bash
cd isabelle
isabelle build -e -d . LatticeCrypto
```

Generated Haskell files will be in `haskell/lattice-crypto/src/Generated/`.

### Building Haskell Library

```bash
cd haskell
cabal build all
```

## Ralph Loop (Recommended)

The Ralph Loop is an iterative orchestrator that generates Isabelle theories with **complete proofs**. It runs multiple iterations, feeding Isabelle error messages back to the AI until the proofs compile.

### Running with Ralph Loop

```bash
ralph/isabella-loop.sh \
    --prompt isabelle-lwe-encryption-01 \
    --skill isabelle-basics \
    --skill isabelle-proofs \
    --skill isabelle-datatypes \
    --skill isabelle-code-generation \
    --skill isabelle-lattice-crypto \
    --iterations 5
```

### How It Works

1. **Work Phase**: AI generates an Isabelle theory
2. **Review Phase**: Isabelle builds the theory (strict mode, no `sorry`)
3. **Feedback Loop**: If build fails, errors are fed back to AI for next iteration
4. **Success**: Loop exits when proofs compile, then exports Haskell code

### Options

| Option | Description | Default |
|--------|-------------|---------|
| `--prompt` | Prompt ID from `eval/prompts/` | (required) |
| `--skill` | Skill to include (repeatable) | - |
| `--iterations` | Max iterations | 5 |
| `--provider` | AI provider (openai, anthropic) | openai |
| `--model` | Model for work phase | gpt-5.2-codex |
| `--session` | Isabelle session name | LatticeCrypto |

## Single-Shot Evaluation

For quick testing without iteration (allows `sorry`):

### Running a Single Prompt

```bash
eval/run-prompt.sh --prompt isabelle-vector-ops-01 --skill isabelle-basics --schema default
```

### With Multiple Skills

```bash
eval/run-prompt.sh \
    --prompt isabelle-lwe-encryption-01 \
    --skill isabelle-basics \
    --skill isabelle-code-generation \
    --skill isabelle-lattice-crypto \
    --schema default --tail
```

### Debugging Failures

```bash
eval/debug.sh --latest
```

### Cleaning Up

```bash
eval/clean.sh --all
```

## Installing Skills

Skills are already configured in `.codex/skills/` (symlinks to `skills/`).

### For Codex CLI

Skills are auto-discovered from `.codex/skills/`. No action needed.

### For Claude Code CLI

```bash
mkdir -p ~/.claude/skills
cp -R ./skills/isabelle-* ~/.claude/skills/
```

### Project-scoped (alternative)

```bash
mkdir -p ./.claude/skills
cp -R ./skills/isabelle-* ./.claude/skills/
```

## Proof Requirements

Isabella enforces **complete proofs** - no `sorry` or `oops` allowed. The Ralph Loop iterates until Isabelle accepts all proofs.

### Proof Methods

| Method | Use Case |
|--------|----------|
| `by auto` | First choice - combines simp + classical reasoning |
| `by simp` | Equational goals with rewrite rules |
| `by blast` | Complex predicate logic |
| `by arith` | Linear arithmetic |
| `by (induct x)` | Structural induction on recursive types |
| `by (cases x)` | Case analysis on constructors |

### Tips for Complete Proofs

1. Start simple - break complex lemmas into smaller steps
2. Unfold definitions: `unfolding foo_def by auto`
3. Add simp rules: `by (auto simp add: def1_def def2_def)`
4. Use auxiliary lemmas for complex subgoals

## Skills Reference

| Skill | Description |
|-------|-------------|
| `isabelle-basics` | Theory files, imports, definitions, lemmas |
| `isabelle-datatypes` | Datatypes, primrec, fun, records |
| `isabelle-proofs` | Proof methods, induction, Isar (NO sorry!) |
| `isabelle-code-generation` | Haskell export, code equations |
| `isabelle-lattice-basics` | Lattice theory, partial orders |
| `isabelle-lattice-crypto` | LWE, SIS, RLWE, security |
| `isabelle-algebra` | Groups, rings, polynomial rings |
| `isabelle-number-theory` | Modular arithmetic, CRT, NTT |

## Lattice Cryptography Topics

The theories cover:

- **Lattice Basics**: Vector operations, inner products, norms
- **Polynomial Rings**: Z_q[X]/(X^n + 1) arithmetic for RLWE
- **LWE**: Learning With Errors problem and encryption
- **Ring-LWE**: More efficient variant using polynomial rings

## Contributing

1. Add new theories in `isabelle/theories/`
2. Update `isabelle/ROOT` to include new theories
3. Add corresponding skills in `skills/`
4. Add evaluation prompts in `eval/prompts/`

## License

MIT
