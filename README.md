# Isabella

**Isab**elle + Latt**ice** Cryptography = **Isabella**

Formally verified lattice-based cryptography in Isabelle/HOL with executable Haskell code generation.

## Overview

This repository contains:

- **Isabelle Theories**: Formal proofs and definitions for lattice-based cryptography
- **Haskell Library**: Generated and hand-written Haskell code for lattice crypto primitives
- **Skills**: Agent skills for writing Isabelle theories
- **Evaluation Harness**: Scripts for testing and validating Isabelle code generation

## Prerequisites

- [Isabelle](https://isabelle.in.tum.de/) (2024 or later)
- [GHC](https://www.haskell.org/ghc/) and [Cabal](https://www.haskell.org/cabal/)
- Python 3.8+
- Claude Code CLI (for evaluation harness)

### Installing Isabelle (macOS)

```bash
brew install --cask isabelle
```

Or download from https://isabelle.in.tum.de/installation.html

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
│   ├── run-prompt.sh      # Main runner
│   ├── verify.sh          # Verification
│   ├── scaffold.sh        # Project scaffolding
│   ├── debug.sh           # Debugging workflow
│   └── prompts/           # Test prompts
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

## Evaluation Harness

The evaluation harness tests agent-generated Isabelle code.

### Running a Single Prompt

```bash
eval/run-prompt.sh --prompt isabelle-vector-ops-01 --skill isabelle-basics
```

### Running All Prompts

```bash
eval/eval-runner.sh --prompts-dir eval/prompts
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

### User-scoped (all projects)

```bash
mkdir -p ~/.claude/skills
cp -R ./skills/isabelle-* ~/.claude/skills/
```

### Project-scoped

```bash
mkdir -p ./.claude/skills
cp -R ./skills/isabelle-* ./.claude/skills/
```

## Skills Reference

| Skill | Description |
|-------|-------------|
| `isabelle-basics` | Theory files, imports, definitions, lemmas |
| `isabelle-datatypes` | Datatypes, primrec, fun, records |
| `isabelle-proofs` | Proof methods, induction, Isar |
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
