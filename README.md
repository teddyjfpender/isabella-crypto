# Isabella

[![CI](https://github.com/anthropics/isabella-crypto/actions/workflows/ci.yml/badge.svg)](https://github.com/anthropics/isabella-crypto/actions/workflows/ci.yml)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)

***Isab***elle + ***Latt***ice Cryptography = ***Isabella***

Formally verified lattice-based cryptography in Isabelle/HOL with multi-language code generation.

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
├── Canon/                 # Lattice Crypto Canon (main verified library)
│   ├── ROOT               # Isabelle session definitions
│   ├── Prelude.thy        # Named theorems, mod utilities
│   ├── Linear/            # Vector/matrix operations
│   ├── Algebra/           # Z_q, encoding/decoding
│   ├── Hardness/          # LWE, SIS definitions
│   ├── Crypto/            # Encryption schemes
│   └── ...
├── collect.sh             # Collect generated code (all languages)
├── build-js.sh            # Build JavaScript/TypeScript from OCaml
├── haskell/               # Verified Haskell library
│   └── isabella/
├── sml/                   # Verified SML library
│   └── isabella/
├── ocaml/                 # Verified OCaml library (source for JS)
│   └── isabella/
├── scala/                 # Verified Scala library
│   └── isabella/
├── javascript/            # Compiled JavaScript (via js_of_ocaml)
│   └── isabella/
├── typescript/            # TypeScript package with type definitions
│   └── isabella/
├── bench/                 # Cross-language benchmarks
│   ├── run-benchmarks.sh  # Main benchmark runner
│   ├── summarize.sh       # Generate comparison report
│   ├── runners/           # Language-specific runners
│   └── data/              # Benchmark results (JSON)
├── eval/                  # Evaluation harness
│   ├── run-prompt.sh      # Single-shot runner
│   ├── verify.sh          # Isabelle verification
│   ├── scaffold.sh        # Project scaffolding
│   ├── prompts/           # Test prompts (including canon-*)
│   └── work/              # Generated theories
├── ralph/                 # Ralph loop orchestrator
│   ├── isabella-loop.sh   # Iterative work-review runner
│   └── step-loop.sh       # Step-based incremental runner
├── plan/                  # Canon roadmap and progress tracking
├── skills/                # Agent skills for Isabelle
│   ├── isabelle-basics/
│   ├── isabelle-proofs/
│   ├── isabelle-code-generation/
│   ├── isabelle-lattice-crypto/
│   ├── isabelle-canon/    # Canon-specific patterns
│   └── ...
└── dist/                  # Packaged skills
```

## Supported Target Languages

| Language | Status | Method |
|----------|--------|--------|
| Haskell | ✓ Built-in | `export_code ... in Haskell` |
| SML | ✓ Built-in | `export_code ... in SML` |
| OCaml | ✓ Built-in | `export_code ... in OCaml` |
| Scala | ✓ Built-in | `export_code ... in Scala` |
| JavaScript | ✓ Via js_of_ocaml | OCaml → `./build-js.sh` |
| TypeScript | ✓ Via js_of_ocaml | OCaml → `./build-js.sh` |

## Quick Start

### Building Isabelle Theories

```bash
cd isabelle
isabelle build -d . -v LatticeCrypto
```

### Collecting Generated Code

```bash
# After ralph loop completes successfully, collect the generated code:
./collect.sh              # Haskell only (default)
./collect.sh --lang all   # All languages
./collect.sh --lang sml   # Specific language
./collect.sh --verbose    # Show collected files
```

Generated modules will be collected into:
- `haskell/isabella/src/Lattice/*.hs`
- `sml/isabella/src/Lattice/*.ML`
- `ocaml/isabella/src/lattice/*.ml`
- `scala/isabella/src/Lattice/*.scala`

### Building Libraries

```bash
# Haskell
cd haskell/isabella && cabal build

# OCaml (native)
cd ocaml/isabella && dune build

# Scala
cd scala/isabella && sbt compile
```

### Building JavaScript/TypeScript

The JavaScript/TypeScript build uses js_of_ocaml to compile OCaml to JS:

```bash
# First time setup (installs OCaml toolchain via opam)
./build-js.sh --setup

# Build JavaScript and TypeScript
./build-js.sh
```

Output:
- `javascript/isabella/dist/isabella.js` - Compiled runtime
- `typescript/isabella/` - TypeScript package with type definitions

### Running Benchmarks

Compare performance across all language targets:

```bash
# Run all benchmarks
./bench/run-benchmarks.sh

# Specific function with custom sizes
./bench/run-benchmarks.sh --function inner_prod --sizes "100,1000,5000"

# View summary report
./bench/summarize.sh
```

Results are stored as JSON in `bench/data/<function>/<language>_<size>.json`.

### Using the Haskell Library

```haskell
import qualified Lattice.LWE_Regev as Regev

-- Encrypt a bit with LWE
let ciphertext = Regev.lwe_encrypt publicKey q randomVector True

-- Decrypt
let plaintext = Regev.lwe_decrypt secretKey q ciphertext
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

## Lattice Crypto Canon

The **Canon** is a layered Isabelle library for lattice cryptography, built incrementally with complete proofs.

### Canon Structure

| Session | Theories | Description |
|---------|----------|-------------|
| `Canon_Base` | Prelude, ListVec, Zq, Norms | Mathematical infrastructure |
| `Canon_Hardness` | LWE_Def, SIS_Def, NormalForms | Hardness assumptions |
| `Canon_Crypto` | Regev_PKE, Commit_SIS, Decomp | Cryptographic constructions |
| `Canon_Rings` | PolyMod, ModuleLWE | Ring variants |
| `Canon_ZK` | Sigma_Base | Zero-knowledge proofs |

### Building the Canon

```bash
# Build the base layer
isabelle build -d Canon Canon_Base

# Build everything (once all theories exist)
isabelle build -d Canon Canon_Full
```

### Step-Loop for Canon Development

The **step-loop** builds Canon theories incrementally, verifying each step before proceeding:

```bash
# Standalone theory (no dependencies)
ralph/step-loop.sh --prompt canon-prelude \
    --output-dir Canon --theory-name Prelude --session Canon_Base

# Theory with dependencies
ralph/step-loop.sh --prompt canon-linear-listvec \
    --output-dir Canon --theory-name ListVec --theory-path Linear \
    --session Canon_Base \
    --imports 'Canon_Base.Prelude' \
    --parent-session Canon_Base --session-dir Canon
```

#### Step-Loop Features

- **Step-by-step verification**: Each step is validated before proceeding
- **Resume capability**: Run the same command to continue after interruption
- **Session-based verification**: Test against Canon session for dependency checking
- **Robust proof patterns**: Prompts include hardened proofs with explicit case splits

See `ralph/README.md` for full step-loop documentation.

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

## About Generated Haskell Code

The Haskell code in `haskell/isabella/` is extracted from Isabelle proofs, not hand-written. It produces GHC warnings (unused imports, incomplete patterns, etc.) but this is normal - the proofs guarantee correctness even where GHC's linter complains. See `haskell/isabella/README.md` for details.

## CI/CD

GitHub Actions workflows automate building and testing:

| Workflow | Trigger | Purpose |
|----------|---------|---------|
| `ci.yml` | Push to main, PRs | Full build: Isabelle → all languages |
| `pr-check.yml` | PRs | Fast syntax checks for Isabelle, TypeScript, OCaml, Haskell |
| `release.yml` | Tags `v*` | Build and publish releases to GitHub, npm |
| `benchmark.yml` | Tags `v*`, manual | Cross-language performance benchmarks |

### CI Pipeline

```
┌─────────────┐     ┌─────────────┐     ┌─────────────────┐
│   Isabelle  │────>│   Collect   │────>│  Build Targets  │
│   Build     │     │   Code      │     │                 │
└─────────────┘     └─────────────┘     │  ├─ Haskell     │
                                        │  ├─ JavaScript  │
                                        │  ├─ TypeScript  │
                                        │  └─ Scala       │
                                        └─────────────────┘
```

### Running Locally

```bash
# Full build (requires Isabelle, opam, cabal)
./collect.sh --lang all
./build-js.sh
cd haskell/isabella && cabal build
```

## Contributing

1. Add new theories in `eval/work/<prompt-name>/`
2. Run Ralph loop to verify proofs: `ralph/isabella-loop.sh --prompt <name>`
3. Collect generated code: `./collect.sh --lang all`
4. Add evaluation prompts in `eval/prompts/`

## License

MIT
