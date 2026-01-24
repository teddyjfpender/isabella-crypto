# Ralph Loop for Isabella

Iterative orchestrator for generating Isabelle theories with **complete proofs**.

## Overview

The Ralph Loop implements Geoffrey Huntley's technique of iterative work-review cycles. Unlike single-shot generation, it feeds Isabelle build errors back to the AI, allowing it to fix proofs until they compile.

Two loop variants are available:

| Script | Use Case |
|--------|----------|
| `isabella-loop.sh` | Full theory generation with work-review cycles |
| `step-loop.sh` | Incremental step-by-step development for Canon library |

## Files

| File | Description |
|------|-------------|
| `isabella-loop.sh` | Main orchestrator script |
| `step-loop.sh` | Step-based incremental builder for Canon |
| `ralph-work.yaml` | Work phase configuration (for goose) |
| `ralph-review.yaml` | Review phase configuration (for goose) |

## Usage

```bash
./isabella-loop.sh \
    --prompt <prompt-id> \
    --skill <skill-name> \
    --iterations <max-attempts>
```

### Example

```bash
./isabella-loop.sh \
    --prompt isabelle-lwe-encryption-01 \
    --skill isabelle-basics \
    --skill isabelle-proofs \
    --skill isabelle-code-generation \
    --skill isabelle-lattice-crypto \
    --iterations 5
```

## Options

| Option | Description | Default |
|--------|-------------|---------|
| `--prompt` | Prompt ID from `eval/prompts/` | (required) |
| `--skill` | Skill to include (repeatable) | - |
| `--iterations` | Max iterations before giving up | 5 |
| `--provider` | AI provider (openai, anthropic) | openai |
| `--model` | Model for work phase | gpt-5.2-codex |
| `--review-provider` | Provider for review phase | anthropic |
| `--review-model` | Model for review phase | claude-sonnet-4-20250514 |
| `--session` | Isabelle session name | LatticeCrypto |
| `--verbose` | Enable verbose output | false |

## How It Works

```
┌─────────────────────────────────────────────────────────────┐
│                     Isabella Loop                            │
├─────────────────────────────────────────────────────────────┤
│                                                              │
│   ┌──────────────┐         ┌──────────────┐                 │
│   │  Work Phase  │ ──────▶ │ Review Phase │                 │
│   │   (Codex)    │         │  (Isabelle)  │                 │
│   │              │         │              │                 │
│   │ Generate .thy│         │ isabelle     │                 │
│   │ with proofs  │         │ build -v     │                 │
│   └──────────────┘         └──────────────┘                 │
│          ▲                        │                          │
│          │                        │                          │
│          │         SUCCESS ───────┼──────▶ EXIT (0)         │
│          │         + export Haskell code                    │
│          │                        │                          │
│          └─────── FAILURE ◀───────┘                          │
│                   (errors as feedback)                       │
│                                                              │
└─────────────────────────────────────────────────────────────┘
```

### Iteration Flow

1. **Work Phase**: Generate Isabelle theory using AI
   - First iteration: Use original prompt
   - Subsequent iterations: Augment prompt with error feedback

2. **Review Phase**: Run `isabelle build` (strict mode)
   - No `quick_and_dirty` - all proofs must be complete
   - No `sorry` or `oops` allowed

3. **Decision**:
   - **Success** (exit 0): Export code to all target languages, exit
   - **Failure**: Extract errors, save as feedback, continue to next iteration

4. **Collection** (after success):
   ```bash
   ./collect.sh --lang all   # Gather Haskell, SML, OCaml, Scala
   ```

## State Directory

State is persisted in `.ralph/<prompt-id>/`:

```
.ralph/isabelle-lwe-encryption-01/
├── feedback.md           # Errors from last failed build
├── iteration.txt         # Current iteration number
├── work-1.log           # Work phase log (iteration 1)
├── isabelle-1.log       # Isabelle build log (iteration 1)
├── augmented/           # Augmented prompts with feedback
│   └── isabelle-lwe-encryption-01.md
└── .ralph-complete      # Created on success
```

## Key Differences from Single-Shot

| Single-Shot (`run-prompt.sh`) | Ralph Loop (`isabella-loop.sh`) |
|------------------------------|--------------------------------|
| One attempt | Up to N iterations |
| May use `sorry` | Complete proofs required |
| Quick validation | Strict Isabelle build |
| Good for prototyping | Good for production proofs |

## Proof Requirements

The loop enforces:

1. **No `sorry`** - All lemmas must have complete proofs
2. **No `oops`** - No abandoned proof attempts
3. **Valid types** - All type errors must be fixed
4. **Working export** - `export_code` must succeed

## Troubleshooting

### Loop never succeeds

- Check if the proof is actually achievable
- Try simpler lemma statements
- Add more specific skills (e.g., `isabelle-proofs`)

### Feedback not helping

- The AI may need more context in the skills
- Consider adding example proofs to skill references

### Isabelle build hangs

- Increase timeout in `scaffold.sh` (default: 600s)
- Some proofs require significant compute

---

## Step-Loop for Canon Development

The step-loop (`step-loop.sh`) builds theories incrementally, processing prompts step-by-step with verification after each step.

### When to Use Step-Loop vs Isabella-Loop

| Scenario | Recommended |
|----------|-------------|
| Building Canon library theories | `step-loop.sh` |
| One-off theory generation | `isabella-loop.sh` |
| Theories with dependencies on Canon | `step-loop.sh` |
| Exploratory proof development | `isabella-loop.sh` |

### Usage

```bash
./step-loop.sh --prompt <prompt-id> [options]
```

### Options

| Option | Description | Default |
|--------|-------------|---------|
| `--prompt` | Prompt ID from `eval/prompts/` | (required) |
| `--skill` | Skill to include (repeatable) | - |
| `--max-attempts` | Max attempts per step | 7 |
| `--provider` | AI provider (anthropic, openai) | anthropic |
| `--model` | Model for generation | claude-sonnet-4-20250514 |
| `--output-dir` | Output directory for theory | Canon |
| `--theory-name` | Theory name | LatticeCrypto |
| `--theory-path` | Subdirectory (e.g., Linear) | - |
| `--session` | Isabelle session name | LatticeCrypto |
| `--imports` | Theory imports | Main + HOL libs |
| `--parent-session` | Parent session for verification | - |
| `--session-dir` | Directory with parent session ROOT | - |
| `--reset` | Clear progress and start fresh | false |
| `--verbose` | Show attempted code on failure | false |

### Examples

#### Standalone Theory (No Dependencies)

```bash
./step-loop.sh --prompt canon-prelude \
    --output-dir Canon \
    --theory-name Prelude \
    --session Canon_Base
```

#### Theory with Dependencies

```bash
./step-loop.sh --prompt canon-linear-listvec \
    --output-dir Canon \
    --theory-name ListVec \
    --theory-path Linear \
    --session Canon_Base \
    --imports 'Canon_Base.Prelude' \
    --parent-session Canon_Base \
    --session-dir Canon
```

### How It Works

```
┌─────────────────────────────────────────────────────────────────┐
│                      Step-Based Loop                             │
├─────────────────────────────────────────────────────────────────┤
│                                                                  │
│   ┌──────────────┐    ┌──────────────┐    ┌──────────────┐      │
│   │   Step 1     │───>│   Step 2     │───>│   Step N     │      │
│   └──────────────┘    └──────────────┘    └──────────────┘      │
│          │                   │                   │               │
│          ▼                   ▼                   ▼               │
│   ┌──────────────┐    ┌──────────────┐    ┌──────────────┐      │
│   │   Verify     │    │   Verify     │    │   Verify     │      │
│   │  (Isabelle)  │    │  (Isabelle)  │    │  (Isabelle)  │      │
│   └──────────────┘    └──────────────┘    └──────────────┘      │
│          │                   │                   │               │
│      ✓ Pass              ✓ Pass              ✓ Pass             │
│          │                   │                   │               │
│          ▼                   ▼                   ▼               │
│   accumulated.thy ─────────────────────> final Theory.thy       │
│                                                                  │
└─────────────────────────────────────────────────────────────────┘
```

### State Directory

Progress is saved in `.ralph/<prompt-id>/`:

```
.ralph/canon-prelude/
├── accumulated.thy      # Verified code so far
├── current_step.txt     # Current step number
├── current_attempt.thy  # Code being tried (visible during attempts)
├── last_feedback.txt    # Error from last failed attempt
└── .complete            # Created on success
```

### Resume Capability

If interrupted or on failure, run the same command to resume:

```bash
# First run - fails at step 3
./step-loop.sh --prompt canon-prelude ...
# ... step 3 fails after max attempts

# Resume from step 3
./step-loop.sh --prompt canon-prelude ...
# "Found existing progress: step 3/4. Resume? [Y/n]"
```

### Verification Modes

The step-loop supports two verification modes:

1. **Standalone** (default): Builds against HOL + HOL-Library + HOL-Number_Theory
2. **Session-based**: Builds on top of a parent session (for dependent theories)

Session-based verification is enabled when `--parent-session` is provided:

```bash
# This verifies ListVec can actually import Prelude from Canon_Base
./step-loop.sh --prompt canon-linear-listvec \
    --parent-session Canon_Base \
    --session-dir Canon \
    ...
```

### Prompt Structure

Step-loop prompts use `### Step N` markers to define steps:

```markdown
## Steps

### Step 1: Type Definitions

Define the basic types...

### Step 2: Operations

Define operations on those types...

### Step 3: Properties

Prove key properties...
```

Each step is processed independently, with code accumulated as steps pass.

### Robustness Guidelines

Step-loop prompts should include:

1. **Exact code blocks** marked with "USE THIS EXACT CODE"
2. **Type annotations** for numeric types (e.g., `(n::int)`)
3. **Explicit case splits** for conditionals
4. **Prefer `arith` over `auto`** for div/mod goals

See `eval/prompts/canon-prelude.md` for an example of a robust prompt.
