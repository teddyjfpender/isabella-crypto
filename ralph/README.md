# Ralph Loop for Isabella

Iterative orchestrator for generating Isabelle theories with **complete proofs**.

## Overview

The Ralph Loop implements Geoffrey Huntley's technique of iterative work-review cycles. Unlike single-shot generation, it feeds Isabelle build errors back to the AI, allowing it to fix proofs until they compile.

## Files

| File | Description |
|------|-------------|
| `isabella-loop.sh` | Main orchestrator script |
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
   - **Success** (exit 0): Export Haskell code, exit
   - **Failure**: Extract errors, save as feedback, continue to next iteration

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
