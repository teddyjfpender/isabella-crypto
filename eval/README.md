# Evaluation Harness

This directory contains the evaluation harness for testing agent-generated Isabelle/HOL theories.

## Overview

The harness provides:
- **Scaffolding**: Initialize Isabelle projects with proper structure
- **Running**: Execute prompts with optional skills
- **Verification**: Build theories and export Haskell code
- **Debugging**: Analyze failures and re-run steps

## Directory Structure

```
eval/
├── run-prompt.sh      # Main orchestration script
├── verify.sh          # Verification (check, build, export)
├── scaffold.sh        # Project initialization
├── eval-runner.sh     # Batch runner
├── clean.sh           # Cleanup script
├── debug.sh           # Debugging workflow
├── prompts/           # Test prompts (markdown)
├── rubric/            # Pass/fail criteria
├── schema/            # JSON output schemas
├── work/              # Working directories (generated)
└── results/           # Verification results (generated)
```

## Workflow

### 1. Single Prompt Evaluation

```bash
# Run a prompt with a skill
./run-prompt.sh --prompt isabelle-vector-ops-01 --skill isabelle-code-generation

# Run with schema enforcement
./run-prompt.sh --prompt isabelle-vector-ops-01 --schema default

# Verbose mode
./run-prompt.sh --prompt isabelle-vector-ops-01 --verbose
```

### 2. Batch Evaluation

```bash
# Run all prompts
./eval-runner.sh --prompts-dir prompts

# Re-run failed only
./eval-runner.sh --work-dirs work --failed-only
```

### 3. Debugging

```bash
# Debug latest failure
./debug.sh --latest

# Show specific step
./debug.sh eval/results/2024-01-23/isabelle-vector-ops-01 --step build

# Re-run a step
./debug.sh eval/results/2024-01-23/isabelle-vector-ops-01 --re-run build
```

### 4. Cleanup

```bash
# Clean everything
./clean.sh --all

# Clean only work directories
./clean.sh --work

# Dry run
./clean.sh --all --dry-run
```

## Verification Steps

The `verify.sh` script runs three steps:

1. **check** - Syntax check with `isabelle build -n`
2. **build** - Full build with `isabelle build`
3. **export** - Export Haskell with `isabelle build -e`

Results are written to `verify.json`:

```json
{
  "status": "pass",
  "steps": [
    {"name": "check", "status": "pass", "duration": 5.2},
    {"name": "build", "status": "pass", "duration": 12.3},
    {"name": "export", "status": "pass", "duration": 8.1}
  ]
}
```

## Writing Prompts

Create prompts in `prompts/` as markdown files:

```markdown
# Prompt ID: my-prompt-01

## Task
[What to build]

## Requirements
1. [Requirement 1]
2. [Requirement 2]

## Constraints
- [Constraint 1]

## Technical Notes
- [Helpful hints]

## Deliverable
Only the complete theory file content.
```

## Writing Rubrics

Create rubrics in `rubric/` matching prompt names:

```markdown
# Rubric for my-prompt-01

## Pass Criteria
- [Criterion 1]
- [Criterion 2]

## Fail Criteria
- [Failure condition]
```

## Output Schema

The default schema (`schema/code-output.schema.json`) expects:

```json
{
  "code": "theory MyTheory...",
  "notes": "Explanation of approach..."
}
```

## Python Utilities

| Script | Purpose |
|--------|---------|
| `extract_code.py` | Extract code from JSON output |
| `ensure_root_file.py` | Normalize ROOT configuration |
| `record_step.py` | Record verification step |
| `steps_to_verify.py` | Generate verify.json |
| `write_run_metadata.py` | Write run.json |
| `collect_haskell.py` | Collect generated Haskell |
