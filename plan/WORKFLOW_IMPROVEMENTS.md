# Workflow Improvements Plan

This document outlines changes needed to support the Canon structure.

---

## Issue 1: Ralph Loop Iteration Granularity

### Current State
- Worker generates **entire theory** in one phase
- Reviewer checks **after full generation**
- Feedback is coarse-grained (entire build log)
- Worker may go far down wrong path before correction

### Desired State
- Worker writes **one step** (definition, lemma, or small group)
- Reviewer verifies **after each step**
- Feedback is fine-grained and immediate
- Course corrections happen early

### Solution: Step-Based Ralph Loop

Create `ralph/step-loop.sh` with:

```
┌─────────────────────────────────────────────────────────┐
│                    STEP-BASED LOOP                       │
├─────────────────────────────────────────────────────────┤
│                                                          │
│  For each STEP in plan:                                  │
│    ┌──────────────┐         ┌──────────────┐            │
│    │  Work Phase  │ ──────▶ │ Review Phase │            │
│    │ (one step)   │         │ (verify step)│            │
│    └──────────────┘         └──────────────┘            │
│           ▲                        │                     │
│           │         PASS ──────────┼──▶ Next step       │
│           │                        │                     │
│           └─────── FAIL ◀──────────┘                     │
│                   (fix this step before moving on)       │
│                                                          │
└─────────────────────────────────────────────────────────┘
```

**Key changes**:
1. Prompts decomposed into numbered steps
2. Worker writes ONE step, reviewer checks immediately
3. Accumulative theory file (append each step)
4. Step-level feedback, not theory-level

### Implementation

#### New files:
- `ralph/step-loop.sh` - Step-based orchestrator
- `ralph/step-work.yaml` - Work phase for single step
- `ralph/step-review.yaml` - Review phase for incremental check

#### Prompt format change:
```markdown
# Prompt ID: canon-linear-listvec

## Steps

### Step 1: Type Synonyms
Define int_vec and int_matrix type synonyms.

### Step 2: Validity Predicates
Define valid_vec and valid_matrix predicates.

### Step 3: Vector Operations
Define vec_add, vec_sub, scalar_mult with length lemmas.

### Step 4: Inner Product
Define inner_prod with bilinearity lemmas.

### Step 5: Matrix Operations
Define mat_vec_mult with dimension lemma.

### Step 6: Transpose Identity
Prove iprod_transpose theorem.

### Step 7: Code Export
Export all definitions to Haskell.
```

#### State files:
```
.ralph/<prompt-id>/
├── current-step.txt         # Which step we're on (1, 2, 3...)
├── step-1-code.thy          # Code from step 1
├── step-1-feedback.md       # Feedback if step 1 failed
├── step-2-code.thy          # Code from step 2
├── accumulated.thy          # All completed steps combined
├── step-attempts.txt        # Attempts per step (step:attempts)
└── ...
```

#### Incremental verification:
```bash
# After each step, verify the accumulated theory
cat header.thy step-1-code.thy step-2-code.thy ... > accumulated.thy
isabelle build -d . -n SessionName
```

---

## Issue 2: Prompts and Skills for Canon Theories

### New Prompts Needed

| Prompt ID | Theory | Priority |
|-----------|--------|----------|
| `canon-prelude` | Prelude.thy | 1 |
| `canon-linear-listvec` | Linear/ListVec.thy | 2 |
| `canon-algebra-zq` | Algebra/Zq.thy | 3 |
| `canon-analysis-norms` | Analysis/Norms.thy | 4 |
| `canon-prob-discrete` | Prob/DiscreteBasics.thy | 12 |
| `canon-hardness-lwe` | Hardness/LWE_Def.thy | 5 |
| `canon-hardness-sis` | Hardness/SIS_Def.thy | 5 |
| `canon-hardness-normalforms` | Hardness/NormalForms.thy | 6 |
| `canon-crypto-regev` | Crypto/Regev_PKE.thy | 7 |
| `canon-gadgets-decomp` | Gadgets/Decomp.thy | 8 |
| `canon-crypto-commit` | Crypto/Commit_SIS.thy | 9 |
| `canon-rings-polymod` | Rings/PolyMod.thy | 10 |
| `canon-rings-modulelwe` | Rings/ModuleLWE.thy | 11 |
| `canon-zk-sigma` | ZK/Sigma_Base.thy | 13 |

### New/Updated Skills Needed

| Skill | Purpose | New? |
|-------|---------|------|
| `isabelle-canon-prelude` | Named theorems, bundles, notations | New |
| `isabelle-modules` | Module algebra over R_q | New |
| `isabelle-gadgets` | Decomposition, gadget matrices | New |
| `isabelle-commitments` | Lattice commitment schemes | New |
| `isabelle-sigma-protocols` | ZK Σ-protocol framework | New |
| `isabelle-locales` | Locale-based dimension tracking | Update existing |

### Prompt Template for Canon

```markdown
# Prompt ID: canon-<section>-<theory>

## Task
Create the Canon/<Section>/<Theory>.thy theory file.

## Dependencies
This theory imports:
- Canon/Prelude (if not Prelude itself)
- Canon/<other dependencies>

## Steps

### Step 1: Header and Imports
```isabelle
theory <TheoryName>
  imports
    "../Prelude"
    (* other imports *)
begin
```

### Step 2: <First concept>
<Detailed requirements>

### Step 3: <Second concept>
<Detailed requirements>

...

### Step N: Code Export
Export to Haskell module Canon.<Section>.<Theory>

## Constraints
- Theory name: <TheoryName>
- No sorry/oops
- Must use named_theorems from Prelude
- Dimension tracking via locales

## Deliverable
Working theory at Canon/<Section>/<Theory>.thy
```

---

## Issue 3: Output Directory Configuration

### Current Behavior
- All output goes to `eval/work/<prompt-id>/LatticeCrypto.thy`
- Session name hardcoded to `LatticeCrypto`
- ROOT file generated in work directory

### Desired Behavior
- Output to Canon directory structure
- Flexible theory names
- ROOT file at Canon root

### Solution: Extended CLI Options

#### New options for `run-prompt.sh`:
```bash
--output-dir <path>     # Where to write theory file (default: eval/work/<id>)
--theory-name <name>    # Theory name (default: LatticeCrypto)
--theory-path <path>    # Subdirectory within session (e.g., Linear)
--root-dir <path>       # Where ROOT file lives (default: same as output-dir)
```

#### New options for `isabella-loop.sh`:
```bash
--output-dir <path>     # Canon output directory
--theory-name <name>    # Theory name for this file
--theory-path <path>    # Subdirectory (Linear, Algebra, etc.)
```

#### Example usage:
```bash
./isabella-loop.sh \
    --prompt canon-linear-listvec \
    --output-dir "${PROJECT_ROOT}/Canon" \
    --theory-name ListVec \
    --theory-path Linear \
    --session Canon_Base \
    --skill isabelle-basics \
    --skill isabelle-proofs \
    --iterations 5
```

This would:
1. Write theory to `Canon/Linear/ListVec.thy`
2. Use session name `Canon_Base`
3. Expect ROOT file at `Canon/ROOT`

### ROOT File Structure for Canon

```
(* Canon/ROOT *)
session Canon_Base = HOL +
  options [document = false]
  sessions
    "HOL-Library"
    "HOL-Number_Theory"
  directories
    "."
    "Linear"
    "Algebra"
    "Analysis"
    "Prob"
  theories
    Prelude
    "Linear/ListVec"
    "Algebra/Zq"
    "Analysis/Norms"
    "Prob/DiscreteBasics"

session Canon_Hardness = Canon_Base +
  directories
    "Hardness"
  theories
    "Hardness/LWE_Def"
    "Hardness/SIS_Def"
    "Hardness/NormalForms"

(* etc. *)
```

---

## Implementation Order

### Phase 1: Workflow Plumbing
1. [ ] Add `--output-dir`, `--theory-name`, `--theory-path` to `run-prompt.sh`
2. [ ] Add same options to `isabella-loop.sh`
3. [ ] Create Canon directory structure with ROOT
4. [ ] Test with existing prompt using new options

### Phase 2: Step-Based Loop
1. [ ] Create `ralph/step-loop.sh`
2. [ ] Create `ralph/step-work.yaml` and `ralph/step-review.yaml`
3. [ ] Define step-based prompt format
4. [ ] Test with simple prompt

### Phase 3: Canon Prompts
1. [ ] Create `canon-prelude` prompt
2. [ ] Create `canon-linear-listvec` prompt (depends on prelude)
3. [ ] Create remaining prompts in dependency order

### Phase 4: Canon Skills
1. [ ] Create `isabelle-canon-prelude` skill
2. [ ] Create domain-specific skills (modules, gadgets, etc.)

---

## Verification Checklist

After implementation, verify:

- [ ] `./isabella-loop.sh --prompt canon-prelude --output-dir Canon --theory-name Prelude` works
- [ ] Step-based loop completes a multi-step prompt
- [ ] Canon/ROOT builds all theories in dependency order
- [ ] Code exports to correct Haskell modules
- [ ] Feedback from step-loop is actionable and specific
