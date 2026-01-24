---
name: isabelle-proofs
description: Proof techniques in Isabelle/HOL including auto, simp, blast, induction, and case analysis. ALWAYS provide complete proofs.
---

# Isabelle Proofs

## CRITICAL: Complete Proofs Required

**NEVER use `sorry` or `oops`**. All lemmas and theorems MUST have complete proofs.
If a proof seems too hard, simplify the lemma statement or break it into smaller steps.

## Web References

When you need more information about proof methods, fetch these sources:

| Topic | URL | Description |
|-------|-----|-------------|
| Prog & Prove | https://isabelle.in.tum.de/doc/prog-prove.pdf | Best intro to proofs in Isabelle |
| Isar Reference | https://isabelle.in.tum.de/doc/isar-ref.pdf | Complete Isar proof language reference |
| Sledgehammer | https://isabelle.in.tum.de/doc/sledgehammer.pdf | Automatic proof finder guide |
| Simplifier | https://isabelle.in.tum.de/doc/simp.pdf | Simplifier documentation |
| What's In Main | https://isabelle.in.tum.de/library/HOL/HOL/Main.html | Main theory with available lemmas |

## Overview

This skill covers the various proof methods and tactics available in Isabelle/HOL. Understanding when to use different proof methods like `auto`, `simp`, `blast`, and when to apply induction or case analysis is crucial for efficient theorem proving.

## Proof Methods (in order of what to try)

1. **by auto** - Combines simp with classical reasoning. Try this first.
2. **by simp** - Simplification using rewrite rules. Good for equational goals.
3. **by blast** - Tableau prover for predicate logic. Use for complex logical goals.
4. **by arith / by linarith** - For linear arithmetic goals.
5. **by (induct x)** - Structural induction on recursive types.
6. **by (cases x)** - Case analysis on constructors.

## Quick Use

- Read `references/proofs.md` before answering questions about proof strategies
- Use web search to fetch the URLs above when stuck on a proof
- Start with simpler methods (simp, auto) before trying more powerful ones
- Use induction for recursive datatypes and properties
- If `auto` fails, try `auto simp add: def1_def def2_def` to unfold definitions

## Response Checklist

- [ ] **NO sorry/oops** - All proofs must be complete
- [ ] Appropriate proof method chosen for the goal
- [ ] Induction variable correctly identified for recursive proofs
- [ ] Case analysis covers all constructors/possibilities
- [ ] Auxiliary lemmas suggested when main proof is complex
- [ ] Isar proofs are well-structured with clear intermediate steps
- [ ] Simp rules and introduction/elimination rules used appropriately

## Common Proof Patterns

### Simple definition-based proofs
```isabelle
lemma foo_prop: "foo x = bar x"
  unfolding foo_def bar_def
  by auto
```

### Induction on lists
```isabelle
lemma sum_append: "sum_list (xs @ ys) = sum_list xs + sum_list ys"
  by (induct xs) auto
```

### Case analysis
```isabelle
lemma bool_case: "P True ∧ P False ⟹ P b"
  by (cases b) auto
```

## Example Requests

- "What's the difference between auto and simp?"
- "How do I prove a property by induction over lists?"
- "When should I use blast vs auto?"
- "How do I structure a proof using Isar?"
- "How do I debug a failing proof?"
