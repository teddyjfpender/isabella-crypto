---
name: isabelle-hol-build-and-codegen-optimisation
description: Profile and optimise Isabelle/HOL performance across proof checking, session builds, and code generation/runtime evaluation. Use when batch builds are slow, IDE responsiveness degrades, code generation is expensive or produces poor runtime behavior, or parallel build settings and evaluation backends need tuning.
---

# Profiling, Build Optimisation, and Code Generation Performance (Isabelle/HOL)

## Goal
Make a development:
- faster to build/check in batch
- more responsive in the IDE
- produce faster / better controlled generated code (SML/OCaml/Haskell/Scala/Eval)

This skill is about performance *across the whole pipeline*:
proof checking → sessions/build → codegen/evaluation → runtime.

---

## 1) Batch-build profiling (find where time goes)

### 1.1 Use build progress + timing thresholds
In recent Isabelle versions there are system options that make long-running commands visible.
Practical pattern:
- enable detailed progress output
- set a timing threshold so only “slow commands” are reported

Recommendation:
- keep the threshold high first (e.g. seconds) to find the worst offenders
- then drill down locally

### 1.2 ML profiling for “what consumes time/allocations”
There is a system option for global ML profiling in builds (typically modes like:
- profiling by **time**
- profiling by **allocations**)

Use it when:
- you suspect a method call triggers huge internal work
- heap usage spikes
- you want per-session performance diagnostics

### 1.3 Use the session build database
If something fails or produces warnings:
- use the build-log tooling to print messages from the build database
- filter for “Error” / “Warning” / specific substrings

This is essential for large multi-session projects (or AFP-scale builds).

### 1.4 Parallel build tuning
Key knobs:
- number of parallel jobs (processes)
- number of Isabelle/ML worker threads per job

Tip:
- more jobs is not always better if each job is heavy on memory.
- set threads based on available cores and memory bandwidth.

---

## 2) Tracing and diagnostics inside proofs (when you need “why is this slow?”)

### 2.1 Use trace bundles for targeted debugging
You can bundle tracing options (simp/linarith/metis/smt) and enable them locally.

Pattern:
~~~isabelle
bundle trace = [[simp_trace, linarith_trace, metis_trace, smt_trace]]

lemma "…"
  including trace
  by …
~~~

Use tracing only around the hotspot lemma (otherwise noise explodes).

### 2.2 Simplifier tracing (most useful in practice)
Turn on simp tracing temporarily when:
- `simp` loops
- `simp` is unexpectedly slow
- a simp rule is firing too often

Then:
- switch to `simp only:` to test hypotheses about which rule set is costly
- use `simp del:` to disable the suspected expensive rule locally

---

## 3) Code generation: understanding, profiling, and optimising

### 3.1 Know the 3 stages of code generation
Conceptually:
1. selection of code theorems
2. translation into an executable view
3. serialization to target language

The HOL toolchain provides commands/attributes to inspect and control this.

### 3.2 Inspect your code setup
Useful commands (exploration/debugging):
- `print_codesetup`
- `code_thms` / `code_deps`
- `code_printing`, `code_identifier`, `code_reserved`

Use these to answer:
- “What equations are actually used for code?”
- “Where do these code equations come from?”
- “Why does codegen pick a weird constant / module name?”

### 3.3 Turn on codegen tracing/timing (when codegen is slow)
There are attributes intended for code generator timing and tracing:
- `code_timing`
- `code_simp_trace`
- `code_runtime_trace`

Use them around the point where you run `export_code`, `value`, or related evaluation.

### 3.4 Evaluation technique matters (performance vs trust)
When you execute terms for validation (e.g. via `value`), different backends trade off:
- **simp-based evaluation**: most symbolic/trustable, often slower
- **nbe**: faster partially symbolic, heavier trusted stack
- **ML/code evaluation**: often fastest but relies on your current codegen setup

Pick the *weakest* evaluation method that is sufficient for your goal.

### 3.5 Optimising generated runtime code
Common performance principles:
- Prefer executable, pattern-matching definitions (`fun`, `primrec`) with good code equations.
- Avoid definitions that force expensive normalization (too much symbolic rewriting).
- Choose appropriate data representations (e.g. finite maps/sets as efficient structures rather than naive lists) when you care about runtime.
- If you need imperative data structures, consider the imperative framework sessions.

### 3.6 `code_reflect` for reusing compiled code inside Isabelle/ML
If you need to embed generated code into the Isabelle runtime (Eval target),
`code_reflect` can compile generated code into an ML structure and reuse it,
instead of regenerating it repeatedly.

Use when:
- you build a proof procedure that evaluates many terms repeatedly
- you want predictable evaluation performance inside ML tooling

---

## 4) Build hygiene that prevents performance regressions

### 4.1 Keep sessions modular
- Put heavy imports in a base session.
- Build heap images for stable foundations.
- Avoid giant “everything in one session” setups if you can factor.

### 4.2 Use “quick and dirty” only as a development mode
For fast iteration, there is a “quick and dirty” mode often used to bypass full checking.
Never use it to produce final artefacts or to assess real performance.

### 4.3 Use a linter / style checker if available
A dedicated Isabelle linter exists as an add-on component and can catch common anti-patterns
that harm maintainability and sometimes performance.

---

## Practical checklist (profiling & optimisation)
- [ ] Can you identify the slowest lemma/command first (don’t guess)?
- [ ] Is the cost in simp, classical search, or metis/smt reconstruction?
- [ ] Can you reduce simp set (`only:` / `del:`) and reduce splits?
- [ ] Can you replace `metis/smt` with a smaller local lemma + `simp/auto`?
- [ ] For runtime: are you using the right evaluation backend (`simp` vs `nbe` vs `code`)?
- [ ] For codegen: do you understand the `code_thms` actually used?