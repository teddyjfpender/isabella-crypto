---
name: isabelle-hol-proof-optimisation
description: Optimise existing Isabelle/HOL proofs for faster check times and stronger robustness under library changes. Use when `.thy` files re-check slowly, a single proof command is a hotspot, automation (`simp`, `auto`, `force`, `blast`, `metis`, `smt`) times out, or small refactors trigger large proof slowdowns.
---

# Isabelle/HOL Proof Optimisation

## Goal
Make existing Isabelle/HOL proofs *faster to check* and *more robust* (less brittle under library changes).

## When to use
- A theory file re-checks slowly, or a specific lemma/method call is a hotspot.
- A proof is “too automatic” (e.g. `auto`, `force`, `blast`, `metis`, `smt`) and sometimes times out.
- A small refactor causes large slowdowns (a sign of fragile automation / oversized rule sets).

## The two levers that matter most
1. **Reduce search** (smaller fact sets, fewer splits, fewer goals).
2. **Reduce rewriting work** (disciplined simp rules, avoid term blow-ups).

---

## Workflow for optimising an existing proof

### 0. Localise the hotspot
- Find the *exact command* that is slow (often a single `by ...`).
- If you can, isolate it into a small lemma (same statement, fewer surrounding assumptions).

### 1. Classify the “engine” that is expensive
- **Simplifier** (`simp`, `simp_all`, and anything that uses simp internally: `auto`, `force`, `fastforce`).
- **Classical reasoner** (`auto`, `blast`, `force`, `fastforce`).
- **ATP/SMT reconstruction** (`metis`, `smt`, `meson`, `sledgehammer` results).
- **Induction/cases explosion** (too many cases or too-general induction).

### 2. Apply the targeted optimisation patterns below
- Start with the **Simplifier** section. It’s the most common performance culprit.

### 3. Re-check (and keep the improved proof)
- Don’t micro-optimise blindly: prefer proofs that are *predictable* and *small* over “clever” ones.

---

## 1) Simplifier performance (the biggest win zone)

### 1.1 Keep the global simp set *small and stable*
Only declare something `[simp]` if it is a genuine simplification rule (it reliably reduces terms and won’t blow things up).
- Good `[simp]`: eliminations like `xs @ [] = xs`, constructor injectivity/distinctness facts, trivial boolean rewrites.
- Dangerous as global `[simp]`: distributivity, expansion rules, rules that *increase* term size or cause exponential growth.
- Avoid “permanent toggles” of `[simp]` status for lemmas imported from a parent theory. Prefer local `simp add:` / `simp del:`.

### 1.2 Prefer *local* simp control over global declarations
Use `simp` modifiers to keep the proof predictable and fast:
- `simp add: thm1 thm2` — add a few rules locally
- `simp del: thmX` — remove an expensive rule locally
- `simp only: thm1 thm2 ...` — maximal predictability (great for performance + robustness)

Example (tight simp set):
~~~isabelle
lemma foo:
  "P x ⟹ f x = g x"
  by (simp only: f_def g_def)
~~~

### 1.3 Control how assumptions are used (avoid loops and huge work)
By default, assumptions participate in simp (they can become rewrite rules and can simplify each other).
Use these when assumptions are expensive or cause looping:
- `simp (no_asm)` — ignore assumptions entirely
- `simp (no_asm_simp)` — do not simplify assumptions, but use them to simplify the goal
- `simp (no_asm_use)` — simplify assumptions, but do not use them to rewrite each other / the goal

Typical fix:
~~~isabelle
apply (simp (no_asm))
~~~

### 1.4 Don’t expand definitions globally “because it works”
Definitions are for abstraction. A good optimisation (and maintainability) tactic:
- Prove abstract lemmas about the definition.
- Only unfold the definition at a few “interface” points.

Prefer:
~~~isabelle
by (simp add: my_def)
~~~
or
~~~isabelle
by (simp only: my_def)
~~~
over making `my_def` globally `[simp]` unless it is truly harmless.

### 1.5 Minimise splitting
Case splits are a classic hidden cost.
- Prefer letting `simp` do controlled splitting via `split:` when appropriate.
- Avoid manual `cases` if a `simp split:` can do it once and locally.

Example:
~~~isabelle
by (simp split: if_split)
~~~

### 1.6 If simp is slow: reduce the simp set *first*
If a proof does `simp add: ...` with a long list, try:
- remove rules that “reshape” terms (distributivity, associativity, commutativity) unless necessary
- replace broad rules with a small, goal-focused lemma
- use `simp only:` as a diagnostic: if `simp only:` is fast, your global simp set is the problem.

---

## 2) Classical reasoner performance (auto/blast/fastforce/force)

### 2.1 Choose the least powerful method that works
A rough cost order (cheap → expensive, varies by goal):
- `simp` / `simp_all`
- `auto`
- `fastforce`
- `blast`
- `force`
- `metis` / `smt` (can be very expensive depending on facts/goal)

Optimisation move:
- If `auto` is slow but the goal is mostly rewriting, switch to `simp`.
- If `blast`/`force` is slow, add the *right* intro/elim rules and use `auto`.

### 2.2 Keep the set of facts small
- Use `using` with a short fact list.
- Avoid `simp add:` with many theorems: prepackage a lemma instead.

Example:
~~~isabelle
using assms my_key_lemma
by (auto)
~~~

---

## 3) Optimising Sledgehammer / metis / smt proofs

### 3.1 Treat Sledgehammer as a *discovery tool*, not the final proof
Best practice:
1. Run Sledgehammer to find relevant facts.
2. **Minimise** the fact set.
3. Replace `metis` with `simp`/`auto`/`fastforce` if possible.
4. If you keep `metis`, keep the fact list tiny and stable.

### 3.2 Reduce the goal before calling ATP/SMT
Common pattern:
~~~isabelle
apply (simp add: ...)
apply (intro ...)
(* now the remaining goal is small *)
by (metis fact1 fact2)
~~~

### 3.3 Use specialised arithmetic methods where appropriate
For arithmetic-heavy goals, try:
- `linarith` (linear arithmetic)
- `arith` / `presburger` (depending on the fragment)
before escalating to `smt`.

---

## 4) Induction/cases: reduce explosion

### 4.1 Induct on the right variable, and generalise explicitly
- Induct on the “structural driver” (e.g. the list you recurse on).
- Use `arbitrary:` to strengthen the induction hypothesis when needed.

Template:
~~~isabelle
lemma foo:
  "… xs … ⟹ …"
proof (induction xs arbitrary: …)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  (* keep the step case small *)
  then show ?case
    by (simp add: …)
qed
~~~

### 4.2 Prefer one clean `simp_all` over repeated heavy automation
After induction, many goals can be discharged by:
- `simp_all` (with a small set of needed lemmas)
- or `auto` if there is genuine search.

---

## “Smells” that almost always indicate slowness/brittleness
- Very long `simp add:` lists (especially with algebraic reshaping rules).
- `metis` with dozens of facts.
- Frequent global toggling of `[simp]` / `[intro]` status.
- Many nested `cases` + big `simp` calls.
- Proofs that work only because the global simp set “happened to contain” something.

---

## Quick optimisation checklist (before you commit)
- [ ] Can the proof be turned into `by simp` / `by auto` with a *small* set of explicit lemmas?
- [ ] Are any newly added simp rules guaranteed to reduce terms?
- [ ] Are definition unfoldings local (via `simp add:` / `simp only:`)?
- [ ] Is any remaining `metis`/`smt` call operating on a small goal with few facts?
- [ ] Would this still work if the library simp set changes slightly? (avoid accidental reliance)