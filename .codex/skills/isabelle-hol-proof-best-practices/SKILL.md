---
name: isabelle-hol-proof-best-practices
description: Write short, readable, and robust Isabelle/HOL proofs using structured Isar, controlled automation, and explicit local reasoning. Use when creating or refactoring `.thy` proofs, replacing brittle long `apply` scripts, turning Sledgehammer output into maintainable proofs, or reviewing proof quality for stability under library changes.
---

# Isabelle/HOL Proof Best Practices (Short, Robust, High-Quality Proofs)

## Goal
Write proofs that are:
- **Short** (minimal steps)
- **Readable** (future you can understand them quickly)
- **Robust** (do not depend on fragile global automation quirks)

## Guiding principle
Prefer *structured Isar proofs* with small, explicit steps, and use automation only in controlled ways.

---

## 1) Structure and readability

### 1.1 Prefer structured Isar over long `apply` scripts
- One-liner proofs are fine: `by simp`, `by auto`, `by (cases x) simp`.
- Avoid 15–50 line `apply` chains unless you are developing a proof interactively and will later refactor.

Good pattern:
~~~isabelle
lemma my_lemma:
  assumes A: "…"
  shows "…"
proof -
  have "…" using A by simp
  moreover have "…" by auto
  ultimately show ?thesis by simp
qed
~~~

### 1.2 Name assumptions and intermediate facts
- Use `assumes A: "..."` and refer to `A`.
- Use `have H: "..."` to avoid repeating proof search.

### 1.3 Keep goals small with helper lemmas
A single well-named helper lemma often replaces:
- huge `simp add:` lists
- repeated automation
- long `metis` proofs

Rule of thumb:
- If you pass > 5 facts into a method call, consider turning them into a lemma.

---

## 2) Controlled automation (short *and* stable)

### 2.1 Use the smallest method that works
Common progression:
1. `simp`
2. `auto`
3. `fastforce` / `blast` / `force`
4. `metis` / `smt`

Avoid jumping straight to #4 unless necessary.

### 2.2 Prefer local rule control (don’t mutate global simp/intro state)
Use local modifiers:
- `simp add: ...`
- `simp del: ...`
- `simp only: ...`

Avoid “surprise simp rules”:
- don’t globally add distributivity rules as `[simp]`
- don’t permanently toggle parent-theory simp attributes

### 2.3 Use “definition unfolding” deliberately
Good:
~~~isabelle
by (simp add: foo_def)
~~~

Even better for predictability:
~~~isabelle
by (simp only: foo_def bar_def)
~~~

Be careful with `unfold`:
- it affects **all subgoals**, which can be surprising.

---

## 3) Induction, cases, and modular proof shape

### 3.1 Standard induction template
~~~isabelle
lemma map_append:
  "map f (xs @ ys) = map f xs @ map f ys"
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  then show ?case by simp
qed
~~~

### 3.2 When induction needs strengthening
Use `arbitrary:` to generalise parameters.
~~~isabelle
proof (induction xs arbitrary: acc)
  …
qed
~~~

### 3.3 Use `cases` early when it reduces complexity
If the proof keeps branching later, do:
~~~isabelle
proof (cases x)
  case …
  …
qed
~~`

---

## 4) Calculational reasoning (keeps proofs short and clear)

### 4.1 Use `also` / `finally`
~~~isabelle
have "f x = …" by simp
also have "… = …" by simp
finally show "f x = …" .
~~~

This avoids manual rewriting steps and makes proof flow explicit.

---

## 5) Locales, contexts, and abstraction barriers

### 5.1 Use locales to avoid repeating assumptions
- Put “algebraic structure” assumptions in a `locale`.
- Prove generic lemmas inside the locale.
- Interpret the locale later.

This is both a proof *shortener* and a *performance* win (smaller contexts per lemma).

### 5.2 Prefer abstract lemmas over unfolding definitions everywhere
- Unfold once, prove stable facts, then work at the abstract level.

---

## 6) Sledgehammer best practice (quality, not just success)

### 6.1 Convert Sledgehammer output into maintainable proofs
- First: ask Sledgehammer for the relevant facts.
- Then: minimise and try to replace `metis` with `simp`/`auto`/small lemma.
- If keeping `metis`: keep the fact list tiny and avoid opaque “kitchen sink” proofs.

---

## Proof-quality checklist
- [ ] Is the proof readable without replaying the IDE state?
- [ ] Are the dependencies explicit (small `using` lists, small simp sets)?
- [ ] Are helper lemmas named and placed near the relevant definitions?
- [ ] Would a library simp-set change likely break this? (if yes: use `simp only:` or explicit lemmas)