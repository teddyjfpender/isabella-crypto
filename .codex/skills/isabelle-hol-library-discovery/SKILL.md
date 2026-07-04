---
name: isabelle-hol-library-discovery
description: Discover reusable Isabelle/HOL standard-library and AFP definitions, lemmas, and sessions before implementing new formalizations. Use when starting or refactoring `.thy` work, when theorem/constant names are unknown, when searches return no results due to missing imports, or when deciding whether to depend on an AFP entry.
---

# Finding Useful Isabelle/HOL Libraries (Standard + AFP)

## Goal
Stop reinventing the wheel:
- find existing definitions, lemmas, and proof tools already used in real developments
- identify which session/library to import instead of re-implementing

## Core idea
Library search in Isabelle is *context-sensitive*:
- You only find/see what your current session imports.
- Often the fastest fix is: import the right theory/session, then search again.

---

## 1) In-IDE discovery (fastest loop)

### 1.1 Use the Query panel (Isabelle/jEdit)
Use:
- **Find Theorems**
- **Find Constants**

These are usually faster than “manual grepping” when you don’t know names yet.

### 1.2 Use `find_theorems` with patterns
Patterns use `_` as a wildcard. Examples:
~~~isabelle
find_theorems "_ @ _ = _"
find_theorems "map _ (_ @ _)"
find_theorems name:"*_induct"
find_theorems "(_ :: 'a set) ⊆ _"
~~~

### 1.3 Use `find_consts` when you suspect a definition exists
Examples:
~~~isabelle
find_consts name:"fold"
find_consts name:"rbt"
find_consts name:"Mapping"
~~~

### 1.4 Jump to definitions
- Use IDE hyperlinks / ctrl-click on constants inside a well-typed term.
- This is the fastest way to discover “what theory does this live in?”.

---

## 2) Know the most useful standard sessions (distribution libraries)

### 2.1 Commonly high-value sessions to look into
(Use these when you need serious existing infrastructure.)

- **HOL-Library**: general-purpose library add-ons (data structures, lemmas, utilities).
- **HOL-Analysis**: real/metric/topological analysis, measure theory, integration.
- **HOL-Probability**: probability theory built on HOL-Analysis.
- **HOL-Computational_Algebra**: computational algebra, polynomials, primes, etc.
- **HOL-Number_Theory**: number theory libraries and tools.
- **HOL-Imperative_HOL**: imperative data structures & refinement framework components.
- **HOL-Eisbach**: proof method language for reusable tactics (Eisbach).
- **HOL-Hoare**, **HOL-IMP**: classic IMP language and Hoare logic material.

Tip: If you’re unsure whether “the thing you need” exists, import the most plausible session
(e.g. HOL-Analysis for limits/integration) and re-run your searches.

---

## 3) Use the online Session/Library browser (for “what exists”)
The official distribution provides a browsable session index with:
- theory lists
- theory dependencies
- sometimes documents/manuals per session

This is especially good for discovering “the right place” to import from.

---

## 4) The Archive of Formal Proofs (AFP): production-grade libraries

### 4.1 What AFP is (and why you should use it)
AFP is a large, refereed collection of Isabelle developments. It’s where many reusable
libraries live (beyond the standard distribution).

### 4.2 Practical workflow for AFP reuse
- Prefer importing the AFP session as-is (session dependency) rather than copying files.
- Build AFP (or the relevant sessions) so you get:
  - browser info
  - searchable theorems/constants in the IDE

### 4.3 How to pick “widely used” AFP entries quickly
Use the AFP “Most used entries” list as a first filter.
Examples of entries that often serve as foundations:
- List Index
- Collections Framework
- Deriving class instances for datatypes
- The Imperative Refinement Framework
- Regular Sets and Expressions
(Exact ranking changes over time; use the AFP stats page.)

---

## 5) Low-level search when all else fails (source grep)
If you *roughly* know a name:
- grep/ripgrep in `~~/src/HOL/` (distribution)
- grep/ripgrep in the AFP directory (once installed)

Use this to locate:
- definition sites
- lemma names
- theory import paths

---

## 6) Reuse checklist (before you implement something new)
- [ ] Did you search with `find_theorems` using structure patterns, not names?
- [ ] Did you search for constants/types with `find_consts`?
- [ ] Did you check whether you imported the right session?
- [ ] Did you check AFP for a library entry?
- [ ] If adopting AFP: can you depend on its session instead of copying code?