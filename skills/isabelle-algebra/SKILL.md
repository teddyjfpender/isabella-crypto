---
name: isabelle-algebra
description: Algebraic structures in Isabelle/HOL including groups, rings, fields, polynomial rings, and quotient rings
---

# Isabelle Algebra

## Overview

This skill covers abstract algebra in Isabelle/HOL, focusing on algebraic structures essential for cryptography: groups, rings, fields, polynomial rings, and quotient constructions. These structures underpin both classical and lattice-based cryptography.

## Web References

| Topic | URL | Description |
|-------|-----|-------------|
| HOL-Algebra | https://isabelle.in.tum.de/library/HOL/HOL-Algebra/index.html | Abstract algebra library |
| Polynomials | https://isabelle.in.tum.de/library/HOL/HOL-Computational_Algebra/index.html | Polynomial rings |
| Number Theory | https://isabelle.in.tum.de/library/HOL/HOL-Number_Theory/index.html | Modular arithmetic |

## Quick Use

- Read `references/algebra.md` before answering algebraic structure questions
- Use web search to fetch the URLs above for specific algebra constructs
- Use HOL-Algebra for abstract structures with carriers
- Use type classes for concrete instantiations

## Response Checklist

- Correct algebraic axioms (associativity, identity, inverses)
- Distinguish between HOL-Algebra locales and type classes
- Ring homomorphisms preserve addition and multiplication
- Ideal and quotient ring constructions are correct
- Polynomial ring operations defined properly
- Field extensions and algebraic closures handled carefully

## Example Requests

- "How do I define a group in Isabelle?"
- "How do I work with polynomial rings in Isabelle?"
- "How do I construct a quotient ring Z[X]/(f(X))?"
- "How do I prove something is a ring homomorphism?"
- "How do I define finite fields in Isabelle?"
