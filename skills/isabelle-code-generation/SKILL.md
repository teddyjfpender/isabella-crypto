---
name: isabelle-code-generation
description: Generating executable Haskell code from Isabelle/HOL specifications using export_code
---

# Isabelle Code Generation

## Overview

This skill covers Isabelle's code generation facility, which allows extracting executable code in Haskell, Scala, SML, and OCaml from verified Isabelle specifications. The focus is on Haskell code generation, including module naming, code equations, numeric types, and handling abstract types.

## Web References

When you need more information about code generation, fetch these sources:

| Topic | URL | Description |
|-------|-----|-------------|
| Code Generation | https://isabelle.in.tum.de/doc/codegen.pdf | Official code generation manual |
| Code Target Numeral | https://isabelle.in.tum.de/library/HOL/HOL-Library/Code_Target_Numeral.html | Efficient numerics theory |
| Code Library | https://isabelle.in.tum.de/library/HOL/HOL-Library/index.html | HOL-Library with code support |
| Haskell Platform | https://www.haskell.org/platform/ | Haskell installation for testing |

## Quick Use

- Read `references/codegen.md` before answering code generation questions
- Use web search to fetch the URLs above when you need export_code details
- Ensure all functions are defined with executable equations
- Use Code_Target_Numeral for efficient integer operations

## Response Checklist

- Functions are defined with computable equations (no underspecification)
- Code_Target_Numeral imported for efficient numerics
- Module names follow Haskell conventions (CamelCase)
- Abstract types properly instantiated or code-printed
- No partial functions without proper handling
- Generated code compiles without errors

## Example Requests

- "How do I export an Isabelle function to Haskell?"
- "How do I make integers efficient in generated code?"
- "How do I control module names in exported code?"
- "How do I handle abstract types in code generation?"
- "Why won't my function generate code?"
