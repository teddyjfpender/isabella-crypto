---
name: isabelle-datatypes
description: Defining datatypes, recursive functions, and records in Isabelle/HOL
---

# Isabelle Datatypes

## Overview

This skill covers the definition of algebraic datatypes, recursive and non-recursive functions, and record types in Isabelle/HOL. Datatypes are fundamental for modeling structured data, while `primrec` and `fun` provide different mechanisms for defining functions over these types.

## Quick Use

- Read `references/datatypes.md` before answering questions about datatype definitions
- Choose between `primrec`, `fun`, and `function` based on recursion complexity
- Use records for structured data with named fields

## Response Checklist

- Datatype constructors have appropriate types
- Recursive functions cover all constructors
- `primrec` used for primitive recursion, `fun` for general pattern matching
- Record fields have clear names and types
- Termination is obvious or explicitly proven
- Pattern matching is exhaustive

## Example Requests

- "How do I define an algebraic datatype in Isabelle?"
- "What's the difference between primrec and fun?"
- "How do I define a recursive function over lists?"
- "How do I create a record type with update syntax?"
- "How do I prove termination for a complex recursive function?"
