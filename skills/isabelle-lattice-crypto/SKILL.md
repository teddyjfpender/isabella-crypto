---
name: isabelle-lattice-crypto
description: Lattice-based cryptography in Isabelle/HOL including LWE, SIS, RLWE, and security reductions
---

# Isabelle Lattice Cryptography

## Overview

This skill covers the formalization of lattice-based cryptographic primitives and their security in Isabelle/HOL. Lattice cryptography is believed to be secure against quantum computers and includes problems like Learning With Errors (LWE), Short Integer Solution (SIS), and their ring variants.

## Quick Use

- Read `references/lattice-crypto.md` before answering lattice cryptography questions
- Understand the distinction between computational and statistical security
- Be precise about probability distributions and error terms

## Response Checklist

- Correct problem definitions (LWE, SIS, RLWE, etc.)
- Security parameters properly tracked (n, q, error distribution)
- Reductions preserve security level
- Probability bounds correctly stated
- Ring variants use appropriate polynomial quotient rings
- Distinguish worst-case and average-case hardness

## Example Requests

- "How do I formalize the LWE assumption in Isabelle?"
- "What's the relationship between SIS and LWE?"
- "How do I define the RLWE problem with cyclotomic polynomials?"
- "How do I prove security reduction from lattice problems?"
- "How do I model the discrete Gaussian distribution?"
