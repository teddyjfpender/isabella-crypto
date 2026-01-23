---
name: isabelle-proofs
description: Proof techniques in Isabelle/HOL including auto, simp, blast, induction, and case analysis
---

# Isabelle Proofs

## Overview

This skill covers the various proof methods and tactics available in Isabelle/HOL. Understanding when to use different proof methods like `auto`, `simp`, `blast`, and when to apply induction or case analysis is crucial for efficient theorem proving.

## Quick Use

- Read `references/proofs.md` before answering questions about proof strategies
- Start with simpler methods (simp, auto) before trying more powerful ones
- Use induction for recursive datatypes and properties

## Response Checklist

- Appropriate proof method chosen for the goal
- Induction variable correctly identified for recursive proofs
- Case analysis covers all constructors/possibilities
- Auxiliary lemmas suggested when main proof is complex
- Isar proofs are well-structured with clear intermediate steps
- Simp rules and introduction/elimination rules used appropriately

## Example Requests

- "What's the difference between auto and simp?"
- "How do I prove a property by induction over lists?"
- "When should I use blast vs auto?"
- "How do I structure a proof using Isar?"
- "How do I debug a failing proof?"
