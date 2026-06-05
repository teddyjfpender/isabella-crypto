# Confidential Transfers Production Readiness

Last updated: 2026-06-05

This ledger tracks the gap between the current SIS-note confidential-transfer
MVP and production confidential transfers. The current branch improves runtime
Fiat-Shamir handling, but production readiness still depends on proof,
parameter, ledger, protocol, implementation, CI, and audit work.

## Status Summary

| Item | Current Evidence | Production Gap | Acceptance Gate |
|---|---|---|---|
| 1. Transcript model | OCaml, Haskell, and TypeScript/js_of_ocaml use canonical signed-64-bit little-endian transcript encoding, domain tags, SHA3-256 counter-mode low-bit expansion, and vectors in `tests/fixtures/confidential-transcript-vectors.json`. | `Canon/ZK/Repeated_FS.thy` still treats `binary_fs_challenge` as a HOL proof abstraction. | CI regenerates vectors with no diff, backend parity tests pass, and a formal Fiat-Shamir security assumption/model is connected to the runtime transcript instantiation. |
| 2. Proof assumptions | `Canon/ZK/Confidential_Transaction.thy` names `balance_fs_extractor_correct`, `range_fs_extractor_correct`, `nullifier_fs_extractor_correct`, `balance_fs_hvzk_assumption`, `range_fs_hvzk_assumption`, and `nullifier_fs_hvzk_assumption`. `verified_opening_collision_yields_sis` links verified opening collisions to `binding_implies_sis`. | Extractors, simulators, rejection-sampling/FS-with-aborts analysis, and exact norm bounds remain assumptions or scaffolding. | Concrete extractor and simulator definitions replace the assumptions, soundness/HVZK theorem statements no longer depend on uninterpreted correctness predicates, and response bounds reduce to SIS binding under selected parameters. |
| 3. Parameters | `scripts/confidential_parameter_screen.py` writes `bench/data/confidential-parameter-screen.json` for `ct_sis_note_mvp_v0` and the separate RLWE/AHE research candidate. | The local screen is not a production security estimate; the external `estimator` module is not available in the recorded artifact. | External lattice-estimator and LaZer-style parameter-generation reports are checked in, selected security levels are documented, proof sizes are estimated, and realistic-dimension prover/verifier benchmarks pass regression thresholds. |
| 4. Ledger hash | `Canon/ZK/Authenticated_Merkle.thy` now defines domain-separated empty/leaf/internal-node encodings, an abstract Merkle hash, collision-resistance assumptions, and same-path membership soundness. `Canon/ZK/Authenticated_Ledger.thy` still marks executable `ledger_hash` as a scaffold. | The transaction verifier still uses the scaffold ledger; runtime Merkle hash vectors and full path/root generation tests are not wired. | Replace or wrap `ledger_hash` with the Merkle model, prove transaction membership soundness under collision resistance, and add implementation vectors for leaves, internal nodes, roots, and paths. |
| 5. Implementation boundary | Runtime transcript parity is pinned with SHA3 vectors. `make test-confidential-production` now builds OCaml/Haskell/TypeScript and runs transcript, audit, SDK-equivalence, parameter-screen, and 128-round benchmark checks. | Mirrors are still hand-maintained; CSPRNG sampling, canonical transaction serialization, numeric overflow review, side-channel review, and context-wide domain separation are incomplete. | Generated or vector-locked conformance covers every exported protocol primitive; all samplers use CSPRNGs; serializers reject non-canonical encodings; overflow/side-channel review is documented; replay/domain tags cover every protocol context. |
| 6. Launch architecture | The roadmap selects SIS note/nullifier MVP first and keeps RLWE/AHE as a separate `EncryptValid` / `SamePlaintext` / `TransferValid` / `NoiseBoundValid` layer. | The RLWE/AHE layer has no formal relations, parameters, estimator report, or benchmarks. | Launch scope explicitly excludes RLWE/AHE unless that layer gets independent proofs, parameter estimates, and benchmarks. |
| 7. Protocol/product completeness | Current theories cover notes, nullifiers, membership, balance, output range proofs, and semantic ledger-step preservation. | Note lifecycle, nullifier-set rules, reorg/replay handling, fees/change outputs, asset IDs, versioning, view/audit keys, wallet flow, and failure semantics are not specified. | A protocol specification fixes transaction formats, lifecycle rules, serialization/versioning, asset and fee semantics, wallet proof-generation flow, and consensus/indexer failure behavior. |
| 8. Audit and CI gates | CI builds formalization, OCaml, Haskell, TypeScript, and validation tests; validation now regenerates transcript vectors and the parameter-screen artifact. Optional LaZer comparison exists behind workflow dispatch. | Parameter reports, proof-size/performance regression thresholds, fuzz/negative mutation suites, full LaZer comparison, and external cryptography review are not mandatory gates. | CI enforces parameter-report freshness, proof-size/perf budgets, negative/fuzz proof mutations, optional-to-required LaZer comparison when available, and signed-off external crypto/implementation audits. |

## Current Stabilization Commands

Use this target before treating a confidential-transfer branch as review-ready:

```bash
make test-confidential-production
```

The target is production-facing, not a production proof. It is intended to
catch transcript drift, stale parameter-screen artifacts, backend parity
regressions, transaction-audit failures, and obvious 128-round performance
regressions while the formal and cryptographic blockers above are discharged.
