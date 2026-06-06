# Confidential Transfers Roadmap

Last updated: 2026-06-06

## Current Branch State

The confidential-transfer source changes are checkpointed in git. The remaining
untracked files are local Codex skill folders, not confidential-transfer source
changes.

The current confidential-transfer stack is an SIS note-commitment MVP:

- `Canon/ZK/Confidential_Balance.thy`: repeated Sigma-style balance proof over
  the aggregate input/output commitment.
- `Canon/ZK/Confidential_Range.thy`: amount range proof via committed bits and
  complement-bit residual checks.
- `Canon/ZK/Confidential_Transaction.thy`: nullifiers, authenticated membership,
  balance, range proofs, and semantic ledger-step preservation.
- `Canon/ZK/Repeated_FS.thy`: shared 128-round, domain-separated binary
  Fiat-Shamir challenge policy, a proof-side cryptographic challenge oracle
  with runtime SHA3 export bindings, and an explicit forked binary challenge
  schedule model for rewinding-style soundness statements.
- `Canon/ZK/Authenticated_Merkle.thy`: production-target Merkle/hash model with
  canonical encodings and collision-resistance membership soundness lemmas.
- `Canon/ZK/Authenticated_Ledger.thy`: executable membership scaffold.

This is still not production confidential transfers.

The production-readiness ledger for the eight launch blockers is maintained in
`plan/CONFIDENTIAL_TRANSFERS_PRODUCTION_READINESS.md`.

The launch-scope protocol/product contract is maintained in
`plan/CONFIDENTIAL_TRANSFERS_PROTOCOL.md`.

## Architecture Decision

Keep the note/SIS path as the MVP. It is already wired through Isabelle,
Haskell, OCaml, wasm/TypeScript, audit tests, and deterministic benchmarks. The
next production-facing milestone is to harden this path rather than switch the
core architecture midstream.

The RLWE/AHE design from `idea.md` should become a separate relation layer:

- `EncryptValid`: prove a ciphertext delta is a valid encryption of a hidden
  plaintext with bounded randomness/noise.
- `SamePlaintext`: prove two ciphertext relations encode the same hidden value.
- `TransferValid`: prove sender/recipient encrypted deltas conserve a hidden
  transfer value.
- `NoiseBoundValid`: prove accumulated noise remains inside decryption bounds.

That layer should import the note/SIS MVP where useful, but it should not
replace the MVP until the RLWE/AHE relations, parameters, estimators, and
benchmarks are independently checked.

## Limitations Addressed In This Pass

- `Repeated_FS.thy` no longer defines the deterministic `transcript_mix`
  scaffold or the old 8 rounds of `(seed + i) mod 2`. The proof theory now
  exposes `binary_fs_challenge` as an abstract cryptographic challenge oracle
  with only the binary-output contract used by the proofs. Isabelle code export
  is bound to the OCaml and Haskell SHA3-256 counter-mode runtime
  implementations, and the TypeScript/js_of_ocaml path uses the same canonical
  signed-64-bit little-endian transcript encoding. Transcript vectors live in
  `tests/fixtures/confidential-transcript-vectors.json`.
- Balance, range, and nullifier proofs now have separate transcript domains and
  public transcript-field encoders.
- `tests/fixtures/confidential-domain-registry.json` records the active
  Fiat-Shamir, Merkle, and transaction-envelope domains/tags. The
  `scripts/check_confidential_domain_registry.py` gate checks uniqueness and
  fixture/source agreement across OCaml, Haskell, TypeScript, and generators.
- `Confidential_Transaction.thy` now states concrete extractor-correctness
  predicates for balance/range/nullifier soundness, explicit simulator
  assumptions for HVZK, narrower programmed-schedule HVZK assumptions, and a
  theorem reducing verified opening collisions to SIS via
  `binding_implies_sis`. Balance, range, and nullifier response bounds now
  also have explicit binary-challenge lemmas for the exact margins used by
  later SIS reductions.
- `Repeated_FS.thy` now defines valid and forked binary challenge schedules.
  `Confidential_Balance.thy`, `Confidential_Range.thy`, and
  `Confidential_Transaction.thy` define named scheduled-fork extractors and
  prove extraction lemmas for balance, range amount, range bit-pair, and
  nullifier rounds. These lemmas show that two accepting scheduled transcripts
  with the same announcements and a forked binary challenge round yield
  bounded algebraic openings. `Confidential_Transaction.thy` now also states
  narrower scheduled-forking assumptions for the Fiat-Shamir verifier and
  proves that those assumptions imply concrete extractor outputs for accepted
  balance, range residual, and nullifier proofs. They deliberately do not prove
  the ROM/forking lemma that obtains such forks from the deterministic SHA3
  Fiat-Shamir verifier.
- Balance, range, and nullifier proofs now also have concrete scheduled
  simulators. The scheduled simulator lemmas prove that programmed binary
  challenge schedules and valid simulated responses verify for the generated
  announcements. The follow-on bridge lemmas prove that the deterministic
  Fiat-Shamir verifier accepts those scheduled simulator proofs when the
  transcript-derived challenge list equals the programmed schedule. This is
  the algebraic simulator core plus an explicit challenge-match bridge only;
  it does not prove distributional HVZK, rejection-sampling bounds, or
  Fiat-Shamir programmability. `Confidential_Transaction.thy` now packages
  this boundary as `balance_fs_programmed_hvzk_assumption`,
  `range_fs_programmed_hvzk_assumption`, and
  `nullifier_fs_programmed_hvzk_assumption`, then proves verifier acceptance
  and the stated indistinguishability predicate from those narrower
  assumptions.
- `Authenticated_Ledger.thy` now marks `ledger_hash` as an execution scaffold
  and explicitly not production-ready. `Authenticated_Merkle.thy` provides the
  checked cryptographic target model for the replacement: canonical empty,
  leaf, and internal-node encodings, an abstract Merkle hash, same-path
  membership soundness, and same-direction membership soundness under collision
  resistance. Runtime SHA3-256 Merkle encoding vectors live in
  `tests/fixtures/confidential-merkle-vectors.json`, and the TypeScript, OCaml,
  and Haskell surfaces expose Merkle leaf/node/root and membership-path APIs
  checked by the SDK-equivalence harnesses.
  `Confidential_Transaction.thy` also now has a Merkle-backed transaction
  proof record, verifier, transaction-level same-path membership soundness
  lemmas, and same-root/same-index/same-depth input membership soundness for
  both fee and non-fee Merkle transaction verifiers. It now also defines a
  depth-tagged `merkle_accepted_root`, root-scoped membership verifier,
  root-scoped fee and non-fee transaction verifiers, refinement lemmas back to
  the digest-only verifier, and same-accepted-root/same-index soundness
  theorems without requiring callers to provide a separate depth equality
  assumption. OCaml, Haskell, and
  TypeScript expose matching Merkle transaction prover/verifier APIs; the
  SDK-equivalence harnesses now cover native Merkle transaction proving and
  verification for OCaml and Haskell, and TypeScript has a focused test for
  root/path tampering. Stable semantic/ledger-step APIs now default to the
  Merkle-backed verifier, with algebraic scaffold calls exposed only through
  explicit scaffold names.
- `CONFIDENTIAL_TRANSFERS_PROTOCOL.md` now fixes the SIS-note MVP protocol
  contract: note lifecycle, nullifier rules, root/reorg behavior, fees/change,
  asset IDs, version contexts, wallet proof generation, and failure semantics.
- The runtime now pins the public SIS-note transaction context with canonical
  bytes and a SHA3-256 digest over protocol version, network ID, asset ID,
  ledger epoch, depth-tagged Merkle root, public fee, two input commitments, two
  output commitments, and two revealed nullifiers. The fixture lives in
  `tests/fixtures/confidential-transaction-vectors.json`, and OCaml, Haskell,
  and TypeScript expose matching `ct-transaction-context` /
  `transactionContextDigest` surfaces checked by the SDK-equivalence harnesses.
  That fixture also pins canonical Merkle-proof and envelope preimage/digest
  bytes under separate `merkleProof` and `envelope` transaction tags. TypeScript,
  OCaml, and Haskell expose proof/envelope digest APIs, and the native
  SDK-equivalence validators check those digests against the pinned vectors.
  The native transaction context, Merkle proof digest, raw Merkle verifier,
  Merkle envelope digest, wallet-request digest, and Merkle envelope verifier
  commands now reject non-canonical numeric/list spellings such as leading
  zeros, plus signs, and negative zero instead of normalizing them before
  hashing or policy checks.
  The same fixture now pins wallet proof request preimage/digest bytes under a
  separate `walletProofRequest` tag. That request binds the canonical public
  transaction context digest, a sorted duplicate-free accepted-root window of
  `(digest, depth)` pairs containing the context root, and a sorted duplicate-free spent-nullifier
  snapshot that must not contain either revealed transaction nullifier.
  TypeScript, OCaml, and Haskell expose matching wallet-request digest APIs
  checked by the SDK-equivalence harnesses, including native rejection checks
  for malformed accepted-root windows and spent-nullifier snapshots.
  TypeScript exposes `fsVerifyMerkleEnvelope`, and OCaml/Haskell expose a
  matching `ct-verify-merkle-envelope` command, so callers can verify the
  canonical context digest, expected protocol version, network, asset, epoch,
  depth-tagged root, fee policy, and explicit Merkle transaction proof as one
  step. The TypeScript envelope verifier rejects incomplete launch policies
  before falling back to the lower-level policy matcher; the native verifier
  commands require the same expected fields on the command line and parse the
  proof's Merkle membership fields instead of deriving membership from the
  supplied ledger. The SDK-equivalence validators exercise the TS and native
  envelope gates with native `ct-transaction-context` digests and native Merkle
  transaction proofs, including stale-digest, wrong-policy, root-depth policy
  mismatch, fee-policy mismatch, context-root/proof-root mismatch,
  context-root-depth/proof-path-depth mismatch, and the shared deterministic
  proof-mutation matrix. The matrix now covers both input membership
  roots/siblings/directions/indices, extended membership paths, spent nullifier
  snapshots, both nullifier proofs, both range proofs, the balance proof,
  swapped proof components, and verifier-root mismatches.
  `Confidential_Balance.thy` now defines public amount
  commitments and `fee_balance_commitment`; `Confidential_Transaction.thy`
  exposes `transaction_relation_fee` and `transaction_fs_verify_merkle_fee`.
  TypeScript exposes `fsProveMerkleWithFee` / `fsVerifyMerkleWithFee`, and the
  OCaml/Haskell envelope commands verify nonzero public-fee proofs by checking
  the balance proof against `balance_commitment - commit([fee], 0)`.
- OCaml and Haskell expose explicit `ct-prove-scaffold`,
  `ct-verify-scaffold`, `ct-verify-bench-scaffold`, and
  `ct-ledger-step-verify-scaffold` commands for the algebraic ledger path. The
  ambiguous native aliases `ct-prove`, `ct-verify`, `ct-verify-bench`, and
  `ct-ledger-step-verify` have been removed. `scripts/check_confidential_scaffold_quarantine.py`
  is wired into CI and `make test-confidential-production`; it rejects
  production-facing uses of those legacy names, verifies the native CLIs do not
  dispatch them, and checks the local TypeScript CLI helper has no ambiguous
  scaffold aliases.

## Remaining Security Work

The formalization still needs these before production:

1. Develop the security model that connects the proof-side
   `binary_fs_challenge` oracle and the SHA3-256 transcript instantiation to
   the Fiat-Shamir assumptions used by the proof system.
2. Connect the deterministic SHA3 Fiat-Shamir verifier to the scheduled-fork
   extraction model with a ROM/forking theorem, then replace the remaining
   extractor-correctness assumptions with full proof-object soundness for
   balance, range, and nullifier proofs.
3. Prove or assume the programmable-transcript theorem that realizes the
   challenge-match condition for the scheduled simulators, then finish
   FS-level HVZK with rejection-sampling/distribution bounds and
   Fiat-Shamir-with-aborts analysis.
4. Tie balance soundness to SIS binding under the exact widened bounds used by
   aggregate randomness and responses.
5. Finish the Merkle-default migration in consensus/product callers, retire the
   remaining algebraic scaffold compatibility APIs, replace the
   hand-maintained native transaction digest/envelope command wrappers with
   generated or vector-locked surfaces, broaden native transaction-level
   negative/fuzz conformance for Merkle proofs, and extend the runtime
   depth-tagged accepted-root model into consensus/indexer API contracts.
6. Run external lattice-estimator and LaZer-style parameter generation for the
   selected dimensions.
7. Extend the pinned depth-tagged wallet proof request serialization into
   consensus/indexer API contracts with non-canonical encoding rejection.
8. Extend fee-aware proof support from the envelope verifier into the remaining
   consensus/indexer and wallet APIs, including change-output policy and
   negative tests for every failure class.

## Parameter Baseline

Repository-local screening is in
`bench/data/confidential-parameter-screen.json`, generated by:

```bash
python3 scripts/confidential_parameter_screen.py --out bench/data/confidential-parameter-screen.json
```

External estimator and LaZer parameter evidence must be attached as structured
JSON report collections, keyed by candidate:

```bash
python3 scripts/confidential_parameter_screen.py \
  --external-estimator-report path/to/estimator-reports.json \
  --lazer-parameter-report path/to/lazer-parameter-reports.json \
  --out bench/data/confidential-parameter-screen.json
```

`scripts/check_confidential_parameter_readiness.py` now validates the estimator
probe, external-estimator report fields, LaZer parameter-generation report
fields, candidate target-security floors, exact parameter-snapshot equality, and
the arithmetic behind each formal proof-margin modulus requirement before any
candidate can be marked production-ready. The regression gate
`scripts/check_confidential_parameter_readiness_regressions.py` checks that
below-target estimator evidence and mismatched estimator/LaZer parameter
snapshots are rejected.

Selected baseline candidates:

| Candidate | Architecture | q | n1 | n2 | m | beta | gamma | range bits | FS bits | target bits |
|---|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| `ct_sis_note_mvp_v0` | SIS note commitment MVP | 8380417 | 1 | 1024 | 1024 | 65536 | 16777216 | 64 | 128 | 128 |
| `rlwe_ahe_transfer_research_v0` | RLWE/AHE research layer | 8380417 | 1 | 2048 | 2048 | 65536 | 16777216 | 64 | 128 | 128 |

The local screen is not a production security estimate. The generated artifact
now records the exact estimator import probe. On this machine the Python
`estimator`, `lattice_estimator`, and `lwe_estimator` modules were not
installed, so the external estimator gate is still open. It also records exact
formal modulus requirements: for `ct_sis_note_mvp_v0`, the current modulus is
`q = 8380417` (23 bits), while the proof-margin aggregate requires an 82-bit
minimum modulus, dominated by the `sis_range_amount_residual_vs_honest` bound.
That gap is surfaced as the machine-readable blocker
`formal_minimum_q_bits_required:82`.

## Validation Plan

Fast checks:

```bash
./scripts/check_formalization.sh
make build-cool
cd tests && bun run audit-confidential
make test-sdk-equivalence
make test-validation
```

Production-facing confidential-transfer gate:

```bash
make test-confidential-production
```

Strict launch/release parameter gate. This intentionally fails while the
current report is blocked:

```bash
make check-confidential-production-readiness
```

Benchmark checks:

```bash
make bench-typescript-confidential
make bench-confidential-verify
make bench-confidential-realistic
node scripts/generate_confidential_transaction_vectors.mjs
node scripts/check_confidential_bench_budgets.mjs
```

The benchmark harnesses still use deterministic fixtures. The realistic balance
benchmark now uses the full `ct_sis_note_mvp_v0` dimensions, but it uses a
structured deterministic commitment key and is not a security estimate.

## Validation Results From This Pass

Completed:

- `./scripts/check_formalization.sh`
- `isabelle build -d Canon Canon_ZK`
- `make build-cool`
- `cd tests && bun run audit-confidential`
- `make test-sdk-equivalence`
- `make test-validation`
- `node scripts/bench_confidential_balance_128.mjs`
- `node scripts/bench_confidential_balance_realistic.mjs`
- `node scripts/generate_confidential_transaction_vectors.mjs`
- `cd tests && bun test confidential-transaction`
- `node scripts/check_confidential_bench_budgets.mjs`
- `python3 scripts/confidential_parameter_screen.py --out bench/data/confidential-parameter-screen.json`
- `python3 scripts/check_confidential_domain_registry.py`

Important validation caveats:

- `audit-confidential` now runs the 128-round semantic transaction/tampering
  fixture by default.
- `tests/src/confidential-merkle.test.ts` and the OCaml/Haskell
  SDK-equivalence validators now run the same deterministic Merkle transaction
  mutation matrix through TypeScript and native `ct-verify-merkle-envelope`.
  The matrix covers both input membership roots/siblings/directions/indices,
  extended membership paths, spent nullifiers, both nullifier responses, the
  balance response, both range responses, swapped proof components, and
  verifier-root mismatches.
- `tests/src/confidential-transaction.test.ts` pins the canonical public
  transaction context preimage/digest, TypeScript canonical Merkle-proof
  preimage/digest, TypeScript canonical envelope preimage/digest, and
  TypeScript canonical wallet proof request preimage/digest. It rejects
  malformed roots, negative fees, unsafe integers, non-ASCII replay-context
  fields, empty/duplicate/unsorted accepted-root windows, non-canonical
  spent-nullifier snapshots, already-spent requested nullifiers, and duplicate
  requested nullifiers. It also checks that proof/envelope/request digests
  change under proof, public-context, root-window, or spent-snapshot mutation.
  It also checks that the TypeScript Merkle envelope verifier rejects stale
  context digests, wrong network/asset policy, fee-policy mismatches, and
  swapped proof components, and accepts a valid nonzero public-fee proof.
  OCaml/Haskell SDK-equivalence validation now checks native
  proof/envelope/wallet-request digest parity against the pinned vectors,
  rejects malformed native wallet requests, rejects non-canonical and
  out-of-range native transaction encodings on production-facing commands,
  and verifies explicit
  Merkle proof rejection through native envelope commands; consensus/indexer
  serialization remains open.
- `test-sdk-equivalence` now runs 128-round balance, range, nullifier,
  membership, transaction context, transaction equivalence, and Merkle envelope
  acceptance/rejection against native context digests and Merkle proofs through
  `ct-verify-merkle-envelope` by default for both OCaml and Haskell.
- `scripts/bench_confidential_balance_128.mjs` now completes and writes
  `bench/data/confidential-balance-128.json`. On the June 5, 2026 local run
  with toy dimensions and SHA3-256 transcript hashing, 128-round balance
  proving had a 4.001 ms median and verification had a 3.950209 ms median.
  The earlier multi-minute behavior was an executable-model bug: the
  prover/verifier hot paths repeatedly evaluated the brute-force SIS
  key-separation predicate. That predicate remains part of the stronger
  security relations, but the executable proof paths now check only
  parameter/key dimensions.
- `scripts/bench_confidential_balance_realistic.mjs` now writes
  `bench/data/confidential-balance-realistic.json`. On the June 5, 2026 local
  run using the `ct_sis_note_mvp_v0` dimensions, a 128-round balance proof had
  a 0.771455667 s proving time, a 0.724763333 s verification time, and a
  972347-byte JSON proof object. This is a structured-key runtime benchmark,
  not a production lattice security estimate.
- `scripts/check_confidential_bench_budgets.mjs` enforces current CI ceilings
  for the 128-round toy benchmark, the realistic-dimension benchmark, and the
  realistic JSON proof size. The ceilings are deliberately wider than local
  medians so CI catches regressions without pretending to be a security
  estimate.
