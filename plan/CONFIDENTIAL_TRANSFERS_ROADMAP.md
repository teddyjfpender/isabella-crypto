# Confidential Transfers Roadmap

Last updated: 2026-06-05

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
  Fiat-Shamir challenge policy.
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

- `Repeated_FS` no longer uses 8 rounds of `(seed + i) mod 2`. It now exposes a
  domain-separated transcript interface with 128 binary rounds. OCaml, Haskell,
  and TypeScript/js_of_ocaml runtime paths now instantiate the executable
  challenge policy with canonical signed-64-bit little-endian transcript
  encoding and SHA3-256 counter-mode low-bit expansion. Transcript vectors live
  in `tests/fixtures/confidential-transcript-vectors.json`.
- Balance, range, and nullifier proofs now have separate transcript domains and
  public transcript-field encoders.
- `Confidential_Transaction.thy` now states concrete extractor-correctness
  predicates for balance/range/nullifier soundness, explicit simulator
  assumptions for HVZK, and a theorem reducing verified opening collisions to
  SIS via `binding_implies_sis`. Balance, range, and nullifier response bounds
  now also have explicit binary-challenge lemmas for the exact margins used by
  later SIS reductions.
- `Authenticated_Ledger.thy` now marks `ledger_hash` as an execution scaffold
  and explicitly not production-ready. `Authenticated_Merkle.thy` provides the
  checked cryptographic target model for the replacement: canonical empty,
  leaf, and internal-node encodings, an abstract Merkle hash, and same-path
  membership soundness under collision resistance. Runtime SHA3-256 Merkle
  encoding vectors live in `tests/fixtures/confidential-merkle-vectors.json`,
  and the TypeScript, OCaml, and Haskell surfaces expose Merkle leaf/node/root
  and membership-path APIs checked by the SDK-equivalence harnesses.
  `Confidential_Transaction.thy` also now has a Merkle-backed transaction
  proof record, verifier, and transaction-level same-path membership soundness
  lemmas. OCaml, Haskell, and TypeScript expose matching Merkle transaction
  prover/verifier APIs; the SDK-equivalence harnesses now cover native Merkle
  transaction proving and verification for OCaml and Haskell, and TypeScript
  has a focused test for root/path tampering. The stable semantic ledger-step
  API now defaults to the Merkle-backed verifier, with algebraic scaffold
  calls exposed only through explicit compatibility names.
- `CONFIDENTIAL_TRANSFERS_PROTOCOL.md` now fixes the SIS-note MVP protocol
  contract: note lifecycle, nullifier rules, root/reorg behavior, fees/change,
  asset IDs, version contexts, wallet proof generation, and failure semantics.
- The runtime now pins the public SIS-note transaction context with canonical
  bytes and a SHA3-256 digest over protocol version, network ID, asset ID,
  ledger epoch, Merkle root, public fee, two input commitments, two output
  commitments, and two revealed nullifiers. The fixture lives in
  `tests/fixtures/confidential-transaction-vectors.json`, and OCaml, Haskell,
  and TypeScript expose matching `ct-transaction-context` /
  `transactionContextDigest` surfaces checked by the SDK-equivalence harnesses.

## Remaining Security Work

The formalization still needs these before production:

1. Replace the HOL proof abstraction for `binary_fs_challenge` with a
   security model that connects the SHA3-256 transcript instantiation to the
   Fiat-Shamir assumptions used by the proof system.
2. Replace extractor-correctness assumptions with concrete extractors and
   soundness proofs for balance, range, and nullifier proof objects.
3. Instantiate simulator assumptions with concrete simulators, rejection
   sampling/distribution bounds, and Fiat-Shamir-with-aborts analysis.
4. Tie balance soundness to SIS binding under the exact widened bounds used by
   aggregate randomness and responses.
5. Finish the Merkle-default migration in consensus/product callers, retire or
   quarantine the remaining algebraic scaffold compatibility APIs, broaden
   native transaction-level negative/fuzz conformance for Merkle proofs, and
   extend transaction membership soundness beyond same-path uniqueness.
6. Run external lattice-estimator and LaZer-style parameter generation for the
   selected dimensions.
7. Extend the pinned public transaction context into full canonical
   transaction/proof serialization, wallet request serialization, and
   consensus/indexer API contracts with non-canonical encoding rejection.

## Parameter Baseline

Repository-local screening is in
`bench/data/confidential-parameter-screen.json`, generated by:

```bash
python3 scripts/confidential_parameter_screen.py --out bench/data/confidential-parameter-screen.json
```

Selected baseline candidates:

| Candidate | Architecture | q | n1 | n2 | m | beta | gamma | range bits | FS bits |
|---|---|---:|---:|---:|---:|---:|---:|---:|---:|
| `ct_sis_note_mvp_v0` | SIS note commitment MVP | 8380417 | 1 | 1024 | 1024 | 65536 | 16777216 | 64 | 128 |
| `rlwe_ahe_transfer_research_v0` | RLWE/AHE research layer | 8380417 | 1 | 2048 | 2048 | 65536 | 16777216 | 64 | 128 |

The local screen is not a production security estimate. On this machine the
Python `estimator` module was not installed, so the external estimator gate is
still open.

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

Important validation caveats:

- `audit-confidential` now runs the 128-round semantic transaction/tampering
  fixture by default.
- `tests/src/confidential-merkle.test.ts` now runs a deterministic Merkle
  transaction mutation matrix covering root/path changes, spent nullifiers,
  nullifier responses, balance responses, range responses, and swapped proof
  components.
- `tests/src/confidential-transaction.test.ts` pins the canonical public
  transaction context preimage/digest and rejects malformed roots, negative
  fees, unsafe integers, and non-ASCII replay-context fields. This is not full
  transaction/proof serialization yet.
- `test-sdk-equivalence` now runs 128-round balance, range, nullifier,
  membership, transaction context, and transaction equivalence by default for
  both OCaml and Haskell.
- `scripts/bench_confidential_balance_128.mjs` now completes and writes
  `bench/data/confidential-balance-128.json`. On the June 5, 2026 local run
  with toy dimensions and SHA3-256 transcript hashing, 128-round balance
  proving had a 3.731042 ms median and verification had a 3.616708 ms median.
  The earlier multi-minute behavior was an executable-model bug: the
  prover/verifier hot paths repeatedly evaluated the brute-force SIS
  key-separation predicate. That predicate remains part of the stronger
  security relations, but the executable proof paths now check only
  parameter/key dimensions.
- `scripts/bench_confidential_balance_realistic.mjs` now writes
  `bench/data/confidential-balance-realistic.json`. On the June 5, 2026 local
  run using the `ct_sis_note_mvp_v0` dimensions, a 128-round balance proof had
  a 3.144791583 s proving time, a 3.27841275 s verification time, and a
  972347-byte JSON proof object. This is a structured-key runtime benchmark,
  not a production lattice security estimate.
- `scripts/check_confidential_bench_budgets.mjs` enforces current CI ceilings
  for the 128-round toy benchmark, the realistic-dimension benchmark, and the
  realistic JSON proof size. The ceilings are deliberately wider than local
  medians so CI catches regressions without pretending to be a security
  estimate.
