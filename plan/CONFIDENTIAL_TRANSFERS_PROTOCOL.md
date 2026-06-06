# Confidential Transfers Protocol Specification

Last updated: 2026-06-05

This is the launch-scope protocol specification for the SIS note/nullifier MVP.
It is a product and integration contract for the formal proof slices. It does
not make the system production-ready by itself; the proof, parameter, ledger,
implementation, and audit gates in `CONFIDENTIAL_TRANSFERS_PRODUCTION_READINESS.md`
still apply.

## Launch Architecture

The launch architecture is the SIS note/nullifier path:

- Notes are SIS commitments to `(asset_id, amount, owner/view metadata,
  randomness)`.
- Spending a note reveals a deterministic nullifier derived from the note
  opening and a nullifier key.
- Transactions prove input membership, input nullifier validity, output range
  validity, and zero balance for the selected asset.
- The RLWE/AHE design is a separate future layer with `EncryptValid`,
  `SamePlaintext`, `TransferValid`, and `NoiseBoundValid` relations. It is not
  part of the MVP unless it receives independent proofs, parameter estimates,
  benchmarks, and audit review.

## Versioned Contexts

Every protocol object carries:

- `protocol_id = "ISABELLA-CT-SIS-NOTE"`
- `protocol_version = 1`
- `network_id`
- `asset_id`
- `ledger_epoch`
- `statement_domain`

Domain separation is mandatory for:

- Fiat-Shamir transcripts
- Merkle leaf, empty-node, and internal-node hashes
- Note commitments
- Nullifier derivation
- Wallet-generated proof requests
- Audit/view-key disclosures

Unknown versions, unsupported domains, or mismatched network/asset IDs are
verification failures.

## Note Lifecycle

1. Deposit or mint creates an unspent note commitment.
2. The note is appended to the note commitment tree.
3. Wallets track note openings and the authenticated path for each spendable
   note.
4. Spending consumes one or more input notes by revealing nullifiers and proving
   membership against an accepted `(digest, depth)` Merkle root.
5. Spending creates output notes, including change notes when needed.
6. A note is spendable only while its nullifier is absent from the accepted
   nullifier set and its membership `(digest, depth)` root is inside the accepted root window.

Wallets must treat missing openings, stale paths, unsupported roots, duplicated
nullifiers, malformed proofs, and asset mismatches as local proof-generation
failures.

## Nullifier Set Rules

- Nullifiers are unique per spendable note opening and nullifier key.
- A transaction is invalid if any revealed nullifier is already in the accepted
  nullifier set.
- A transaction is invalid if it reveals duplicate nullifiers internally.
- Reorg handling must roll nullifier-set updates back with the corresponding
  ledger root.
- Indexers must expose nullifier inclusion and root-window state atomically.

The consensus or settlement layer must define the finality depth after which a
root and nullifier-set update are considered irreversible for wallet UX.

## Membership Roots And Reorgs

Verifiers accept membership proofs only against roots in the root window:

- `latest_finalized_root`
- optional recent unfinalized roots for latency-sensitive flows
- root expiration height or epoch

If a root leaves the window before a transaction lands, the transaction must be
rebuilt with fresh paths. Wallets must not silently reuse old paths across
network IDs, asset IDs, or protocol versions.

## Fees, Change Outputs, And Assets

The MVP uses one asset per confidential transaction statement.

Balance equation:

```text
sum(inputs) = sum(outputs) + public_fee
```

Rules:

- `asset_id` is public and bound into all transaction statements.
- `public_fee` is public and non-negative.
- Change is represented as a normal output note.
- Empty change is encoded by omitting the output, not by creating malformed
  zero notes.
- Cross-asset transfers require separate statements or a future multi-asset
  relation; they are not part of the MVP.

The formal 2-in/2-out slices are the current proof target. Production wallets
may build fixed-arity transactions by padding with explicit dummy notes only
after dummy-note semantics are specified and tested.

## Transaction Object

A serialized transaction contains:

- Header: protocol ID, version, network ID, asset ID, ledger epoch, accepted
  membership root, public fee.
- Inputs: input commitments, membership paths, revealed nullifiers.
- Outputs: output commitments and encrypted note payloads for recipients.
- Proofs: balance proof, output range proofs, nullifier proofs, membership
  proofs, and any future protocol-extension proofs.
- Optional disclosure data: view/audit payloads, policy IDs, or encrypted memo
  fields.

Canonical serialization is required. Duplicate fields, non-canonical integer
encodings, out-of-range values, unsupported proof shapes, or trailing bytes are
verification failures.

## View And Audit Keys

View/audit keys are optional in the MVP, but the transaction format reserves
domain-separated payload slots for them.

If enabled, a view key may reveal:

- asset ID
- amount
- recipient metadata
- note commitment opening material needed for wallet recovery

Audit disclosures must be explicitly bound to a policy ID and must not alter the
balance, range, membership, or nullifier statement being verified.

## Wallet Proof Generation Flow

1. Select notes for the target asset and fee.
2. Fetch fresh membership paths for an accepted root.
3. Construct recipient and change note openings.
4. Derive nullifiers for inputs.
5. Build the public statement and bind protocol/network/asset/root/fee contexts.
   The MVP wallet proof request serialization commits to the canonical public
   context digest, a sorted duplicate-free accepted-root window of `(digest,
   depth)` pairs containing the selected root, and a sorted duplicate-free spent-nullifier snapshot that does
   not already contain either requested nullifier.
6. Sample masks with a CSPRNG.
7. Generate balance, nullifier, membership, and output range proofs.
8. Verify the full transaction locally before broadcast.
9. Store output openings, encrypted note payloads, and root/nullifier metadata.

Wallets must fail closed if any proof or local verification step fails.

## Failure Semantics

Verification returns failure for:

- unsupported protocol version or domain
- mismatched network, asset, root, or fee context
- malformed canonical serialization
- expired or unknown membership root
- invalid membership path
- duplicated or already-spent nullifier
- invalid balance proof
- invalid range proof
- invalid nullifier proof
- output amount outside the selected range
- numeric overflow or integer outside canonical bounds
- unsupported extension field

No verifier path may silently coerce a malformed value into a valid one.

## Production Gates

Before launch, this specification must be backed by:

- formal statement definitions for every serialized field
- runtime canonical serialization vectors, including wallet proof requests
- Merkle leaf/node/root vectors
- negative mutation tests for every failure class above
- parameter and proof-size reports
- realistic-dimension proving and verification benchmarks
- external cryptography and implementation review
