#!/usr/bin/env python3
"""Check confidential-transfer domain separation constants.

The registry is the audit surface for production-facing transcript/hash
namespaces. This checker compares it against generated fixtures and the
hand-maintained OCaml/Haskell/TypeScript runtime constants.
"""

from __future__ import annotations

import json
import re
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
REGISTRY = ROOT / "tests/fixtures/confidential-domain-registry.json"
TRANSCRIPT_VECTORS = ROOT / "tests/fixtures/confidential-transcript-vectors.json"
MERKLE_VECTORS = ROOT / "tests/fixtures/confidential-merkle-vectors.json"
TRANSACTION_VECTORS = ROOT / "tests/fixtures/confidential-transaction-vectors.json"
BIGNUM_TRANSACTION_VECTORS = ROOT / "tests/fixtures/confidential-bignum-transaction-vectors.json"


def fail(message: str) -> None:
    raise SystemExit(message)


def load_json(path: Path) -> dict[str, Any]:
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except FileNotFoundError:
        fail(f"missing JSON file: {path.relative_to(ROOT)}")
    except json.JSONDecodeError as exc:
        fail(f"invalid JSON in {path.relative_to(ROOT)}: {exc}")
    if not isinstance(value, dict):
        fail(f"{path.relative_to(ROOT)} must contain a JSON object")
    return value


def require_object(value: Any, label: str) -> dict[str, Any]:
    if not isinstance(value, dict):
        fail(f"{label} must be an object")
    return value


def require_string(value: Any, label: str) -> str:
    if not isinstance(value, str) or not value:
        fail(f"{label} must be a non-empty string")
    if any(ord(ch) < 0x20 or ord(ch) > 0x7e for ch in value):
        fail(f"{label} must be printable ASCII")
    return value


def require_int(value: Any, label: str) -> int:
    if not isinstance(value, int) or isinstance(value, bool):
        fail(f"{label} must be an integer")
    if value < 0 or value > 9_007_199_254_740_991:
        fail(f"{label} must be a non-negative safe protocol integer")
    return value


def require_unique_values(values: dict[str, int], label: str) -> None:
    seen: dict[int, str] = {}
    for name, value in values.items():
        previous = seen.get(value)
        if previous is not None:
            fail(f"{label} duplicates value {value}: {previous} and {name}")
        seen[value] = name


def read_text(path: str) -> str:
    full_path = ROOT / path
    try:
        return full_path.read_text(encoding="utf-8")
    except FileNotFoundError:
        fail(f"missing source file: {path}")


def require_pattern(path: str, pattern: str, label: str) -> None:
    if re.search(pattern, read_text(path), flags=re.MULTILINE) is None:
        fail(f"{path} is missing {label}")


def forbid_pattern(path: str, pattern: str, label: str) -> None:
    if re.search(pattern, read_text(path), flags=re.MULTILINE) is not None:
        fail(f"{path} must not contain {label}")


def check_registry_shape(registry: dict[str, Any]) -> dict[str, dict[str, Any]]:
    if require_int(registry.get("version"), "version") != 1:
        fail("version must be 1")
    encoding = require_string(registry.get("integerEncoding"), "integerEncoding")
    if encoding != "namespace-specific":
        fail("integerEncoding must be namespace-specific")

    namespaces = require_object(registry.get("namespaces"), "namespaces")
    required = {"fiatShamir", "merkle", "merkleBignum", "transaction", "transactionBignum"}
    missing = required - set(namespaces)
    if missing:
        fail(f"missing namespace(s): {sorted(missing)}")

    dsts: dict[str, str] = {}
    for namespace_name, raw_namespace in namespaces.items():
        namespace = require_object(raw_namespace, f"namespaces.{namespace_name}")
        dst = require_string(namespace.get("dst"), f"namespaces.{namespace_name}.dst")
        if dst in dsts:
            fail(f"duplicate DST {dst}: {dsts[dst]} and {namespace_name}")
        dsts[dst] = namespace_name

    fs = require_object(namespaces["fiatShamir"], "namespaces.fiatShamir")
    if require_int(fs.get("rounds"), "namespaces.fiatShamir.rounds") != 128:
        fail("Fiat-Shamir rounds must be 128")
    if require_string(fs.get("challengeExpansion"), "namespaces.fiatShamir.challengeExpansion") != "SHA3-256-counter-mode-low-bit":
        fail("Fiat-Shamir challenge expansion must be SHA3-256-counter-mode-low-bit")
    if require_string(fs.get("controlEncoding"), "namespaces.fiatShamir.controlEncoding") != "domain_i64_le || round_i64_le || field_count_i64_le":
        fail("Fiat-Shamir control encoding must be domain_i64_le || round_i64_le || field_count_i64_le")
    if require_string(fs.get("fieldEncoding"), "namespaces.fiatShamir.fieldEncoding") != "sign_u8 || len_i64_le || magnitude_le_minimal":
        fail("Fiat-Shamir field encoding must be the confidential bignum codec")
    if require_string(fs.get("transcriptLayout"), "namespaces.fiatShamir.transcriptLayout") != "dst || domain_i64_le || round_i64_le || field_count_i64_le || fields_bignum...":
        fail("Fiat-Shamir transcript layout must use bignum transcript fields")
    domains = {
        name: require_int(value, f"namespaces.fiatShamir.domains.{name}")
        for name, value in require_object(fs.get("domains"), "namespaces.fiatShamir.domains").items()
    }
    require_unique_values(domains, "Fiat-Shamir domains")

    for namespace_name in ["merkle", "transaction"]:
        namespace = require_object(namespaces[namespace_name], f"namespaces.{namespace_name}")
        if require_string(namespace.get("integerEncoding"), f"namespaces.{namespace_name}.integerEncoding") != "signed-64-bit-little-endian":
            fail(f"{namespace_name} integer encoding must be signed-64-bit-little-endian")
        tags = {
            name: require_int(value, f"namespaces.{namespace_name}.tags.{name}")
            for name, value in require_object(namespace.get("tags"), f"namespaces.{namespace_name}.tags").items()
        }
        require_unique_values(tags, f"{namespace_name} tags")

    for namespace_name in ["merkleBignum", "transactionBignum"]:
        namespace = require_object(namespaces[namespace_name], f"namespaces.{namespace_name}")
        if require_string(namespace.get("integerEncoding"), f"namespaces.{namespace_name}.integerEncoding") != "sign_u8 || len_i64_le || magnitude_le_minimal":
            fail(f"{namespace_name} integer encoding must be the confidential bignum codec")
        if require_string(namespace.get("digestEncoding"), f"namespaces.{namespace_name}.digestEncoding") != "len_i64_le || 32 raw digest bytes":
            fail(f"{namespace_name} digest encoding must be len_i64_le || 32 raw digest bytes")
        tags = {
            name: require_int(value, f"namespaces.{namespace_name}.tags.{name}")
            for name, value in require_object(namespace.get("tags"), f"namespaces.{namespace_name}.tags").items()
        }
        require_unique_values(tags, f"{namespace_name} tags")

    require_string(namespaces["transaction"].get("protocolId"), "namespaces.transaction.protocolId")
    require_string(namespaces["transactionBignum"].get("protocolId"), "namespaces.transactionBignum.protocolId")
    return namespaces


def check_fixtures(namespaces: dict[str, dict[str, Any]]) -> None:
    fs = namespaces["fiatShamir"]
    transcript = load_json(TRANSCRIPT_VECTORS)
    if transcript.get("dst") != fs["dst"]:
        fail("confidential-transcript-vectors dst disagrees with registry")
    if transcript.get("algorithm") != fs["challengeExpansion"]:
        fail("confidential-transcript-vectors challenge expansion disagrees with registry")
    expected_integer_encoding = f"control={fs['controlEncoding']}; field={fs['fieldEncoding']}"
    if transcript.get("integerEncoding") != expected_integer_encoding:
        fail("confidential-transcript-vectors integer encoding disagrees with registry")
    if transcript.get("controlEncoding") != fs["controlEncoding"]:
        fail("confidential-transcript-vectors control encoding disagrees with registry")
    if transcript.get("fieldEncoding") != fs["fieldEncoding"]:
        fail("confidential-transcript-vectors field encoding disagrees with registry")
    if transcript.get("transcriptLayout") != fs["transcriptLayout"]:
        fail("confidential-transcript-vectors layout disagrees with registry")
    registry_domains = set(require_object(fs["domains"], "fiatShamir.domains").values())
    vector_domains = {
        require_int(require_object(case, "transcript case").get("domain"), "transcript case.domain")
        for case in transcript.get("cases", [])
    }
    if vector_domains != registry_domains:
        fail(f"transcript vector domains {sorted(vector_domains)} disagree with registry {sorted(registry_domains)}")

    merkle = namespaces["merkle"]
    merkle_vectors = load_json(MERKLE_VECTORS)
    if merkle_vectors.get("dst") != merkle["dst"]:
        fail("confidential-merkle-vectors dst disagrees with registry")
    if merkle_vectors.get("integerEncoding") != merkle["integerEncoding"]:
        fail("confidential-merkle-vectors integer encoding disagrees with registry")
    if merkle_vectors.get("tags") != merkle["tags"]:
        fail("confidential-merkle-vectors tags disagree with registry")

    transaction = namespaces["transaction"]
    transaction_vectors = load_json(TRANSACTION_VECTORS)
    if transaction_vectors.get("dst") != transaction["dst"]:
        fail("confidential-transaction-vectors dst disagrees with registry")
    if transaction_vectors.get("integerEncoding") != transaction["integerEncoding"]:
        fail("confidential-transaction-vectors integer encoding disagrees with registry")
    if transaction_vectors.get("protocolId") != transaction["protocolId"]:
        fail("confidential-transaction-vectors protocolId disagrees with registry")
    if transaction_vectors.get("tags") != transaction["tags"]:
        fail("confidential-transaction-vectors tags disagree with registry")

    merkle_bignum = namespaces["merkleBignum"]
    transaction_bignum = namespaces["transactionBignum"]
    bignum_transaction_vectors = load_json(BIGNUM_TRANSACTION_VECTORS)
    bignum_merkle_vectors = require_object(
        bignum_transaction_vectors.get("merkle"),
        "confidential-bignum-transaction-vectors merkle",
    )
    bignum_tx_vectors = require_object(
        bignum_transaction_vectors.get("transaction"),
        "confidential-bignum-transaction-vectors transaction",
    )
    if bignum_merkle_vectors.get("dst") != merkle_bignum["dst"]:
        fail("confidential-bignum-transaction-vectors Merkle dst disagrees with registry")
    if bignum_merkle_vectors.get("integerEncoding") != merkle_bignum["integerEncoding"]:
        fail("confidential-bignum-transaction-vectors Merkle integer encoding disagrees with registry")
    if bignum_merkle_vectors.get("digestEncoding") != merkle_bignum["digestEncoding"]:
        fail("confidential-bignum-transaction-vectors Merkle digest encoding disagrees with registry")
    if bignum_merkle_vectors.get("tags") != merkle_bignum["tags"]:
        fail("confidential-bignum-transaction-vectors Merkle tags disagree with registry")
    if bignum_tx_vectors.get("dst") != transaction_bignum["dst"]:
        fail("confidential-bignum-transaction-vectors transaction dst disagrees with registry")
    if bignum_tx_vectors.get("integerEncoding") != transaction_bignum["integerEncoding"]:
        fail("confidential-bignum-transaction-vectors transaction integer encoding disagrees with registry")
    if bignum_tx_vectors.get("digestEncoding") != transaction_bignum["digestEncoding"]:
        fail("confidential-bignum-transaction-vectors transaction digest encoding disagrees with registry")
    if bignum_tx_vectors.get("protocolId") != transaction_bignum["protocolId"]:
        fail("confidential-bignum-transaction-vectors transaction protocolId disagrees with registry")
    if bignum_tx_vectors.get("tags") != transaction_bignum["tags"]:
        fail("confidential-bignum-transaction-vectors transaction tags disagree with registry")


def check_source_constants(namespaces: dict[str, dict[str, Any]]) -> None:
    fs = namespaces["fiatShamir"]
    merkle = namespaces["merkle"]
    merkle_bignum = namespaces["merkleBignum"]
    transaction = namespaces["transaction"]
    transaction_bignum = namespaces["transactionBignum"]
    fs_domains = fs["domains"]
    merkle_tags = merkle["tags"]
    transaction_tags = transaction["tags"]

    string_checks = [
        ("scripts/generate_confidential_transcript_vectors.mjs", fs["dst"], "Fiat-Shamir generator DST"),
        ("isabella.ml/src/canon/repeated_fs.ml", fs["dst"], "OCaml Fiat-Shamir DST"),
        ("isabella.hs/src/Canon/ZK/Internal/RepeatedFS.hs", fs["dst"], "Haskell Fiat-Shamir DST"),
        ("scripts/generate_confidential_merkle_vectors.mjs", merkle["dst"], "Merkle generator DST"),
        ("isabella.ts/src/index.ts", merkle["dst"], "TypeScript Merkle DST"),
        ("isabella.ts/src/index.ts", merkle_bignum["dst"], "TypeScript bignum Merkle DST"),
        ("scripts/generate_confidential_bignum_transaction_vectors.mjs", merkle_bignum["dst"], "bignum transaction generator Merkle DST"),
        ("isabella.ml/src/canon/confidential_merkle.ml", merkle["dst"], "OCaml Merkle DST"),
        ("isabella.hs/src/Canon/ZK/Confidential_Merkle.hs", merkle["dst"], "Haskell Merkle DST"),
        ("scripts/generate_confidential_transaction_vectors.mjs", transaction["dst"], "transaction generator DST"),
        ("scripts/generate_confidential_transaction_vectors.mjs", transaction["protocolId"], "transaction generator protocol id"),
        ("isabella.ts/src/index.ts", transaction["dst"], "TypeScript transaction DST"),
        ("isabella.ts/src/index.ts", transaction_bignum["dst"], "TypeScript bignum transaction DST"),
        ("isabella.ts/src/index.ts", transaction["protocolId"], "TypeScript transaction protocol id"),
        ("scripts/generate_confidential_bignum_transaction_vectors.mjs", transaction_bignum["dst"], "bignum transaction generator DST"),
        ("scripts/generate_confidential_bignum_transaction_vectors.mjs", transaction_bignum["protocolId"], "bignum transaction generator protocol id"),
        ("isabella.ml/src/canon/confidential_transaction.ml", transaction["dst"], "OCaml transaction DST"),
        ("isabella.ml/src/canon/confidential_transaction.ml", transaction["protocolId"], "OCaml transaction protocol id"),
        ("isabella.hs/src/Canon/ZK/Confidential_Transaction.hs", transaction["dst"], "Haskell transaction DST"),
        ("isabella.hs/src/Canon/ZK/Confidential_Transaction.hs", transaction["protocolId"], "Haskell transaction protocol id"),
    ]
    for path, literal, label in string_checks:
        require_pattern(path, re.escape(literal), label)

    numeric_checks = [
        ("isabella.ml/src/canon/confidential_balance.ml", r"let\s+balance_fs_domain\s*=\s*{}", fs_domains["balance"], "OCaml balance FS domain"),
        ("isabella.hs/src/Canon/ZK/Confidential_Balance.hs", r"balanceFsDomain\s*=\s*{}", fs_domains["balance"], "Haskell balance FS domain"),
        ("Canon/ZK/Confidential_Balance.thy", r'"balance_fs_domain\s*=\s*{}"', fs_domains["balance"], "HOL balance FS domain"),
        ("isabella.ml/src/canon/confidential_range.ml", r"let\s+range_fs_domain\s*=\s*{}", fs_domains["range"], "OCaml range FS domain"),
        ("isabella.hs/src/Canon/ZK/Confidential_Range.hs", r"rangeFsDomain\s*=\s*{}", fs_domains["range"], "Haskell range FS domain"),
        ("Canon/ZK/Confidential_Range.thy", r'"range_fs_domain\s*=\s*{}"', fs_domains["range"], "HOL range FS domain"),
        ("isabella.ml/src/canon/confidential_transaction.ml", r"let\s+nullifier_fs_domain\s*=\s*{}", fs_domains["nullifier"], "OCaml nullifier FS domain"),
        ("isabella.hs/src/Canon/ZK/Confidential_Transaction.hs", r"nullifierFsDomain\s*=\s*{}", fs_domains["nullifier"], "Haskell nullifier FS domain"),
        ("Canon/ZK/Confidential_Transaction.thy", r'"nullifier_fs_domain\s*=\s*{}"', fs_domains["nullifier"], "HOL nullifier FS domain"),
        ("isabella.ts/src/index.ts", r"context:\s*{},", transaction_tags["context"], "TypeScript transaction context tag"),
        ("isabella.ts/src/index.ts", r"merkleProof:\s*{},", transaction_tags["merkleProof"], "TypeScript transaction Merkle proof tag"),
        ("isabella.ts/src/index.ts", r"envelope:\s*{},", transaction_tags["envelope"], "TypeScript transaction envelope tag"),
        ("isabella.ts/src/index.ts", r"walletProofRequest:\s*{},", transaction_tags["walletProofRequest"], "TypeScript wallet proof request tag"),
        ("isabella.ts/src/index.ts", r"acceptedRootWindow:\s*{},", transaction_tags["acceptedRootWindow"], "TypeScript accepted root window tag"),
        ("scripts/generate_confidential_transaction_vectors.mjs", r"context:\s*{},", transaction_tags["context"], "transaction generator context tag"),
        ("scripts/generate_confidential_transaction_vectors.mjs", r"merkleProof:\s*{},", transaction_tags["merkleProof"], "transaction generator Merkle proof tag"),
        ("scripts/generate_confidential_transaction_vectors.mjs", r"envelope:\s*{},", transaction_tags["envelope"], "transaction generator envelope tag"),
        ("scripts/generate_confidential_transaction_vectors.mjs", r"walletProofRequest:\s*{},", transaction_tags["walletProofRequest"], "transaction generator wallet proof request tag"),
        ("scripts/generate_confidential_transaction_vectors.mjs", r"acceptedRootWindow:\s*{},", transaction_tags["acceptedRootWindow"], "transaction generator accepted root window tag"),
        ("scripts/generate_confidential_bignum_transaction_vectors.mjs", r"context:\s*{},", transaction_tags["context"], "bignum transaction generator context tag"),
        ("scripts/generate_confidential_bignum_transaction_vectors.mjs", r"merkleProof:\s*{},", transaction_tags["merkleProof"], "bignum transaction generator Merkle proof tag"),
        ("scripts/generate_confidential_bignum_transaction_vectors.mjs", r"envelope:\s*{},", transaction_tags["envelope"], "bignum transaction generator envelope tag"),
        ("scripts/generate_confidential_bignum_transaction_vectors.mjs", r"walletProofRequest:\s*{},", transaction_tags["walletProofRequest"], "bignum transaction generator wallet proof request tag"),
        ("scripts/generate_confidential_bignum_transaction_vectors.mjs", r"acceptedRootWindow:\s*{},", transaction_tags["acceptedRootWindow"], "bignum transaction generator accepted root window tag"),
        ("scripts/generate_confidential_bignum_transaction_vectors.mjs", r"leaf:\s*{},", merkle_tags["leaf"], "bignum transaction generator Merkle leaf tag"),
        ("scripts/generate_confidential_bignum_transaction_vectors.mjs", r"node:\s*{},", merkle_tags["node"], "bignum transaction generator Merkle node tag"),
        ("scripts/generate_confidential_bignum_transaction_vectors.mjs", r"empty:\s*{},", merkle_tags["empty"], "bignum transaction generator Merkle empty tag"),
        ("isabella.ml/src/canon/confidential_merkle.ml", r"let\s+merkle_leaf_tag\s*=\s*{}", merkle_tags["leaf"], "OCaml Merkle leaf tag"),
        ("isabella.ml/src/canon/confidential_merkle.ml", r"let\s+merkle_node_tag\s*=\s*{}", merkle_tags["node"], "OCaml Merkle node tag"),
        ("isabella.ml/src/canon/confidential_merkle.ml", r"let\s+merkle_empty_tag\s*=\s*{}", merkle_tags["empty"], "OCaml Merkle empty tag"),
        ("isabella.hs/src/Canon/ZK/Confidential_Merkle.hs", r"merkleLeafTag\s*=\s*{}", merkle_tags["leaf"], "Haskell Merkle leaf tag"),
        ("isabella.hs/src/Canon/ZK/Confidential_Merkle.hs", r"merkleNodeTag\s*=\s*{}", merkle_tags["node"], "Haskell Merkle node tag"),
        ("isabella.hs/src/Canon/ZK/Confidential_Merkle.hs", r"merkleEmptyTag\s*=\s*{}", merkle_tags["empty"], "Haskell Merkle empty tag"),
        ("isabella.ml/src/canon/confidential_transaction.ml", r"let\s+transaction_context_tag\s*=\s*{}", transaction_tags["context"], "OCaml transaction context tag"),
        ("isabella.ml/src/canon/confidential_transaction.ml", r"let\s+transaction_merkle_proof_tag\s*=\s*{}", transaction_tags["merkleProof"], "OCaml transaction Merkle proof tag"),
        ("isabella.ml/src/canon/confidential_transaction.ml", r"let\s+transaction_envelope_tag\s*=\s*{}", transaction_tags["envelope"], "OCaml transaction envelope tag"),
        ("isabella.ml/src/canon/confidential_transaction.ml", r"let\s+transaction_wallet_proof_request_tag\s*=\s*{}", transaction_tags["walletProofRequest"], "OCaml wallet proof request tag"),
        ("isabella.ml/src/canon/confidential_transaction.ml", r"let\s+transaction_accepted_root_window_tag\s*=\s*{}", transaction_tags["acceptedRootWindow"], "OCaml accepted root window tag"),
        ("isabella.hs/src/Canon/ZK/Confidential_Transaction.hs", r"transactionContextTag\s*=\s*{}", transaction_tags["context"], "Haskell transaction context tag"),
        ("isabella.hs/src/Canon/ZK/Confidential_Transaction.hs", r"transactionMerkleProofTag\s*=\s*{}", transaction_tags["merkleProof"], "Haskell transaction Merkle proof tag"),
        ("isabella.hs/src/Canon/ZK/Confidential_Transaction.hs", r"transactionEnvelopeTag\s*=\s*{}", transaction_tags["envelope"], "Haskell transaction envelope tag"),
        ("isabella.hs/src/Canon/ZK/Confidential_Transaction.hs", r"transactionWalletProofRequestTag\s*=\s*{}", transaction_tags["walletProofRequest"], "Haskell wallet proof request tag"),
        ("isabella.hs/src/Canon/ZK/Confidential_Transaction.hs", r"transactionAcceptedRootWindowTag\s*=\s*{}", transaction_tags["acceptedRootWindow"], "Haskell accepted root window tag"),
    ]
    for path, template, value, label in numeric_checks:
        require_pattern(path, template.format(value), label)

    repeated_fs_theory = "Canon/ZK/Repeated_FS.thy"
    forbid_pattern(
        repeated_fs_theory,
        r"\btranscript_mix\b",
        "the old deterministic transcript mixer",
    )
    require_pattern(
        repeated_fs_theory,
        r"axiomatization\s+binary_fs_challenge\s*::",
        "abstract binary_fs_challenge oracle",
    )
    require_pattern(
        repeated_fs_theory,
        r"binary_fs_challenge_bit:",
        "binary_fs_challenge bit-output contract",
    )
    require_pattern(
        repeated_fs_theory,
        r"Canon\.ZK\.Internal\.RepeatedFS\.binaryFsChallenge",
        "Haskell binary_fs_challenge code-printing binding",
    )
    require_pattern(
        repeated_fs_theory,
        r"Repeated_fs\.binary_fs_challenge",
        "OCaml binary_fs_challenge code-printing binding",
    )


def main() -> None:
    registry = load_json(REGISTRY)
    namespaces = check_registry_shape(registry)
    check_fixtures(namespaces)
    check_source_constants(namespaces)
    print(json.dumps({
        "gate": "confidential-domain-registry",
        "status": "passed",
        "namespaces": sorted(namespaces),
    }, indent=2))


if __name__ == "__main__":
    main()
