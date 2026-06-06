#!/usr/bin/env python3
"""Screen confidential-transfer parameter candidates.

This is a deterministic repository-local sanity pass, not a replacement for
Albrecht-style lattice-estimator analysis. It records the concrete MVP
dimensions the formalization is targeting and flags whether an external
estimator module is available in the local Python environment.
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any


@dataclass(frozen=True)
class Candidate:
    name: str
    architecture: str
    n1: int
    n2: int
    m: int
    q: int
    beta: int
    gamma: int
    range_bits: int
    fs_rounds: int
    notes: str


def log2(x: float) -> float:
    return math.log(x, 2)


def volume_bits(dimension: int, bound: int) -> float:
    return dimension * log2(2 * bound + 1)


def bound_check(q: int, bound: int) -> dict[str, Any]:
    return {
        "bound": bound,
        "log2_bound": round(log2(bound), 2) if bound > 0 else None,
        "less_than_modulus": bound < q,
        "bound_to_modulus_ratio": round(bound / q, 6),
    }


def proof_margins(candidate: Candidate) -> dict[str, Any]:
    if "SIS note" not in candidate.architecture:
        return {
            "applicable": False,
            "reason": (
                "Current formal extraction/SIS-margin theorems apply to the SIS "
                "note/nullifier MVP. The RLWE/AHE layer needs separate EncryptValid, "
                "SamePlaintext, TransferValid, and NoiseBoundValid relations before "
                "analogous proof margins can be computed."
            ),
            "required_relations": [
                "EncryptValid",
                "SamePlaintext",
                "TransferValid",
                "NoiseBoundValid",
            ],
        }

    beta = candidate.beta
    gamma = candidate.gamma
    k = candidate.range_bits

    balance_witness = 4 * beta
    balance_extracted = 2 * gamma + balance_witness
    range_amount_witness = (2**k) * beta
    range_amount_extracted = 2 * gamma + range_amount_witness
    range_pair_witness = 2 * beta
    range_pair_extracted = 2 * gamma + range_pair_witness
    nullifier_witness = beta
    nullifier_extracted = 2 * gamma + nullifier_witness

    sis_comparison_bounds = {
        "balance_zero_opening_vs_honest": balance_extracted + balance_witness,
        "range_amount_residual_vs_honest": range_amount_extracted + range_amount_witness,
        "range_pair_residual_vs_honest": range_pair_extracted + range_pair_witness,
        "nullifier_opening_vs_honest": nullifier_extracted + nullifier_witness,
    }

    checks = {
        "balance_extracted_response": bound_check(candidate.q, balance_extracted),
        "range_amount_extracted_response": bound_check(candidate.q, range_amount_extracted),
        "range_pair_extracted_response": bound_check(candidate.q, range_pair_extracted),
        "nullifier_extracted_opening": bound_check(candidate.q, nullifier_extracted),
        **{
            f"sis_{name}": bound_check(candidate.q, bound)
            for name, bound in sis_comparison_bounds.items()
        },
    }

    warnings = [
        name
        for name, check in checks.items()
        if not check["less_than_modulus"]
    ]

    return {
        "applicable": True,
        "formal_sources": [
            "Canon/ZK/Confidential_Balance.thy: balance_sigma_extract_distinct_binary_bound",
            "Canon/ZK/Confidential_Range.thy: range_amount_sigma_extract_distinct_binary_bound",
            "Canon/ZK/Confidential_Range.thy: range_pair_sigma_extract_distinct_binary_bound",
            "Canon/ZK/Confidential_Transaction.thy: nullifier_sigma_extract_distinct_binary_bound",
            "Canon/Crypto/Commit_SIS.thy: commit_collision_yields_sis_bound",
        ],
        "extracted_response_bounds": {
            "balance": balance_extracted,
            "range_amount": range_amount_extracted,
            "range_pair": range_pair_extracted,
            "nullifier": nullifier_extracted,
        },
        "honest_witness_bounds": {
            "balance": balance_witness,
            "range_amount": range_amount_witness,
            "range_pair": range_pair_witness,
            "nullifier": nullifier_witness,
        },
        "sis_comparison_bounds": sis_comparison_bounds,
        "volume_bits": {
            "balance_extracted_response": round(volume_bits(candidate.n2, balance_extracted), 2),
            "range_amount_extracted_response": round(volume_bits(candidate.n2, range_amount_extracted), 2),
            "range_pair_extracted_response": round(volume_bits(candidate.n2, range_pair_extracted), 2),
            "nullifier_extracted_opening": round(
                volume_bits(candidate.n1 + candidate.n2, nullifier_extracted), 2
            ),
        },
        "modulus_checks": checks,
        "warnings": warnings,
    }


def screen(candidate: Candidate) -> dict[str, Any]:
    total_dim = candidate.n1 + candidate.n2
    syndrome_bits = candidate.m * log2(candidate.q)
    opening_bits = total_dim * log2(2 * candidate.beta + 1)
    response_bits = candidate.n2 * log2(2 * (candidate.gamma + 4 * candidate.beta) + 1)
    return {
        **asdict(candidate),
        "total_opening_dimension": total_dim,
        "syndrome_capacity_bits": round(syndrome_bits, 2),
        "short_opening_volume_bits": round(opening_bits, 2),
        "capacity_minus_opening_bits": round(syndrome_bits - opening_bits, 2),
        "balance_response_volume_bits": round(response_bits, 2),
        "fiat_shamir_soundness_bits": candidate.fs_rounds,
        "formal_proof_margins": proof_margins(candidate),
        "screening_status": "screen_only",
    }


def production_blockers(screened: dict[str, Any], external_estimator: bool) -> list[str]:
    blockers: list[str] = []

    if screened.get("screening_status") != "production_candidate":
        blockers.append("screening_status_is_not_production_candidate")

    if not external_estimator:
        blockers.append("external_lattice_estimator_unavailable")

    if "external_lattice_estimator_report" not in screened:
        blockers.append("external_lattice_estimator_report_missing")

    if "lazer_parameter_generation_report" not in screened:
        blockers.append("lazer_parameter_generation_report_missing")

    margins = screened.get("formal_proof_margins", {})
    if not margins.get("applicable", False):
        blockers.append("formal_proof_margins_not_applicable")
        for relation in margins.get("required_relations", []):
            blockers.append(f"formal_relation_missing:{relation}")
    else:
        warnings = margins.get("warnings", [])
        if warnings:
            blockers.append(
                "formal_proof_margin_modulus_failures:" + ",".join(str(warning) for warning in warnings)
            )
        checks = margins.get("modulus_checks", {})
        failed_checks = [
            name
            for name, check in checks.items()
            if not check.get("less_than_modulus", False)
        ]
        if failed_checks:
            blockers.append("sis_bound_checks_failed:" + ",".join(failed_checks))

    return blockers


def external_estimator_available() -> bool:
    try:
        __import__("estimator")
    except Exception:
        return False
    return True


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--out", default="bench/data/confidential-parameter-screen.json")
    args = parser.parse_args()

    candidates = [
        Candidate(
            name="ct_sis_note_mvp_v0",
            architecture="SIS note commitment MVP",
            n1=1,
            n2=1024,
            m=1024,
            q=8_380_417,
            beta=2**16,
            gamma=2**24,
            range_bits=64,
            fs_rounds=128,
            notes=(
                "Formal MVP target for note commitments/nullifiers/range proofs; "
                "requires external lattice-estimator validation before production."
            ),
        ),
        Candidate(
            name="rlwe_ahe_transfer_research_v0",
            architecture="Separate RLWE/AHE EncryptValid/SamePlaintext/TransferValid layer",
            n1=1,
            n2=2048,
            m=2048,
            q=8_380_417,
            beta=2**16,
            gamma=2**24,
            range_bits=64,
            fs_rounds=128,
            notes=(
                "Research track from idea.md; kept separate from the SIS-note MVP "
                "until EncryptValid/SamePlaintext/TransferValid relations are formalized."
            ),
        ),
    ]

    estimator_available = external_estimator_available()
    screened_candidates = []
    for candidate in candidates:
        screened = screen(candidate)
        blockers = production_blockers(screened, estimator_available)
        screened["production_readiness"] = {
            "ready": len(blockers) == 0,
            "blockers": blockers,
        }
        screened_candidates.append(screened)

    ready_candidates = [
        candidate["name"]
        for candidate in screened_candidates
        if candidate["production_readiness"]["ready"]
    ]

    output = {
        "tool": "confidential_parameter_screen",
        "external_lattice_estimator_available": estimator_available,
        "warning": (
            "This JSON is a deterministic parameter screening artifact. It is not "
            "a production security estimate and does not replace lattice-estimator, "
            "LaZer parameter generation, or implementation benchmarks."
        ),
        "launch_readiness": {
            "ready": len(ready_candidates) > 0,
            "selected_production_candidate": ready_candidates[0] if len(ready_candidates) == 1 else None,
            "ready_candidates": ready_candidates,
            "status": "ready" if ready_candidates else "blocked",
            "blockers": [] if ready_candidates else [
                "no_candidate_has_external_estimator_lazer_report_and_passing_formal_margins"
            ],
        },
        "candidates": screened_candidates,
    }

    out = Path(args.out)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(output, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(output, indent=2))


if __name__ == "__main__":
    main()
