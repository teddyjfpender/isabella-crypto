#!/usr/bin/env python3
"""Screen confidential-transfer parameter candidates.

This is a deterministic repository-local sanity pass, not a replacement for
Albrecht-style lattice-estimator analysis. It records the concrete MVP
dimensions the formalization is targeting and flags whether an external
estimator module is available in the local Python environment.
"""

from __future__ import annotations

import argparse
import importlib
import json
import math
from importlib import metadata
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
    target_security_bits: int
    notes: str


PARAMETER_FIELDS = ("n1", "n2", "m", "q", "beta", "gamma", "range_bits", "fs_rounds")


def log2(x: float) -> float:
    return math.log(x, 2)


def volume_bits(dimension: int, bound: int) -> float:
    return dimension * log2(2 * bound + 1)


def bound_check(q: int, bound: int) -> dict[str, Any]:
    minimum_q = bound + 1
    q_shortfall = max(0, minimum_q - q)
    return {
        "bound": bound,
        "log2_bound": round(log2(bound), 2) if bound > 0 else None,
        "less_than_modulus": bound < q,
        "bound_to_modulus_ratio": round(bound / q, 6),
        "minimum_q": minimum_q,
        "minimum_q_bits": minimum_q.bit_length(),
        "current_q_bits": q.bit_length(),
        "q_shortfall": q_shortfall,
        "q_bits_shortfall": max(0, minimum_q.bit_length() - q.bit_length()),
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
    minimum_q = max(check["minimum_q"] for check in checks.values())

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
        "minimum_modulus_requirement": {
            "current_q": candidate.q,
            "current_q_bits": candidate.q.bit_length(),
            "minimum_q": minimum_q,
            "minimum_q_bits": minimum_q.bit_length(),
            "q_shortfall": max(0, minimum_q - candidate.q),
            "q_bits_shortfall": max(0, minimum_q.bit_length() - candidate.q.bit_length()),
            "blocking_checks": warnings,
        },
        "warnings": warnings,
    }


def external_lattice_estimator_request(candidate: Candidate, margins: dict[str, Any]) -> dict[str, Any]:
    if not margins.get("applicable", False):
        return {
            "applicable": False,
            "reason": margins.get("reason", "formal SIS margins are not available for this candidate"),
            "required_relations": margins.get("required_relations", []),
        }

    sis_bounds = margins.get("sis_comparison_bounds", {})
    if not isinstance(sis_bounds, dict) or not sis_bounds:
        return {
            "applicable": False,
            "reason": "formal SIS comparison bounds are missing",
        }

    source_bound_name, length_bound = max(
        ((str(name), int(bound)) for name, bound in sis_bounds.items()),
        key=lambda item: item[1],
    )
    q_minus_one = candidate.q - 1
    twice_length_bound = 2 * length_bound
    half_modulus = q_minus_one / 2
    length_bound_lt_half_modulus = twice_length_bound < q_minus_one
    total_dim = candidate.n1 + candidate.n2

    return {
        "applicable": True,
        "tool_family": "malb/lattice-estimator",
        "problem": "SIS",
        "estimator_api": {
            "module": "estimator",
            "constructor": "SIS.Parameters",
            "estimate_calls": ["SIS.estimate", "SIS.estimate.rough"],
        },
        "parameter_mapping": {
            "n": candidate.m,
            "m": total_dim,
            "q": candidate.q,
            "norm": "infinity",
            "length_bound": length_bound,
        },
        "source_bound": {
            "name": f"sis_{source_bound_name}",
            "value": length_bound,
            "formal_source": "Canon/Crypto/Commit_SIS.thy: commit_collision_yields_sis_bound",
        },
        "estimator_preconditions": {
            "length_bound_lt_half_modulus": length_bound_lt_half_modulus,
            "comparison": "2 * length_bound < q - 1",
            "q_minus_one": q_minus_one,
            "twice_length_bound": twice_length_bound,
            "half_modulus": half_modulus,
            "current_q_bits": candidate.q.bit_length(),
            "length_bound_bits": length_bound.bit_length(),
        },
        "status": (
            "ready_for_external_estimator"
            if length_bound_lt_half_modulus
            else "blocked_by_formal_modulus"
        ),
        "notes": (
            "Pass this SIS instance to lattice-estimator with norm=+Infinity only "
            "after the formal response/SIS bound is below (q - 1) / 2."
        ),
    }


def screen(candidate: Candidate) -> dict[str, Any]:
    total_dim = candidate.n1 + candidate.n2
    syndrome_bits = candidate.m * log2(candidate.q)
    opening_bits = total_dim * log2(2 * candidate.beta + 1)
    response_bits = candidate.n2 * log2(2 * (candidate.gamma + 4 * candidate.beta) + 1)
    margins = proof_margins(candidate)
    return {
        **asdict(candidate),
        "total_opening_dimension": total_dim,
        "syndrome_capacity_bits": round(syndrome_bits, 2),
        "short_opening_volume_bits": round(opening_bits, 2),
        "capacity_minus_opening_bits": round(syndrome_bits - opening_bits, 2),
        "balance_response_volume_bits": round(response_bits, 2),
        "fiat_shamir_soundness_bits": candidate.fs_rounds,
        "formal_proof_margins": margins,
        "external_lattice_estimator_request": external_lattice_estimator_request(candidate, margins),
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

    target_security_bits = screened.get("target_security_bits")
    estimator_report = screened.get("external_lattice_estimator_report")
    if isinstance(estimator_report, dict):
        security_bits = estimator_report.get("security_level_bits")
        if (
            not isinstance(security_bits, (int, float))
            or isinstance(security_bits, bool)
            or not isinstance(target_security_bits, (int, float))
            or isinstance(target_security_bits, bool)
            or security_bits < target_security_bits
        ):
            blockers.append("external_lattice_estimator_security_below_target")
        parameters = estimator_report.get("parameters")
        if not isinstance(parameters, dict) or not parameter_snapshot_matches(screened, parameters):
            blockers.append("external_lattice_estimator_parameter_mismatch")

    lazer_report = screened.get("lazer_parameter_generation_report")
    if isinstance(lazer_report, dict):
        security_bits = lazer_report.get("security_level_bits")
        if (
            not isinstance(security_bits, (int, float))
            or isinstance(security_bits, bool)
            or not isinstance(target_security_bits, (int, float))
            or isinstance(target_security_bits, bool)
            or security_bits < target_security_bits
        ):
            blockers.append("lazer_parameter_security_below_target")
        parameter_set = lazer_report.get("parameter_set")
        if not isinstance(parameter_set, dict) or not parameter_snapshot_matches(screened, parameter_set):
            blockers.append("lazer_parameter_set_mismatch")

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
            requirement = margins.get("minimum_modulus_requirement", {})
            minimum_q_bits = requirement.get("minimum_q_bits")
            if isinstance(minimum_q_bits, int) and minimum_q_bits > 0:
                blockers.append(f"formal_minimum_q_bits_required:{minimum_q_bits}")
        checks = margins.get("modulus_checks", {})
        failed_checks = [
            name
            for name, check in checks.items()
            if not check.get("less_than_modulus", False)
        ]
        if failed_checks:
            blockers.append("sis_bound_checks_failed:" + ",".join(failed_checks))

    return blockers


def parameter_snapshot_matches(candidate: dict[str, Any], parameters: dict[str, Any]) -> bool:
    return all(parameters.get(field) == candidate.get(field) for field in PARAMETER_FIELDS)


def module_version(distribution: str) -> str | None:
    try:
        return metadata.version(distribution)
    except metadata.PackageNotFoundError:
        return None


def external_estimator_probe() -> dict[str, Any]:
    attempted = []
    for module_name in ["estimator", "lattice_estimator", "lwe_estimator"]:
        attempt: dict[str, Any] = {"module": module_name}
        try:
            module = importlib.import_module(module_name)
        except Exception as exc:  # noqa: BLE001 - capture exact local import failure as evidence.
            attempt["available"] = False
            attempt["error"] = type(exc).__name__
            attempt["message"] = str(exc)
            attempted.append(attempt)
            continue

        attempt["available"] = True
        attempt["path"] = getattr(module, "__file__", None)
        attempt["version"] = (
            getattr(module, "__version__", None)
            or module_version(module_name)
            or module_version("lattice-estimator")
        )
        attempted.append(attempt)
        return {
            "available": True,
            "selected_module": module_name,
            "attempted_modules": attempted,
        }

    return {
        "available": False,
        "selected_module": None,
        "attempted_modules": attempted,
    }


def load_report_collection(path: str | None, label: str) -> dict[str, dict[str, Any]]:
    if path is None:
        return {}
    report_path = Path(path)
    try:
        loaded = json.loads(report_path.read_text(encoding="utf-8"))
    except FileNotFoundError as exc:
        raise SystemExit(f"{label} report file missing: {report_path}") from exc
    except json.JSONDecodeError as exc:
        raise SystemExit(f"{label} report file is not valid JSON: {exc}") from exc

    reports = loaded.get("reports") if isinstance(loaded, dict) else None
    if not isinstance(reports, list):
        raise SystemExit(f"{label} report file must contain a reports list")

    by_candidate: dict[str, dict[str, Any]] = {}
    for index, report in enumerate(reports):
        if not isinstance(report, dict):
            raise SystemExit(f"{label} report at index {index} must be an object")
        candidate = report.get("candidate")
        if not isinstance(candidate, str) or not candidate:
            raise SystemExit(f"{label} report at index {index} must name a candidate")
        if candidate in by_candidate:
            raise SystemExit(f"{label} report has duplicate candidate entry: {candidate}")
        by_candidate[candidate] = report
    return by_candidate


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--out", default="bench/data/confidential-parameter-screen.json")
    parser.add_argument(
        "--external-estimator-report",
        help="optional JSON report collection containing production lattice-estimator evidence",
    )
    parser.add_argument(
        "--lazer-parameter-report",
        help="optional JSON report collection containing LaZer-style parameter-generation evidence",
    )
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
            target_security_bits=128,
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
            target_security_bits=128,
            notes=(
                "Research track from idea.md; kept separate from the SIS-note MVP "
                "until EncryptValid/SamePlaintext/TransferValid relations are formalized."
            ),
        ),
    ]

    estimator_probe = external_estimator_probe()
    estimator_available = bool(estimator_probe["available"])
    estimator_reports = load_report_collection(args.external_estimator_report, "external estimator")
    lazer_reports = load_report_collection(args.lazer_parameter_report, "LaZer parameter")
    screened_candidates = []
    for candidate in candidates:
        screened = screen(candidate)
        if candidate.name in estimator_reports:
            screened["external_lattice_estimator_report"] = estimator_reports[candidate.name]
            screened["screening_status"] = "production_candidate"
        if candidate.name in lazer_reports:
            screened["lazer_parameter_generation_report"] = lazer_reports[candidate.name]
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
        "external_lattice_estimator_probe": estimator_probe,
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
