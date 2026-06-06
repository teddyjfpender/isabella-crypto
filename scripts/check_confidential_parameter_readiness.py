#!/usr/bin/env python3
"""Validate confidential-transfer parameter-readiness reports.

The default mode is an honesty gate: it passes when the report explicitly marks
the current candidates as blocked with machine-readable reasons. Release builds
can add --require-production to fail unless at least one candidate has external
estimator evidence, LaZer parameter-generation evidence, and passing formal
proof-margin checks.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any


PARAMETER_FIELDS = ("n1", "n2", "m", "q", "beta", "gamma", "range_bits", "fs_rounds")


def fail(message: str) -> None:
    raise SystemExit(message)


def read_report(path: Path) -> dict[str, Any]:
    try:
        report = json.loads(path.read_text(encoding="utf-8"))
    except FileNotFoundError:
        fail(f"parameter report missing: {path}")
    except json.JSONDecodeError as exc:
        fail(f"parameter report is not valid JSON: {exc}")
    if not isinstance(report, dict):
        fail("parameter report root must be a JSON object")
    return report


def require_object(value: Any, label: str) -> dict[str, Any]:
    if not isinstance(value, dict):
        fail(f"{label} must be an object")
    return value


def require_list(value: Any, label: str) -> list[Any]:
    if not isinstance(value, list):
        fail(f"{label} must be a list")
    return value


def require_string(value: Any, label: str) -> str:
    if not isinstance(value, str) or not value:
        fail(f"{label} must be a non-empty string")
    return value


def require_positive_number(value: Any, label: str) -> int | float:
    if not isinstance(value, (int, float)) or isinstance(value, bool) or value <= 0:
        fail(f"{label} must be a positive number")
    return value


def require_positive_int(value: Any, label: str) -> int:
    if not isinstance(value, int) or isinstance(value, bool) or value <= 0:
        fail(f"{label} must be a positive integer")
    return value


def candidate_name(candidate: dict[str, Any]) -> str:
    name = candidate.get("name")
    if not isinstance(name, str) or not name:
        fail("candidate.name must be a non-empty string")
    return name


def validate_estimator_probe(report: dict[str, Any], external_estimator_available: bool) -> None:
    probe = require_object(report.get("external_lattice_estimator_probe"), "external_lattice_estimator_probe")
    if probe.get("available") != external_estimator_available:
        fail("external_lattice_estimator_probe.available disagrees with external_lattice_estimator_available")
    selected = probe.get("selected_module")
    if external_estimator_available:
        require_string(selected, "external_lattice_estimator_probe.selected_module")
    elif selected is not None:
        fail("external_lattice_estimator_probe.selected_module must be null when unavailable")

    attempts = require_list(
        probe.get("attempted_modules"),
        "external_lattice_estimator_probe.attempted_modules",
    )
    if not attempts:
        fail("external_lattice_estimator_probe.attempted_modules must not be empty")

    saw_available = False
    for index, raw_attempt in enumerate(attempts):
        attempt = require_object(raw_attempt, f"external_lattice_estimator_probe.attempted_modules[{index}]")
        module = require_string(attempt.get("module"), f"estimator attempt {index}.module")
        available = attempt.get("available")
        if not isinstance(available, bool):
            fail(f"estimator attempt {module}.available must be a boolean")
        if available:
            saw_available = True
            if selected != module:
                fail(f"available estimator attempt {module} must match selected_module")
            path = attempt.get("path")
            if path is not None and not isinstance(path, str):
                fail(f"estimator attempt {module}.path must be a string or null")
        else:
            require_string(attempt.get("error"), f"estimator attempt {module}.error")
            message = attempt.get("message")
            if not isinstance(message, str):
                fail(f"estimator attempt {module}.message must be a string")

    if external_estimator_available != saw_available:
        fail("external_lattice_estimator_probe availability is inconsistent with attempts")


def validate_command(value: Any, label: str) -> None:
    if isinstance(value, str):
        if not value:
            fail(f"{label} must not be empty")
        return
    if isinstance(value, list) and value and all(isinstance(part, str) and part for part in value):
        return
    fail(f"{label} must be a non-empty string or non-empty string list")


def validate_parameter_snapshot(parameters: dict[str, Any], candidate: dict[str, Any], label: str) -> None:
    for field in PARAMETER_FIELDS:
        expected = candidate.get(field)
        if not isinstance(expected, int) or isinstance(expected, bool) or expected <= 0:
            fail(f"{candidate_name(candidate)}.{field} must be a positive integer")
        actual = parameters.get(field)
        if actual != expected:
            fail(f"{label}.{field} must equal candidate.{field} ({expected})")


def validate_report_security_level(
    report: dict[str, Any],
    candidate: dict[str, Any],
    label: str,
) -> None:
    security_bits = require_positive_number(report.get("security_level_bits"), f"{label}.security_level_bits")
    target_security_bits = require_positive_number(
        candidate.get("target_security_bits"),
        f"{candidate_name(candidate)}.target_security_bits",
    )
    if security_bits < target_security_bits:
        fail(f"{label}.security_level_bits is below target_security_bits={target_security_bits}")


def validate_external_estimator_report(report: dict[str, Any], candidate: dict[str, Any]) -> None:
    candidate_id = candidate_name(candidate)
    label = f"{candidate_id}.external_lattice_estimator_report"
    if require_string(report.get("candidate"), f"{label}.candidate") != candidate_id:
        fail(f"{label}.candidate does not match candidate name")
    require_string(report.get("tool"), f"{label}.tool")
    require_string(report.get("source"), f"{label}.source")
    require_string(report.get("generated_at"), f"{label}.generated_at")
    validate_command(report.get("command"), f"{label}.command")
    validate_report_security_level(report, candidate, label)
    parameters = require_object(
        report.get("parameters"),
        f"{label}.parameters",
    )
    validate_parameter_snapshot(parameters, candidate, f"{label}.parameters")
    assumptions = require_list(
        report.get("assumptions"),
        f"{label}.assumptions",
    )
    if not assumptions or not all(isinstance(assumption, str) and assumption for assumption in assumptions):
        fail(f"{label}.assumptions must contain non-empty strings")


def validate_lazer_parameter_report(report: dict[str, Any], candidate: dict[str, Any]) -> None:
    candidate_id = candidate_name(candidate)
    label = f"{candidate_id}.lazer_parameter_generation_report"
    if require_string(report.get("candidate"), f"{label}.candidate") != candidate_id:
        fail(f"{label}.candidate does not match candidate name")
    require_string(report.get("tool"), f"{label}.tool")
    require_string(report.get("source"), f"{label}.source")
    require_string(report.get("generated_at"), f"{label}.generated_at")
    validate_command(report.get("command"), f"{label}.command")
    parameter_set = require_object(
        report.get("parameter_set"),
        f"{label}.parameter_set",
    )
    validate_parameter_snapshot(parameter_set, candidate, f"{label}.parameter_set")
    require_object(
        report.get("proof_size_estimate"),
        f"{label}.proof_size_estimate",
    )
    validate_report_security_level(report, candidate, label)


def validate_formal_modulus_requirements(
    candidate: dict[str, Any],
    margins: dict[str, Any],
    warnings: list[Any],
) -> None:
    candidate_id = candidate_name(candidate)
    q = require_positive_int(candidate.get("q"), f"{candidate_id}.q")
    checks = require_object(margins.get("modulus_checks"), f"{candidate_id}.formal_proof_margins.modulus_checks")
    failed_checks: list[str] = []
    minimum_q = 1

    for check_name, raw_check in checks.items():
        if not isinstance(check_name, str) or not check_name:
            fail(f"{candidate_id}.formal_proof_margins.modulus_checks keys must be non-empty strings")
        check = require_object(raw_check, f"{candidate_id}.formal_proof_margins.modulus_checks.{check_name}")
        bound = require_positive_int(check.get("bound"), f"{candidate_id}.{check_name}.bound")
        expected_minimum_q = bound + 1
        minimum_q = max(minimum_q, expected_minimum_q)
        less_than_modulus = check.get("less_than_modulus")
        if not isinstance(less_than_modulus, bool):
            fail(f"{candidate_id}.{check_name}.less_than_modulus must be a boolean")
        if less_than_modulus != (bound < q):
            fail(f"{candidate_id}.{check_name}.less_than_modulus is inconsistent with bound and q")
        if not less_than_modulus:
            failed_checks.append(check_name)
        if check.get("minimum_q") != expected_minimum_q:
            fail(f"{candidate_id}.{check_name}.minimum_q must be bound + 1")
        if check.get("minimum_q_bits") != expected_minimum_q.bit_length():
            fail(f"{candidate_id}.{check_name}.minimum_q_bits is inconsistent with minimum_q")
        if check.get("current_q_bits") != q.bit_length():
            fail(f"{candidate_id}.{check_name}.current_q_bits is inconsistent with candidate.q")
        if check.get("q_shortfall") != max(0, expected_minimum_q - q):
            fail(f"{candidate_id}.{check_name}.q_shortfall is inconsistent with minimum_q and candidate.q")
        if check.get("q_bits_shortfall") != max(0, expected_minimum_q.bit_length() - q.bit_length()):
            fail(f"{candidate_id}.{check_name}.q_bits_shortfall is inconsistent with minimum_q_bits and candidate.q")

    if warnings != failed_checks:
        fail(f"{candidate_id}.formal_proof_margins.warnings must match failed modulus checks")

    requirement = require_object(
        margins.get("minimum_modulus_requirement"),
        f"{candidate_id}.formal_proof_margins.minimum_modulus_requirement",
    )
    if requirement.get("current_q") != q:
        fail(f"{candidate_id}.minimum_modulus_requirement.current_q must equal candidate.q")
    if requirement.get("current_q_bits") != q.bit_length():
        fail(f"{candidate_id}.minimum_modulus_requirement.current_q_bits is inconsistent with candidate.q")
    if requirement.get("minimum_q") != minimum_q:
        fail(f"{candidate_id}.minimum_modulus_requirement.minimum_q must equal the maximum check minimum_q")
    if requirement.get("minimum_q_bits") != minimum_q.bit_length():
        fail(f"{candidate_id}.minimum_modulus_requirement.minimum_q_bits is inconsistent with minimum_q")
    if requirement.get("q_shortfall") != max(0, minimum_q - q):
        fail(f"{candidate_id}.minimum_modulus_requirement.q_shortfall is inconsistent with minimum_q and candidate.q")
    if requirement.get("q_bits_shortfall") != max(0, minimum_q.bit_length() - q.bit_length()):
        fail(f"{candidate_id}.minimum_modulus_requirement.q_bits_shortfall is inconsistent with minimum_q_bits and candidate.q")
    blocking_checks = require_list(
        requirement.get("blocking_checks"),
        f"{candidate_id}.minimum_modulus_requirement.blocking_checks",
    )
    if blocking_checks != failed_checks:
        fail(f"{candidate_id}.minimum_modulus_requirement.blocking_checks must match failed modulus checks")


def validate_external_estimator_request(candidate: dict[str, Any], margins: dict[str, Any]) -> None:
    candidate_id = candidate_name(candidate)
    request = require_object(
        candidate.get("external_lattice_estimator_request"),
        f"{candidate_id}.external_lattice_estimator_request",
    )
    applicable = request.get("applicable")
    if not isinstance(applicable, bool):
        fail(f"{candidate_id}.external_lattice_estimator_request.applicable must be a boolean")

    if not margins.get("applicable", False):
        if applicable:
            fail(f"{candidate_id}.external_lattice_estimator_request must not be applicable without SIS margins")
        required_relations = require_list(
            request.get("required_relations"),
            f"{candidate_id}.external_lattice_estimator_request.required_relations",
        )
        margins_relations = margins.get("required_relations", [])
        if required_relations != margins_relations:
            fail(f"{candidate_id}.external_lattice_estimator_request.required_relations must match margins")
        return

    if not applicable:
        fail(f"{candidate_id}.external_lattice_estimator_request must be applicable when SIS margins are applicable")
    if require_string(request.get("problem"), f"{candidate_id}.external_lattice_estimator_request.problem") != "SIS":
        fail(f"{candidate_id}.external_lattice_estimator_request.problem must be SIS")
    require_string(request.get("tool_family"), f"{candidate_id}.external_lattice_estimator_request.tool_family")
    api = require_object(
        request.get("estimator_api"),
        f"{candidate_id}.external_lattice_estimator_request.estimator_api",
    )
    if require_string(api.get("module"), f"{candidate_id}.external_lattice_estimator_request.estimator_api.module") != "estimator":
        fail(f"{candidate_id}.external_lattice_estimator_request.estimator_api.module must be estimator")
    require_string(
        api.get("constructor"),
        f"{candidate_id}.external_lattice_estimator_request.estimator_api.constructor",
    )
    estimate_calls = require_list(
        api.get("estimate_calls"),
        f"{candidate_id}.external_lattice_estimator_request.estimator_api.estimate_calls",
    )
    if not estimate_calls or not all(isinstance(call, str) and call for call in estimate_calls):
        fail(f"{candidate_id}.external_lattice_estimator_request.estimator_api.estimate_calls must contain strings")

    q = require_positive_int(candidate.get("q"), f"{candidate_id}.q")
    n1 = require_positive_int(candidate.get("n1"), f"{candidate_id}.n1")
    n2 = require_positive_int(candidate.get("n2"), f"{candidate_id}.n2")
    rows = require_positive_int(candidate.get("m"), f"{candidate_id}.m")
    mapping = require_object(
        request.get("parameter_mapping"),
        f"{candidate_id}.external_lattice_estimator_request.parameter_mapping",
    )
    if mapping.get("n") != rows:
        fail(f"{candidate_id}.external_lattice_estimator_request.parameter_mapping.n must equal candidate.m")
    if mapping.get("m") != n1 + n2:
        fail(f"{candidate_id}.external_lattice_estimator_request.parameter_mapping.m must equal candidate.n1 + candidate.n2")
    if mapping.get("q") != q:
        fail(f"{candidate_id}.external_lattice_estimator_request.parameter_mapping.q must equal candidate.q")
    if mapping.get("norm") != "infinity":
        fail(f"{candidate_id}.external_lattice_estimator_request.parameter_mapping.norm must be infinity")

    sis_bounds = require_object(
        margins.get("sis_comparison_bounds"),
        f"{candidate_id}.formal_proof_margins.sis_comparison_bounds",
    )
    source_bound_name = ""
    source_length_bound = -1
    for raw_name, raw_bound in sis_bounds.items():
        if not isinstance(raw_name, str) or not raw_name:
            fail(f"{candidate_id}.formal_proof_margins.sis_comparison_bounds keys must be non-empty strings")
        bound = require_positive_int(raw_bound, f"{candidate_id}.sis_comparison_bounds.{raw_name}")
        if bound > source_length_bound:
            source_bound_name = raw_name
            source_length_bound = bound
    if mapping.get("length_bound") != source_length_bound:
        fail(f"{candidate_id}.external_lattice_estimator_request.parameter_mapping.length_bound must equal max SIS comparison bound")

    source = require_object(
        request.get("source_bound"),
        f"{candidate_id}.external_lattice_estimator_request.source_bound",
    )
    if source.get("name") != f"sis_{source_bound_name}":
        fail(f"{candidate_id}.external_lattice_estimator_request.source_bound.name must identify max SIS bound")
    if source.get("value") != source_length_bound:
        fail(f"{candidate_id}.external_lattice_estimator_request.source_bound.value must equal length_bound")
    require_string(
        source.get("formal_source"),
        f"{candidate_id}.external_lattice_estimator_request.source_bound.formal_source",
    )

    preconditions = require_object(
        request.get("estimator_preconditions"),
        f"{candidate_id}.external_lattice_estimator_request.estimator_preconditions",
    )
    expected_q_minus_one = q - 1
    expected_twice_length_bound = 2 * source_length_bound
    expected_precondition = expected_twice_length_bound < expected_q_minus_one
    if preconditions.get("length_bound_lt_half_modulus") != expected_precondition:
        fail(f"{candidate_id}.external_lattice_estimator_request.estimator_preconditions.length_bound_lt_half_modulus is inconsistent")
    if preconditions.get("comparison") != "2 * length_bound < q - 1":
        fail(f"{candidate_id}.external_lattice_estimator_request.estimator_preconditions.comparison is inconsistent")
    if preconditions.get("q_minus_one") != expected_q_minus_one:
        fail(f"{candidate_id}.external_lattice_estimator_request.estimator_preconditions.q_minus_one is inconsistent")
    if preconditions.get("twice_length_bound") != expected_twice_length_bound:
        fail(f"{candidate_id}.external_lattice_estimator_request.estimator_preconditions.twice_length_bound is inconsistent")
    half_modulus = require_positive_number(
        preconditions.get("half_modulus"),
        f"{candidate_id}.external_lattice_estimator_request.estimator_preconditions.half_modulus",
    )
    if half_modulus != expected_q_minus_one / 2:
        fail(f"{candidate_id}.external_lattice_estimator_request.estimator_preconditions.half_modulus is inconsistent with q")
    if preconditions.get("current_q_bits") != q.bit_length():
        fail(f"{candidate_id}.external_lattice_estimator_request.estimator_preconditions.current_q_bits is inconsistent with q")
    if preconditions.get("length_bound_bits") != source_length_bound.bit_length():
        fail(f"{candidate_id}.external_lattice_estimator_request.estimator_preconditions.length_bound_bits is inconsistent")

    expected_status = "ready_for_external_estimator" if expected_precondition else "blocked_by_formal_modulus"
    if request.get("status") != expected_status:
        fail(f"{candidate_id}.external_lattice_estimator_request.status must be {expected_status}")


def validate_candidate(candidate: dict[str, Any], external_estimator_available: bool) -> bool:
    name = candidate_name(candidate)
    readiness = require_object(candidate.get("production_readiness"), f"{name}.production_readiness")
    blockers = require_list(readiness.get("blockers"), f"{name}.production_readiness.blockers")
    ready = readiness.get("ready")
    if not isinstance(ready, bool):
        fail(f"{name}.production_readiness.ready must be a boolean")
    if ready != (len(blockers) == 0):
        fail(f"{name}.production_readiness.ready is inconsistent with blockers")

    margins = require_object(candidate.get("formal_proof_margins"), f"{name}.formal_proof_margins")
    warnings = margins.get("warnings", [])
    if warnings is None:
        warnings = []
    if not isinstance(warnings, list):
        fail(f"{name}.formal_proof_margins.warnings must be a list when present")
    if margins.get("applicable", False):
        validate_formal_modulus_requirements(candidate, margins, warnings)
    validate_external_estimator_request(candidate, margins)

    estimator_report = candidate.get("external_lattice_estimator_report")
    if estimator_report is not None:
        validate_external_estimator_report(
            require_object(estimator_report, f"{name}.external_lattice_estimator_report"),
            candidate,
        )

    lazer_report = candidate.get("lazer_parameter_generation_report")
    if lazer_report is not None:
        validate_lazer_parameter_report(
            require_object(lazer_report, f"{name}.lazer_parameter_generation_report"),
            candidate,
        )

    if ready:
        if candidate.get("screening_status") != "production_candidate":
            fail(f"{name} is ready without screening_status=production_candidate")
        if not external_estimator_available:
            fail(f"{name} is ready while external_lattice_estimator_available=false")
        if estimator_report is None:
            fail(f"{name} is ready without external_lattice_estimator_report")
        if lazer_report is None:
            fail(f"{name} is ready without lazer_parameter_generation_report")
        if not margins.get("applicable", False):
            fail(f"{name} is ready without applicable formal proof margins")
        if warnings:
            fail(f"{name} is ready with formal proof-margin warnings: {warnings}")
        checks = require_object(margins.get("modulus_checks"), f"{name}.formal_proof_margins.modulus_checks")
        failed = [
            check_name
            for check_name, check in checks.items()
            if not require_object(check, f"{name}.{check_name}").get("less_than_modulus", False)
        ]
        if failed:
            fail(f"{name} is ready with failed SIS modulus checks: {failed}")
    elif not blockers:
        fail(f"{name} is not ready but has no blockers")

    return ready


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--report", default="bench/data/confidential-parameter-screen.json")
    parser.add_argument(
        "--require-production",
        action="store_true",
        help="fail unless at least one candidate is production-ready",
    )
    args = parser.parse_args()

    report_path = Path(args.report)
    report = read_report(report_path)

    if report.get("tool") != "confidential_parameter_screen":
        fail("parameter report tool must be confidential_parameter_screen")

    external_estimator_available = report.get("external_lattice_estimator_available")
    if not isinstance(external_estimator_available, bool):
        fail("external_lattice_estimator_available must be a boolean")
    validate_estimator_probe(report, external_estimator_available)

    launch = require_object(report.get("launch_readiness"), "launch_readiness")
    candidates = require_list(report.get("candidates"), "candidates")
    ready_candidates = [
        candidate_name(candidate)
        for candidate in candidates
        if validate_candidate(require_object(candidate, "candidate"), external_estimator_available)
    ]

    launch_ready = launch.get("ready")
    if launch_ready != bool(ready_candidates):
        fail("launch_readiness.ready is inconsistent with candidate readiness")

    declared_ready = require_list(launch.get("ready_candidates"), "launch_readiness.ready_candidates")
    if declared_ready != ready_candidates:
        fail("launch_readiness.ready_candidates does not match candidate readiness")

    status = launch.get("status")
    expected_status = "ready" if ready_candidates else "blocked"
    if status != expected_status:
        fail(f"launch_readiness.status must be {expected_status}")

    if args.require_production and not ready_candidates:
        fail("no production-ready confidential-transfer parameter candidate is available")

    print(json.dumps({
        "gate": "confidential-parameter-readiness",
        "status": "passed",
        "require_production": args.require_production,
        "launch_ready": bool(ready_candidates),
        "ready_candidates": ready_candidates,
        "blocked_candidates": [
            candidate_name(candidate)
            for candidate in candidates
            if not require_object(candidate, "candidate")["production_readiness"]["ready"]
        ],
    }, indent=2))


if __name__ == "__main__":
    main()
