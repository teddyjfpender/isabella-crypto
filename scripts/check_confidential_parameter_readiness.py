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


def candidate_name(candidate: dict[str, Any]) -> str:
    name = candidate.get("name")
    if not isinstance(name, str) or not name:
        fail("candidate.name must be a non-empty string")
    return name


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

    if ready:
        if candidate.get("screening_status") != "production_candidate":
            fail(f"{name} is ready without screening_status=production_candidate")
        if not external_estimator_available:
            fail(f"{name} is ready while external_lattice_estimator_available=false")
        if "external_lattice_estimator_report" not in candidate:
            fail(f"{name} is ready without external_lattice_estimator_report")
        if "lazer_parameter_generation_report" not in candidate:
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
