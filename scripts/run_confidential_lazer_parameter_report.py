#!/usr/bin/env python3
"""Generate LaZer-style parameter report collections.

This runner is an honesty artifact. It records why each current confidential
parameter candidate can or cannot be handed to a LaZer-style parameter
generation flow. It does not fabricate generated LaZer security evidence.
"""

from __future__ import annotations

import argparse
import json
import sys
from datetime import UTC, datetime
from pathlib import Path
from typing import Any


PARAMETER_FIELDS = ("n1", "n2", "m", "q", "beta", "gamma", "range_bits", "fs_rounds")


def read_json(path: Path) -> dict[str, Any]:
    try:
        loaded = json.loads(path.read_text(encoding="utf-8"))
    except FileNotFoundError as exc:
        raise SystemExit(f"parameter screen missing: {path}") from exc
    except json.JSONDecodeError as exc:
        raise SystemExit(f"parameter screen is not valid JSON: {exc}") from exc
    if not isinstance(loaded, dict):
        raise SystemExit("parameter screen root must be an object")
    return loaded


def parameter_snapshot(candidate: dict[str, Any]) -> dict[str, int]:
    snapshot: dict[str, int] = {}
    name = candidate.get("name", "<unknown>")
    for field in PARAMETER_FIELDS:
        value = candidate.get(field)
        if not isinstance(value, int) or isinstance(value, bool) or value <= 0:
            raise SystemExit(f"{name}.{field} must be a positive integer")
        snapshot[field] = value
    return snapshot


def report_for_candidate(
    candidate: dict[str, Any],
    generated_at: str,
    command: list[str],
) -> dict[str, Any]:
    name = candidate.get("name")
    if not isinstance(name, str) or not name:
        raise SystemExit("candidate.name must be a non-empty string")

    margins = candidate.get("formal_proof_margins")
    if not isinstance(margins, dict):
        raise SystemExit(f"{name}.formal_proof_margins must be an object")
    runtime = candidate.get("runtime_integer_compatibility")
    if not isinstance(runtime, dict):
        raise SystemExit(f"{name}.runtime_integer_compatibility must be an object")

    base = {
        "candidate": name,
        "tool": "LaZer-style parameter generation",
        "source": "scripts/run_confidential_lazer_parameter_report.py",
        "generated_at": generated_at,
        "command": command,
        "parameter_set": parameter_snapshot(candidate),
        "assumptions": [
            "This report is structured readiness evidence, not generated LaZer parameter evidence.",
            "Production readiness requires status=generated from an actual LaZer-style parameter-generation run.",
        ],
    }

    if not margins.get("applicable", False):
        return {
            **base,
            "status": "not_applicable",
            "reason": margins.get("reason", "formal proof margins are not applicable"),
        }

    warnings = margins.get("warnings", [])
    if not isinstance(warnings, list):
        raise SystemExit(f"{name}.formal_proof_margins.warnings must be a list")
    if warnings:
        return {
            **base,
            "status": "blocked_by_formal_modulus",
            "reason": "No LaZer-style parameter generation was attempted because formal modulus checks fail.",
            "blocking_checks": warnings,
        }

    if runtime.get("compatible") is not True:
        return {
            **base,
            "status": "blocked_by_runtime_integer_model",
            "reason": (
                "No LaZer-style parameter generation was attempted because the "
                "selected parameters exceed the current runtime integer model."
            ),
            "blocking_values": runtime.get("blocking_values", {}),
            "required_for_compatibility": runtime.get("required_for_compatibility", []),
        }

    return {
        **base,
        "status": "failed",
        "reason": (
            "The candidate passed local formal-modulus and runtime-integer prechecks, "
            "but this repository-local runner is not wired to a LaZer parameter "
            "generator. Attach an externally generated report collection instead."
        ),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--parameter-screen",
        default="bench/data/confidential-parameter-screen.json",
        help="parameter-screen JSON containing confidential candidates",
    )
    parser.add_argument(
        "--out",
        default="bench/data/confidential-lazer-parameter-reports.json",
        help="output report collection path",
    )
    parser.add_argument(
        "--candidate",
        action="append",
        help="candidate name to include; may be passed more than once",
    )
    parser.add_argument(
        "--generated-at",
        help="override generated_at for reproducible tests",
    )
    args = parser.parse_args()

    parameter_screen = read_json(Path(args.parameter_screen))
    raw_candidates = parameter_screen.get("candidates")
    if not isinstance(raw_candidates, list):
        raise SystemExit("parameter screen must contain a candidates list")

    selected = set(args.candidate or [])
    generated_at = args.generated_at or datetime.now(UTC).replace(microsecond=0).isoformat()
    command = [Path(sys.argv[0]).name, *sys.argv[1:]]
    reports = [
        report_for_candidate(candidate, generated_at, command)
        for candidate in raw_candidates
        if isinstance(candidate, dict) and (not selected or candidate.get("name") in selected)
    ]
    if selected:
        found = {report["candidate"] for report in reports}
        missing = sorted(selected - found)
        if missing:
            raise SystemExit(f"candidate not found in parameter screen: {', '.join(missing)}")

    output = {
        "tool": "confidential_lazer_parameter_report_runner",
        "source": "scripts/run_confidential_lazer_parameter_report.py",
        "generated_at": generated_at,
        "parameter_screen": args.parameter_screen,
        "reports": reports,
    }
    out = Path(args.out)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(output, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(output, indent=2))


if __name__ == "__main__":
    main()
