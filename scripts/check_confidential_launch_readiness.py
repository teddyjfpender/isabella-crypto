#!/usr/bin/env python3
"""Validate the confidential-transfer launch-readiness manifest.

The default mode is an honesty gate: it passes while the manifest accurately
records the current non-production blockers and evidence snippets. Strict mode
is a release gate and fails until production claims are allowed, the parameter
screen is ready, and no launch blocker remains open.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "tests" / "fixtures" / "confidential-launch-readiness.json"
BLOCKER_STATUSES = {"open", "closed", "mvp_excluded"}
OPEN_STATUSES = {"open"}


def fail(message: str) -> None:
    raise SystemExit(message)


def read_text(path: Path) -> str:
    try:
        return path.read_text(encoding="utf-8")
    except FileNotFoundError:
        fail(f"required file is missing: {path.relative_to(ROOT)}")


def read_json(path: Path, label: str) -> dict[str, Any]:
    try:
        loaded = json.loads(path.read_text(encoding="utf-8"))
    except FileNotFoundError:
        fail(f"{label} missing: {path.relative_to(ROOT)}")
    except json.JSONDecodeError as exc:
        fail(f"{label} is not valid JSON: {exc}")
    if not isinstance(loaded, dict):
        fail(f"{label} root must be an object")
    return loaded


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


def require_string_list(value: Any, label: str) -> list[str]:
    values = require_list(value, label)
    if not all(isinstance(item, str) and item for item in values):
        fail(f"{label} must contain non-empty strings")
    if len(values) != len(set(values)):
        fail(f"{label} must not contain duplicates")
    return values


def path_from_manifest(value: Any, label: str) -> Path:
    raw_path = require_string(value, label)
    path = ROOT / raw_path
    if not path.is_file():
        fail(f"{label} points at a missing file: {raw_path}")
    return path


def require_snippets(path: Path, snippets: list[str], label: str) -> None:
    text = read_text(path)
    for snippet in snippets:
        if snippet not in text:
            fail(f"{path.relative_to(ROOT)} is missing {label}: {snippet}")


def check_evidence(raw_evidence: Any, label: str) -> int:
    evidence = require_list(raw_evidence, label)
    if not evidence:
        fail(f"{label} must not be empty")
    checked = 0
    for index, raw_item in enumerate(evidence):
        item = require_object(raw_item, f"{label}[{index}]")
        path = path_from_manifest(item.get("file"), f"{label}[{index}].file")
        snippets = require_string_list(item.get("snippets"), f"{label}[{index}].snippets")
        require_snippets(path, snippets, "launch-readiness evidence snippet")
        checked += len(snippets)
    return checked


def check_launch_scope(manifest: dict[str, Any]) -> dict[str, int | bool | str]:
    scope = require_object(manifest.get("launchScope"), "launchScope")
    target = require_string(scope.get("target"), "launchScope.target")
    production_allowed = scope.get("productionClaimAllowed")
    if not isinstance(production_allowed, bool):
        fail("launchScope.productionClaimAllowed must be a boolean")
    included = require_string_list(scope.get("includedRelations"), "launchScope.includedRelations")
    excluded = require_string_list(scope.get("excludedRelations"), "launchScope.excludedRelations")
    overlap = sorted(set(included) & set(excluded))
    if overlap:
        fail(f"launch scope includes and excludes the same relations: {overlap}")
    evidence_snippets = check_evidence(scope.get("evidence"), "launchScope.evidence")
    return {
        "target": target,
        "production_claim_allowed": production_allowed,
        "included_relations": len(included),
        "excluded_relations": len(excluded),
        "evidence_snippets": evidence_snippets,
    }


def check_parameter_report(manifest: dict[str, Any]) -> dict[str, str | bool]:
    spec = require_object(manifest.get("parameterReport"), "parameterReport")
    path = path_from_manifest(spec.get("file"), "parameterReport.file")
    expected_status = require_string(spec.get("expectedStatus"), "parameterReport.expectedStatus")
    required_production_status = require_string(
        spec.get("requiredProductionStatus"),
        "parameterReport.requiredProductionStatus",
    )
    require_snippets(
        path,
        require_string_list(spec.get("requiredSnippets"), "parameterReport.requiredSnippets"),
        "launch-readiness parameter-report snippet",
    )

    report = read_json(path, "parameter report")
    launch = require_object(report.get("launch_readiness"), "parameter report launch_readiness")
    actual_status = require_string(launch.get("status"), "parameter report launch_readiness.status")
    ready = launch.get("ready")
    if not isinstance(ready, bool):
        fail("parameter report launch_readiness.ready must be a boolean")
    if actual_status != expected_status:
        fail(
            "parameterReport.expectedStatus is stale: "
            f"expected {expected_status}, actual {actual_status}"
        )
    if required_production_status != "ready":
        fail("parameterReport.requiredProductionStatus must be ready")
    if ready != (actual_status == "ready"):
        fail("parameter report launch_readiness.ready disagrees with status")
    return {
        "file": str(path.relative_to(ROOT)),
        "status": actual_status,
        "ready": ready,
    }


def check_launch_blockers(manifest: dict[str, Any]) -> dict[str, Any]:
    blockers = require_list(manifest.get("launchBlockers"), "launchBlockers")
    if not blockers:
        fail("launchBlockers must not be empty")
    ids: set[str] = set()
    open_ids: list[str] = []
    non_open_ids: list[str] = []
    evidence_snippets = 0
    for index, raw_blocker in enumerate(blockers):
        blocker = require_object(raw_blocker, f"launchBlockers[{index}]")
        blocker_id = require_string(blocker.get("id"), f"launchBlockers[{index}].id")
        if blocker_id in ids:
            fail(f"duplicate launch blocker id: {blocker_id}")
        ids.add(blocker_id)
        require_string(blocker.get("category"), f"launchBlockers[{index}].category")
        status = require_string(blocker.get("status"), f"launchBlockers[{index}].status")
        if status not in BLOCKER_STATUSES:
            fail(f"{blocker_id} has invalid status: {status}")
        require_string(blocker.get("summary"), f"launchBlockers[{index}].summary")
        require_string(blocker.get("acceptanceGate"), f"launchBlockers[{index}].acceptanceGate")
        evidence_snippets += check_evidence(
            blocker.get("evidence"),
            f"launchBlockers[{index}].evidence",
        )
        if status in OPEN_STATUSES:
            open_ids.append(blocker_id)
        else:
            non_open_ids.append(blocker_id)

    return {
        "blockers": len(blockers),
        "open": len(open_ids),
        "non_open": len(non_open_ids),
        "open_ids": open_ids,
        "non_open_ids": non_open_ids,
        "evidence_snippets": evidence_snippets,
    }


def check_gate_wiring(manifest: dict[str, Any]) -> dict[str, int]:
    wiring = require_object(manifest.get("gateWiring"), "gateWiring")
    checked = 0
    for raw_path, raw_snippets in wiring.items():
        if not isinstance(raw_path, str) or not raw_path:
            fail("gateWiring keys must be non-empty path strings")
        path = path_from_manifest(raw_path, f"gateWiring.{raw_path}")
        snippets = require_string_list(raw_snippets, f"gateWiring.{raw_path}")
        require_snippets(path, snippets, "launch-readiness gate wiring")
        checked += len(snippets)
    return {"snippets": checked}


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--require-production",
        action="store_true",
        help="fail unless the launch-readiness manifest permits production claims",
    )
    args = parser.parse_args()

    manifest = read_json(MANIFEST, "launch-readiness manifest")
    if manifest.get("version") != 1:
        fail("launch-readiness manifest version must be 1")

    summary = {
        "launch_scope": check_launch_scope(manifest),
        "parameter_report": check_parameter_report(manifest),
        "launch_blockers": check_launch_blockers(manifest),
        "gate_wiring": check_gate_wiring(manifest),
    }

    production_allowed = bool(summary["launch_scope"]["production_claim_allowed"])
    parameter_ready = bool(summary["parameter_report"]["ready"])
    open_blockers = int(summary["launch_blockers"]["open"])

    if production_allowed and (open_blockers > 0 or not parameter_ready):
        fail(
            "launchScope.productionClaimAllowed cannot be true while "
            f"{open_blockers} launch blockers remain open and parameter_ready={parameter_ready}"
        )

    if args.require_production and (not production_allowed or open_blockers > 0 or not parameter_ready):
        fail(
            "confidential launch-readiness gate is blocked: "
            f"productionClaimAllowed={production_allowed}, "
            f"parameter_ready={parameter_ready}, open_blockers={open_blockers}, "
            f"open_ids={summary['launch_blockers']['open_ids']}"
        )

    print(json.dumps({
        "gate": "confidential-launch-readiness",
        "status": "passed",
        "manifest": str(MANIFEST.relative_to(ROOT)),
        "require_production": args.require_production,
        "summary": summary,
    }, indent=2))


if __name__ == "__main__":
    main()
