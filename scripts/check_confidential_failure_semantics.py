#!/usr/bin/env python3
"""Validate confidential-transfer failure-semantics coverage tracking."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "tests" / "fixtures" / "confidential-failure-semantics.json"


def fail(message: str) -> None:
    raise SystemExit(message)


def read_text(path: Path) -> str:
    try:
        return path.read_text(encoding="utf-8")
    except FileNotFoundError:
        fail(f"required file is missing: {path.relative_to(ROOT)}")


def read_json(path: Path) -> dict[str, Any]:
    try:
        loaded = json.loads(path.read_text(encoding="utf-8"))
    except FileNotFoundError:
        fail(f"failure-semantics manifest missing: {path.relative_to(ROOT)}")
    except json.JSONDecodeError as exc:
        fail(f"failure-semantics manifest is not valid JSON: {exc}")
    if not isinstance(loaded, dict):
        fail("failure-semantics manifest root must be an object")
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


def check_protocol_spec(manifest: dict[str, Any]) -> dict[str, int]:
    spec = require_object(manifest.get("protocolSpec"), "protocolSpec")
    path = path_from_manifest(spec.get("file"), "protocolSpec.file")
    snippets = require_string_list(spec.get("requiredSnippets"), "protocolSpec.requiredSnippets")
    require_snippets(path, snippets, "protocol failure-semantics spec snippet")
    return {"snippets": len(snippets)}


def check_evidence_list(raw_evidence: Any, label: str) -> int:
    evidence_items = require_list(raw_evidence, label)
    if not evidence_items:
        fail(f"{label} must not be empty")
    checked = 0
    for index, raw_item in enumerate(evidence_items):
        item = require_object(raw_item, f"{label}[{index}]")
        path = path_from_manifest(item.get("file"), f"{label}[{index}].file")
        snippets = require_string_list(item.get("snippets"), f"{label}[{index}].snippets")
        require_snippets(path, snippets, "failure-semantics evidence snippet")
        checked += len(snippets)
    return checked


def check_failure_classes(manifest: dict[str, Any]) -> dict[str, int]:
    spec = require_object(manifest.get("protocolSpec"), "protocolSpec")
    spec_path = path_from_manifest(spec.get("file"), "protocolSpec.file")
    classes = require_list(manifest.get("failureClasses"), "failureClasses")
    if not classes:
        fail("failureClasses must not be empty")

    ids: set[str] = set()
    evidence_snippets = 0
    covered = 0
    open_count = 0
    for index, raw_class in enumerate(classes):
        item = require_object(raw_class, f"failureClasses[{index}]")
        class_id = require_string(item.get("id"), f"failureClasses[{index}].id")
        if class_id in ids:
            fail(f"duplicate failure class id: {class_id}")
        ids.add(class_id)
        status = require_string(item.get("status"), f"failureClasses[{index}].status")
        if status not in {"covered", "open"}:
            fail(f"{class_id} has invalid status: {status}")
        spec_snippets = require_string_list(
            item.get("specSnippets"),
            f"failureClasses[{index}].specSnippets",
        )
        require_snippets(spec_path, spec_snippets, f"{class_id} spec snippet")
        evidence_snippets += check_evidence_list(
            item.get("evidence"),
            f"failureClasses[{index}].evidence",
        )
        if status == "covered":
            covered += 1
        else:
            open_count += 1

    return {
        "classes": len(classes),
        "covered": covered,
        "open": open_count,
        "evidence_snippets": evidence_snippets,
    }


def check_production_limitations(manifest: dict[str, Any]) -> dict[str, int]:
    limitations = require_list(manifest.get("productionLimitations"), "productionLimitations")
    ids: set[str] = set()
    open_count = 0
    evidence_snippets = 0
    for index, raw_item in enumerate(limitations):
        item = require_object(raw_item, f"productionLimitations[{index}]")
        limitation_id = require_string(item.get("id"), f"productionLimitations[{index}].id")
        if limitation_id in ids:
            fail(f"duplicate production limitation id: {limitation_id}")
        ids.add(limitation_id)
        status = require_string(item.get("status"), f"productionLimitations[{index}].status")
        if status not in {"closed", "open"}:
            fail(f"{limitation_id} has invalid status: {status}")
        if status == "open":
            open_count += 1
        evidence_snippets += check_evidence_list(
            item.get("evidence"),
            f"productionLimitations[{index}].evidence",
        )
    return {
        "limitations": len(limitations),
        "open": open_count,
        "evidence_snippets": evidence_snippets,
    }


def check_gate_wiring(manifest: dict[str, Any]) -> dict[str, int]:
    wiring = require_object(manifest.get("gateWiring"), "gateWiring")
    checked = 0
    for raw_path, raw_snippets in wiring.items():
        path = path_from_manifest(raw_path, f"gateWiring.{raw_path}")
        snippets = require_string_list(raw_snippets, f"gateWiring.{raw_path}")
        require_snippets(path, snippets, "failure-semantics gate wiring")
        checked += len(snippets)
    return {"snippets": checked}


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--require-production",
        action="store_true",
        help="fail while any failure class or production limitation remains open",
    )
    args = parser.parse_args()

    manifest = read_json(MANIFEST)
    if manifest.get("version") != 1:
        fail("failure-semantics manifest version must be 1")

    summary = {
        "protocol_spec": check_protocol_spec(manifest),
        "failure_classes": check_failure_classes(manifest),
        "production_limitations": check_production_limitations(manifest),
        "gate_wiring": check_gate_wiring(manifest),
    }

    open_classes = summary["failure_classes"]["open"]
    open_limitations = summary["production_limitations"]["open"]
    if args.require_production and (open_classes > 0 or open_limitations > 0):
        fail(
            "failure-semantics production gate is blocked: "
            f"{open_classes} open failure classes, {open_limitations} open production limitations"
        )

    print(json.dumps({
        "gate": "confidential-failure-semantics",
        "status": "passed",
        "manifest": str(MANIFEST.relative_to(ROOT)),
        "require_production": args.require_production,
        "summary": summary,
    }, indent=2))


if __name__ == "__main__":
    main()
