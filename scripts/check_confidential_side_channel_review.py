#!/usr/bin/env python3
"""Validate confidential-transfer side-channel review tracking."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "tests" / "fixtures" / "confidential-side-channel-review.json"

REQUIRED_REVIEW_IDS = {
    "typescript_csprng_sampling",
    "native_csprng_sampling",
    "prover_secret_path_boundary",
    "verifier_public_input_boundary",
    "canonical_serialization_public_boundary",
    "scaffold_benchmark_boundary",
}
REVIEW_STATUSES = {"reviewed", "accepted_residual"}
RESIDUAL_STATUSES = {"accepted_for_reference_mvp", "required_before_launch", "signed_off"}


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
        fail(f"side-channel review manifest missing: {path.relative_to(ROOT)}")
    except json.JSONDecodeError as exc:
        fail(f"side-channel review manifest is not valid JSON: {exc}")
    if not isinstance(loaded, dict):
        fail("side-channel review manifest root must be an object")
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


def check_scope(manifest: dict[str, Any]) -> dict[str, int]:
    scope = require_object(manifest.get("scope"), "scope")
    require_string(scope.get("reviewDate"), "scope.reviewDate")
    require_string(scope.get("target"), "scope.target")
    boundary = require_string(scope.get("boundary"), "scope.boundary")
    for required in (
        "Verifier, serializer, digest, Merkle, envelope, and root-window paths operate on public transaction data.",
        "not constant-time kernels",
    ):
        if required not in boundary:
            fail(f"scope.boundary must document: {required}")
    secret_data = require_string_list(manifest.get("secretData"), "secretData")
    public_data = require_string_list(manifest.get("publicData"), "publicData")
    return {
        "secret_data_classes": len(secret_data),
        "public_data_classes": len(public_data),
    }


def check_evidence(raw_evidence: Any, label: str) -> int:
    evidence_items = require_list(raw_evidence, label)
    if not evidence_items:
        fail(f"{label} must not be empty")
    checked = 0
    for index, raw_item in enumerate(evidence_items):
        item = require_object(raw_item, f"{label}[{index}]")
        path = path_from_manifest(item.get("file"), f"{label}[{index}].file")
        snippets = require_string_list(item.get("snippets"), f"{label}[{index}].snippets")
        require_snippets(path, snippets, "side-channel evidence snippet")
        checked += len(snippets)
    return checked


def check_review_items(manifest: dict[str, Any]) -> dict[str, int]:
    items = require_list(manifest.get("reviewItems"), "reviewItems")
    ids: set[str] = set()
    residual_items = 0
    evidence_snippets = 0
    for index, raw_item in enumerate(items):
        item = require_object(raw_item, f"reviewItems[{index}]")
        item_id = require_string(item.get("id"), f"reviewItems[{index}].id")
        if item_id in ids:
            fail(f"duplicate side-channel review item id: {item_id}")
        ids.add(item_id)
        status = require_string(item.get("status"), f"reviewItems[{index}].status")
        if status not in REVIEW_STATUSES:
            fail(f"{item_id} has invalid side-channel review status: {status}")
        if status == "accepted_residual":
            residual_items += 1
        require_string(item.get("dataClass"), f"reviewItems[{index}].dataClass")
        require_string(item.get("finding"), f"reviewItems[{index}].finding")
        evidence_snippets += check_evidence(item.get("evidence"), f"reviewItems[{index}].evidence")

    missing = sorted(REQUIRED_REVIEW_IDS - ids)
    if missing:
        fail(f"side-channel review manifest is missing required review item ids: {missing}")
    extra = sorted(ids - REQUIRED_REVIEW_IDS)
    if extra:
        fail(f"side-channel review manifest has unexpected review item ids: {extra}")

    return {
        "items": len(items),
        "accepted_residual": residual_items,
        "evidence_snippets": evidence_snippets,
    }


def check_residual_risks(manifest: dict[str, Any]) -> dict[str, int]:
    risks = require_list(manifest.get("residualRisks"), "residualRisks")
    if not risks:
        fail("residualRisks must not be empty")
    ids: set[str] = set()
    launch_required = 0
    signed_off = 0
    for index, raw_risk in enumerate(risks):
        risk = require_object(raw_risk, f"residualRisks[{index}]")
        risk_id = require_string(risk.get("id"), f"residualRisks[{index}].id")
        if risk_id in ids:
            fail(f"duplicate residual risk id: {risk_id}")
        ids.add(risk_id)
        status = require_string(risk.get("status"), f"residualRisks[{index}].status")
        if status not in RESIDUAL_STATUSES:
            fail(f"{risk_id} has invalid residual risk status: {status}")
        require_string(risk.get("mitigation"), f"residualRisks[{index}].mitigation")
        require_string(risk.get("launchCondition"), f"residualRisks[{index}].launchCondition")
        if status == "required_before_launch":
            launch_required += 1
        if status == "signed_off":
            signed_off += 1
    return {
        "risks": len(risks),
        "required_before_launch": launch_required,
        "signed_off": signed_off,
    }


def check_external_review(manifest: dict[str, Any]) -> dict[str, int | str]:
    review = require_object(manifest.get("externalReview"), "externalReview")
    status = require_string(review.get("status"), "externalReview.status")
    if status not in {"required_before_launch", "signed_off"}:
        fail(f"externalReview.status has invalid status: {status}")
    evidence_snippets = check_evidence(review.get("evidence"), "externalReview.evidence")
    return {
        "status": status,
        "evidence_snippets": evidence_snippets,
    }


def check_gate_wiring(manifest: dict[str, Any]) -> dict[str, int]:
    wiring = require_object(manifest.get("gateWiring"), "gateWiring")
    checked = 0
    for raw_path, raw_snippets in wiring.items():
        path = path_from_manifest(raw_path, f"gateWiring.{raw_path}")
        snippets = require_string_list(raw_snippets, f"gateWiring.{raw_path}")
        require_snippets(path, snippets, "side-channel gate wiring")
        checked += len(snippets)
    return {"snippets": checked}


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--require-production",
        action="store_true",
        help="fail unless the side-channel review has external production signoff",
    )
    args = parser.parse_args()

    manifest = read_json(MANIFEST)
    if manifest.get("version") != 1:
        fail("side-channel review manifest version must be 1")

    summary = {
        "scope": check_scope(manifest),
        "review_items": check_review_items(manifest),
        "residual_risks": check_residual_risks(manifest),
        "external_review": check_external_review(manifest),
        "gate_wiring": check_gate_wiring(manifest),
    }

    external_status = summary["external_review"]["status"]
    if args.require_production and external_status != "signed_off":
        fail(
            "side-channel production gate is blocked: "
            f"externalReview.status is {external_status}, not signed_off"
        )

    print(json.dumps({
        "gate": "confidential-side-channel-review",
        "status": "passed",
        "manifest": str(MANIFEST.relative_to(ROOT)),
        "require_production": args.require_production,
        "summary": summary,
    }, indent=2))


if __name__ == "__main__":
    main()
