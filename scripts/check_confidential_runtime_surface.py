#!/usr/bin/env python3
"""Validate the confidential-transfer runtime surface manifest."""

from __future__ import annotations

import argparse
import json
import re
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "tests" / "fixtures" / "confidential-runtime-surface.json"
COMMAND_PATTERN = re.compile(r"""["'](ct-[A-Za-z0-9-]+)["']""")


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
        fail(f"runtime-surface manifest missing: {path.relative_to(ROOT)}")
    except json.JSONDecodeError as exc:
        fail(f"runtime-surface manifest is not valid JSON: {exc}")
    if not isinstance(loaded, dict):
        fail("runtime-surface manifest root must be an object")
    return loaded


def require_list(value: Any, label: str) -> list[Any]:
    if not isinstance(value, list):
        fail(f"{label} must be a list")
    return value


def require_string_list(value: Any, label: str) -> list[str]:
    values = require_list(value, label)
    if not all(isinstance(item, str) and item for item in values):
        fail(f"{label} must contain non-empty strings")
    if len(values) != len(set(values)):
        fail(f"{label} must not contain duplicates")
    return values


def require_object(value: Any, label: str) -> dict[str, Any]:
    if not isinstance(value, dict):
        fail(f"{label} must be an object")
    return value


def require_string(value: Any, label: str) -> str:
    if not isinstance(value, str) or not value:
        fail(f"{label} must be a non-empty string")
    return value


def path_from_manifest(value: Any, label: str) -> Path:
    if not isinstance(value, str) or not value:
        fail(f"{label} must be a non-empty path string")
    path = ROOT / value
    if not path.is_file():
        fail(f"{label} points at a missing file: {value}")
    return path


def quoted_commands(path: Path) -> set[str]:
    return set(COMMAND_PATTERN.findall(read_text(path)))


def require_snippet(path: Path, snippet: str, label: str) -> None:
    if snippet not in read_text(path):
        fail(f"{path.relative_to(ROOT)} is missing {label}: {snippet}")


def forbid_snippet(path: Path, snippet: str, label: str) -> None:
    if snippet in read_text(path):
        fail(f"{path.relative_to(ROOT)} still contains forbidden {label}: {snippet}")


def require_export(path: Path, export_name: str, label: str) -> None:
    pattern = re.compile(rf"\bexport\s+function\s+{re.escape(export_name)}\b")
    if pattern.search(read_text(path)) is None:
        fail(f"{path.relative_to(ROOT)} is missing {label} export: {export_name}")


def forbid_export(path: Path, export_name: str, label: str) -> None:
    pattern = re.compile(
        rf"\bexport\s+(?:function|const|let|var)\s+{re.escape(export_name)}\b"
    )
    if pattern.search(read_text(path)) is not None:
        fail(f"{path.relative_to(ROOT)} contains forbidden {label} export: {export_name}")


def check_native_cli(manifest: dict[str, Any]) -> dict[str, int]:
    native = require_object(manifest.get("nativeCli"), "nativeCli")
    ocaml_path = path_from_manifest(native.get("ocamlDispatch"), "nativeCli.ocamlDispatch")
    haskell_path = path_from_manifest(native.get("haskellDispatch"), "nativeCli.haskellDispatch")
    help_path = path_from_manifest(native.get("haskellHelp"), "nativeCli.haskellHelp")
    production_commands = require_string_list(
        native.get("productionCommands"),
        "nativeCli.productionCommands",
    )
    haskell_preview_commands = require_string_list(
        native.get("haskellPreviewCommands", []),
        "nativeCli.haskellPreviewCommands",
    )
    ocaml_preview_commands = require_string_list(
        native.get("ocamlPreviewCommands", []),
        "nativeCli.ocamlPreviewCommands",
    )
    scaffold_commands = require_string_list(
        native.get("scaffoldCommands"),
        "nativeCli.scaffoldCommands",
    )
    scaffold_opt_in_env = native.get("scaffoldOptInEnv")
    if scaffold_opt_in_env != "ISABELLA_ENABLE_SCAFFOLD_COMPAT":
        fail("nativeCli.scaffoldOptInEnv must be ISABELLA_ENABLE_SCAFFOLD_COMPAT")
    retired_commands = require_string_list(
        native.get("retiredCommands"),
        "nativeCli.retiredCommands",
    )
    required_commands = production_commands + scaffold_commands

    for path in (ocaml_path, haskell_path):
        commands = quoted_commands(path)
        missing = sorted(command for command in required_commands if command not in commands)
        if missing:
            fail(f"{path.relative_to(ROOT)} is missing native confidential commands: {missing}")
        require_snippet(path, scaffold_opt_in_env, "native scaffold opt-in guard")
        retired_present = sorted(command for command in retired_commands if command in commands)
        if retired_present:
            fail(f"{path.relative_to(ROOT)} reintroduces retired scaffold commands: {retired_present}")

    haskell_commands = quoted_commands(haskell_path)
    missing_haskell_preview = sorted(
        command for command in haskell_preview_commands if command not in haskell_commands
    )
    if missing_haskell_preview:
        fail(
            f"{haskell_path.relative_to(ROOT)} is missing Haskell preview confidential commands: "
            f"{missing_haskell_preview}"
        )

    ocaml_commands = quoted_commands(ocaml_path)
    missing_ocaml_preview = sorted(
        command for command in ocaml_preview_commands if command not in ocaml_commands
    )
    if missing_ocaml_preview:
        fail(
            f"{ocaml_path.relative_to(ROOT)} is missing OCaml preview confidential commands: "
            f"{missing_ocaml_preview}"
        )

    for command in required_commands + haskell_preview_commands:
        require_snippet(help_path, command, "Haskell CLI help command")
    for command in ocaml_preview_commands:
        require_snippet(ocaml_path, command, "OCaml CLI help command")

    return {
        "production_commands": len(production_commands),
        "haskell_preview_commands": len(haskell_preview_commands),
        "ocaml_preview_commands": len(ocaml_preview_commands),
        "scaffold_commands": len(scaffold_commands),
        "retired_commands": len(retired_commands),
    }


def check_typescript_cli(manifest: dict[str, Any]) -> dict[str, int]:
    ts_cli = require_object(manifest.get("typescriptCliHarness"), "typescriptCliHarness")
    path = path_from_manifest(ts_cli.get("file"), "typescriptCliHarness.file")
    required_exports = require_string_list(
        ts_cli.get("requiredExports"),
        "typescriptCliHarness.requiredExports",
    )
    forbidden_exports = require_string_list(
        ts_cli.get("forbiddenExports"),
        "typescriptCliHarness.forbiddenExports",
    )
    for export_name in required_exports:
        require_export(path, export_name, "TypeScript CLI harness")
    for export_name in forbidden_exports:
        forbid_export(path, export_name, "TypeScript CLI harness")
    return {
        "required_exports": len(required_exports),
        "forbidden_exports": len(forbidden_exports),
    }


def check_typescript_sdk(manifest: dict[str, Any]) -> dict[str, int]:
    sdk = require_object(manifest.get("typescriptSdk"), "typescriptSdk")
    path = path_from_manifest(sdk.get("file"), "typescriptSdk.file")
    namespaces = require_object(sdk.get("namespaces"), "typescriptSdk.namespaces")
    export_count = 0
    for namespace, exports in namespaces.items():
        if not isinstance(namespace, str) or not namespace:
            fail("typescriptSdk.namespaces keys must be non-empty strings")
        require_snippet(path, f"export namespace {namespace}", "TypeScript SDK namespace")
        for export_name in require_string_list(exports, f"typescriptSdk.namespaces.{namespace}"):
            require_export(path, export_name, f"TypeScript SDK {namespace}")
            export_count += 1

    for snippet in require_string_list(
        sdk.get("requiredSnippets"),
        "typescriptSdk.requiredSnippets",
    ):
        require_snippet(path, snippet, "TypeScript SDK production-boundary snippet")
    for snippet in require_string_list(
        sdk.get("forbiddenSnippets"),
        "typescriptSdk.forbiddenSnippets",
    ):
        forbid_snippet(path, snippet, "TypeScript SDK production-boundary snippet")
    return {"required_exports": export_count}


def check_runtime_integer_boundary(
    manifest: dict[str, Any],
    require_production: bool,
) -> dict[str, Any]:
    boundary = require_object(
        manifest.get("runtimeIntegerBoundary"),
        "runtimeIntegerBoundary",
    )
    status = require_string(boundary.get("status"), "runtimeIntegerBoundary.status")
    allowed_statuses = {"blocked_by_transaction_i64_encoding", "bignum_ready"}
    if status not in allowed_statuses:
        fail(f"runtimeIntegerBoundary.status must be one of {sorted(allowed_statuses)}")
    if require_production and status != "bignum_ready":
        fail(f"runtime bignum boundary is blocked: status={status}")

    production_encoding = require_string(
        boundary.get("productionIntegerEncoding"),
        "runtimeIntegerBoundary.productionIntegerEncoding",
    )
    required_encoding = require_string(
        boundary.get("requiredProductionEncoding"),
        "runtimeIntegerBoundary.requiredProductionEncoding",
    )
    if production_encoding != "signed-64-bit-little-endian":
        fail("runtimeIntegerBoundary.productionIntegerEncoding is stale")
    if required_encoding != "sign_u8 || len_i64_le || magnitude_le_minimal":
        fail("runtimeIntegerBoundary.requiredProductionEncoding must be the confidential bignum codec")

    registry_path = path_from_manifest(
        boundary.get("domainRegistry"),
        "runtimeIntegerBoundary.domainRegistry",
    )
    registry = read_json(registry_path)
    namespaces = require_object(registry.get("namespaces"), "domain registry namespaces")
    for namespace_name in ("merkle", "transaction"):
        namespace = require_object(namespaces.get(namespace_name), f"domain registry {namespace_name}")
        actual_encoding = require_string(
            namespace.get("integerEncoding"),
            f"domain registry {namespace_name}.integerEncoding",
        )
        if actual_encoding != production_encoding:
            fail(
                f"runtimeIntegerBoundary.productionIntegerEncoding disagrees with "
                f"{namespace_name} registry encoding: {actual_encoding}"
            )

    sdk_path = path_from_manifest(
        boundary.get("typescriptSdkFile"),
        "runtimeIntegerBoundary.typescriptSdkFile",
    )
    i64_snippets = require_string_list(
        boundary.get("i64TransactionSnippets"),
        "runtimeIntegerBoundary.i64TransactionSnippets",
    )
    preview_snippets = require_string_list(
        boundary.get("bigintPreviewSnippets"),
        "runtimeIntegerBoundary.bigintPreviewSnippets",
    )
    for snippet in i64_snippets:
        require_snippet(sdk_path, snippet, "runtime i64 transaction-boundary snippet")
    for snippet in preview_snippets:
        require_snippet(sdk_path, snippet, "runtime BigInt preview snippet")
    require_string_list(
        boundary.get("requiredForProduction"),
        "runtimeIntegerBoundary.requiredForProduction",
    )
    return {
        "status": status,
        "production_integer_encoding": production_encoding,
        "required_production_encoding": required_encoding,
        "i64_transaction_snippets": len(i64_snippets),
        "bigint_preview_snippets": len(preview_snippets),
    }


def check_validator_coverage(manifest: dict[str, Any]) -> dict[str, int]:
    validators = require_object(manifest.get("validators"), "validators")
    checked = 0
    for raw_path, commands in validators.items():
        if not isinstance(raw_path, str) or not raw_path:
            fail("validators keys must be non-empty path strings")
        path = path_from_manifest(raw_path, f"validators.{raw_path}")
        text = read_text(path)
        for command in require_string_list(commands, f"validators.{raw_path}"):
            if command not in text:
                fail(f"{raw_path} is missing validator coverage marker: {command}")
            checked += 1
    return {"markers": checked}


def check_gate_wiring(manifest: dict[str, Any]) -> dict[str, int]:
    wiring = require_object(manifest.get("gateWiring"), "gateWiring")
    checked = 0
    for raw_path, snippets in wiring.items():
        if not isinstance(raw_path, str) or not raw_path:
            fail("gateWiring keys must be non-empty path strings")
        path = path_from_manifest(raw_path, f"gateWiring.{raw_path}")
        for snippet in require_string_list(snippets, f"gateWiring.{raw_path}"):
            require_snippet(path, snippet, "runtime-surface gate wiring")
            checked += 1
    return {"snippets": checked}


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--require-production",
        action="store_true",
        help="fail unless the runtime integer boundary is production bignum-ready",
    )
    args = parser.parse_args()

    manifest = read_json(MANIFEST)
    if manifest.get("version") != 1:
        fail("runtime-surface manifest version must be 1")

    summary = {
        "native_cli": check_native_cli(manifest),
        "typescript_cli_harness": check_typescript_cli(manifest),
        "typescript_sdk": check_typescript_sdk(manifest),
        "runtime_integer_boundary": check_runtime_integer_boundary(
            manifest,
            args.require_production,
        ),
        "validator_coverage": check_validator_coverage(manifest),
        "gate_wiring": check_gate_wiring(manifest),
    }

    print(json.dumps({
        "gate": "confidential-runtime-surface",
        "status": "passed",
        "manifest": str(MANIFEST.relative_to(ROOT)),
        "require_production": args.require_production,
        "summary": summary,
    }, indent=2))


if __name__ == "__main__":
    main()
