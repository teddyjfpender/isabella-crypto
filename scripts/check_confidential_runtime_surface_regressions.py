#!/usr/bin/env python3
"""Regression tests for confidential runtime-surface gate transitions."""

from __future__ import annotations

import copy
import json
import subprocess
import tempfile
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
CHECKER = ROOT / "scripts" / "check_confidential_runtime_surface.py"
MANIFEST = ROOT / "tests" / "fixtures" / "confidential-runtime-surface.json"
DOMAIN_REGISTRY = ROOT / "tests" / "fixtures" / "confidential-domain-registry.json"


def run_checker(path: Path, require_production: bool = False) -> subprocess.CompletedProcess[str]:
    cmd = ["python3", str(CHECKER), "--manifest", str(path)]
    if require_production:
        cmd.append("--require-production")
    return subprocess.run(cmd, cwd=ROOT, check=False, capture_output=True, text=True)


def write_json(path: Path, value: dict) -> None:
    path.write_text(json.dumps(value, indent=2) + "\n", encoding="utf-8")


def expect_checker_failure(path: Path, expected: str, require_production: bool = False) -> None:
    proc = run_checker(path, require_production=require_production)
    combined = proc.stdout + proc.stderr
    if proc.returncode == 0:
        raise SystemExit(f"runtime-surface checker unexpectedly accepted {path}")
    if expected not in combined:
        raise SystemExit(
            f"runtime-surface checker failure for {path} did not include {expected!r}; got:\n{combined}"
        )


def main() -> None:
    with tempfile.TemporaryDirectory() as tmp:
        tmpdir = Path(tmp)
        base_manifest = json.loads(MANIFEST.read_text(encoding="utf-8"))
        base_path = tmpdir / "base.json"
        write_json(base_path, base_manifest)

        base_proc = run_checker(base_path)
        if base_proc.returncode != 0:
            raise SystemExit(base_proc.stdout + base_proc.stderr)

        expect_checker_failure(
            base_path,
            "runtime bignum boundary is blocked",
            require_production=True,
        )

        dishonest_ready_signed = copy.deepcopy(base_manifest)
        dishonest_ready_signed["runtimeIntegerBoundary"]["status"] = "bignum_ready"
        dishonest_ready_signed_path = tmpdir / "dishonest-ready-signed64.json"
        write_json(dishonest_ready_signed_path, dishonest_ready_signed)
        expect_checker_failure(
            dishonest_ready_signed_path,
            "bignum_ready runtimeIntegerBoundary.productionIntegerEncoding",
        )

        dishonest_ready_namespaces = copy.deepcopy(base_manifest)
        dishonest_ready_namespaces["runtimeIntegerBoundary"]["status"] = "bignum_ready"
        dishonest_ready_namespaces["runtimeIntegerBoundary"]["productionIntegerEncoding"] = (
            dishonest_ready_namespaces["runtimeIntegerBoundary"]["requiredProductionEncoding"]
        )
        dishonest_ready_namespaces_path = tmpdir / "dishonest-ready-namespaces.json"
        write_json(dishonest_ready_namespaces_path, dishonest_ready_namespaces)
        expect_checker_failure(
            dishonest_ready_namespaces_path,
            "bignum_ready runtimeIntegerBoundary.productionDomainNamespaces",
        )

        blocked_with_bignum_encoding = copy.deepcopy(base_manifest)
        blocked_with_bignum_encoding["runtimeIntegerBoundary"]["productionIntegerEncoding"] = (
            blocked_with_bignum_encoding["runtimeIntegerBoundary"]["requiredProductionEncoding"]
        )
        blocked_with_bignum_encoding_path = tmpdir / "blocked-with-bignum-encoding.json"
        write_json(blocked_with_bignum_encoding_path, blocked_with_bignum_encoding)
        expect_checker_failure(
            blocked_with_bignum_encoding_path,
            "blocked runtimeIntegerBoundary.productionIntegerEncoding",
        )

        bad_registry = json.loads(DOMAIN_REGISTRY.read_text(encoding="utf-8"))
        bad_registry["namespaces"]["merkleBignum"]["integerEncoding"] = "signed-64-bit-little-endian"
        bad_registry_path = tmpdir / "bad-domain-registry.json"
        write_json(bad_registry_path, bad_registry)
        bad_preview_manifest = copy.deepcopy(base_manifest)
        bad_preview_manifest["runtimeIntegerBoundary"]["domainRegistry"] = str(bad_registry_path)
        bad_preview_manifest_path = tmpdir / "bad-preview-registry.json"
        write_json(bad_preview_manifest_path, bad_preview_manifest)
        expect_checker_failure(
            bad_preview_manifest_path,
            "runtimeIntegerBoundary.requiredProductionEncoding disagrees with merkleBignum",
        )

    print(json.dumps({"gate": "confidential-runtime-surface-regressions", "status": "passed"}))


if __name__ == "__main__":
    main()
