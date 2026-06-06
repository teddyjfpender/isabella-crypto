#!/usr/bin/env python3
"""Regression tests for confidential parameter-readiness report validation."""

from __future__ import annotations

import copy
import json
import subprocess
import tempfile
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SCREEN = ROOT / "scripts" / "confidential_parameter_screen.py"
CHECKER = ROOT / "scripts" / "check_confidential_parameter_readiness.py"


def run(cmd: list[str]) -> subprocess.CompletedProcess[str]:
    return subprocess.run(cmd, cwd=ROOT, check=False, capture_output=True, text=True)


def write_report(path: Path, report: dict) -> None:
    path.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")


def matching_parameters(candidate: dict) -> dict:
    fields = ("n1", "n2", "m", "q", "beta", "gamma", "range_bits", "fs_rounds")
    return {field: candidate[field] for field in fields}


def estimator_report(candidate: dict, security_bits: int, parameters: dict) -> dict:
    return {
        "candidate": candidate["name"],
        "tool": "regression-estimator",
        "source": "scripts/check_confidential_parameter_readiness_regressions.py",
        "generated_at": "2026-06-06T00:00:00Z",
        "command": ["regression-estimator", candidate["name"]],
        "security_level_bits": security_bits,
        "parameters": parameters,
        "assumptions": ["regression fixture; not production estimator evidence"],
    }


def lazer_report(candidate: dict, security_bits: int, parameter_set: dict) -> dict:
    return {
        "candidate": candidate["name"],
        "tool": "regression-lazer-params",
        "source": "scripts/check_confidential_parameter_readiness_regressions.py",
        "generated_at": "2026-06-06T00:00:00Z",
        "command": ["regression-lazer-params", candidate["name"]],
        "security_level_bits": security_bits,
        "parameter_set": parameter_set,
        "proof_size_estimate": {"bytes": 1},
    }


def expect_checker_failure(path: Path, expected: str) -> None:
    proc = run(["python3", str(CHECKER), "--report", str(path)])
    combined = proc.stdout + proc.stderr
    if proc.returncode == 0:
        raise SystemExit(f"checker unexpectedly accepted {path}")
    if expected not in combined:
        raise SystemExit(
            f"checker failure for {path} did not include {expected!r}; got:\n{combined}"
        )


def main() -> None:
    with tempfile.TemporaryDirectory() as tmp:
        tmpdir = Path(tmp)
        base_path = tmpdir / "base.json"
        screen_proc = run(["python3", str(SCREEN), "--out", str(base_path)])
        if screen_proc.returncode != 0:
            raise SystemExit(screen_proc.stdout + screen_proc.stderr)
        checker_proc = run(["python3", str(CHECKER), "--report", str(base_path)])
        if checker_proc.returncode != 0:
            raise SystemExit(checker_proc.stdout + checker_proc.stderr)

        base_report = json.loads(base_path.read_text(encoding="utf-8"))
        candidate = base_report["candidates"][0]
        params = matching_parameters(candidate)

        low_security = copy.deepcopy(base_report)
        low_security["candidates"][0]["external_lattice_estimator_report"] = estimator_report(
            candidate,
            candidate["target_security_bits"] - 1,
            params,
        )
        low_security_path = tmpdir / "low-security.json"
        write_report(low_security_path, low_security)
        expect_checker_failure(low_security_path, "below target_security_bits")

        mismatched_estimator = copy.deepcopy(base_report)
        bad_params = dict(params)
        bad_params["q"] = bad_params["q"] + 1
        mismatched_estimator["candidates"][0]["external_lattice_estimator_report"] = estimator_report(
            candidate,
            candidate["target_security_bits"],
            bad_params,
        )
        mismatched_estimator_path = tmpdir / "mismatched-estimator.json"
        write_report(mismatched_estimator_path, mismatched_estimator)
        expect_checker_failure(mismatched_estimator_path, "parameters.q must equal")

        mismatched_lazer = copy.deepcopy(base_report)
        bad_lazer_params = dict(params)
        bad_lazer_params["fs_rounds"] = bad_lazer_params["fs_rounds"] - 1
        mismatched_lazer["candidates"][0]["lazer_parameter_generation_report"] = lazer_report(
            candidate,
            candidate["target_security_bits"],
            bad_lazer_params,
        )
        mismatched_lazer_path = tmpdir / "mismatched-lazer.json"
        write_report(mismatched_lazer_path, mismatched_lazer)
        expect_checker_failure(mismatched_lazer_path, "parameter_set.fs_rounds must equal")

    print(json.dumps({"gate": "confidential-parameter-readiness-regressions", "status": "passed"}))


if __name__ == "__main__":
    main()
