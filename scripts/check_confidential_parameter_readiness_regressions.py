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


def estimator_report(
    candidate: dict,
    security_bits: int | None,
    parameters: dict,
    status: str | None = None,
) -> dict:
    request = candidate["external_lattice_estimator_request"]
    report = {
        "candidate": candidate["name"],
        "tool": "regression-estimator",
        "source": "scripts/check_confidential_parameter_readiness_regressions.py",
        "generated_at": "2026-06-06T00:00:00Z",
        "command": ["regression-estimator", candidate["name"]],
        "status": status or request["status"],
        "parameters": parameters,
        "estimator_request": request,
        "assumptions": ["regression fixture; not production estimator evidence"],
    }
    if report["status"] == "estimated":
        report["security_level_bits"] = security_bits
        report["estimates"] = {"SIS.estimate.rough": {"regression": {"rop_bits": security_bits}}}
    else:
        report["reason"] = "regression fixture preserves a non-estimated request status"
    return report


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
        estimator_ready_candidate = base_report["candidates"][1]
        estimator_ready_params = matching_parameters(estimator_ready_candidate)
        if estimator_ready_candidate["external_lattice_estimator_request"]["status"] != "ready_for_external_estimator":
            raise SystemExit("widened SIS candidate must be ready_for_external_estimator")
        if estimator_ready_candidate["formal_proof_margins"]["warnings"]:
            raise SystemExit("widened SIS candidate must pass formal proof-margin modulus checks")

        blocked_estimator = copy.deepcopy(base_report)
        blocked_estimator["candidates"][0]["external_lattice_estimator_report"] = estimator_report(
            candidate,
            None,
            params,
        )
        blocked_estimator_path = tmpdir / "blocked-estimator.json"
        write_report(blocked_estimator_path, blocked_estimator)
        blocked_proc = run(["python3", str(CHECKER), "--report", str(blocked_estimator_path)])
        if blocked_proc.returncode != 0:
            raise SystemExit(blocked_proc.stdout + blocked_proc.stderr)

        dishonest_estimated = copy.deepcopy(base_report)
        dishonest_estimated["candidates"][0]["external_lattice_estimator_report"] = estimator_report(
            candidate,
            candidate["target_security_bits"] - 1,
            params,
            status="estimated",
        )
        dishonest_estimated_path = tmpdir / "dishonest-estimated.json"
        write_report(dishonest_estimated_path, dishonest_estimated)
        expect_checker_failure(dishonest_estimated_path, "status must be blocked_by_formal_modulus")

        mismatched_estimator = copy.deepcopy(base_report)
        bad_params = dict(params)
        bad_params["q"] = bad_params["q"] + 1
        mismatched_estimator["candidates"][0]["external_lattice_estimator_report"] = estimator_report(
            candidate,
            None,
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

        mismatched_estimator_request = copy.deepcopy(base_report)
        request_mapping = mismatched_estimator_request["candidates"][0][
            "external_lattice_estimator_request"
        ]["parameter_mapping"]
        request_mapping["n"] = request_mapping["n"] + 1
        mismatched_request_path = tmpdir / "mismatched-estimator-request.json"
        write_report(mismatched_request_path, mismatched_estimator_request)
        expect_checker_failure(
            mismatched_request_path,
            "external_lattice_estimator_request.parameter_mapping.n must equal candidate.m",
        )

        mismatched_estimator_status = copy.deepcopy(base_report)
        mismatched_estimator_status["candidates"][0][
            "external_lattice_estimator_request"
        ]["status"] = "ready_for_external_estimator"
        mismatched_status_path = tmpdir / "mismatched-estimator-status.json"
        write_report(mismatched_status_path, mismatched_estimator_status)
        expect_checker_failure(
            mismatched_status_path,
            "external_lattice_estimator_request.status must be blocked_by_formal_modulus",
        )

        ready_failed_estimator = copy.deepcopy(base_report)
        ready_failed_estimator["candidates"][1]["external_lattice_estimator_report"] = estimator_report(
            estimator_ready_candidate,
            None,
            estimator_ready_params,
            status="failed",
        )
        ready_failed_path = tmpdir / "ready-failed-estimator.json"
        write_report(ready_failed_path, ready_failed_estimator)
        ready_failed_proc = run(["python3", str(CHECKER), "--report", str(ready_failed_path)])
        if ready_failed_proc.returncode != 0:
            raise SystemExit(ready_failed_proc.stdout + ready_failed_proc.stderr)

        ready_low_security_estimator = copy.deepcopy(base_report)
        ready_low_security_estimator["candidates"][1]["external_lattice_estimator_report"] = estimator_report(
            estimator_ready_candidate,
            estimator_ready_candidate["target_security_bits"] - 1,
            estimator_ready_params,
            status="estimated",
        )
        ready_low_security_path = tmpdir / "ready-low-security-estimator.json"
        write_report(ready_low_security_path, ready_low_security_estimator)
        expect_checker_failure(
            ready_low_security_path,
            "security_level_bits is below target_security_bits",
        )

        mismatched_ready_estimator_status = copy.deepcopy(base_report)
        mismatched_ready_estimator_status["candidates"][1][
            "external_lattice_estimator_request"
        ]["status"] = "blocked_by_formal_modulus"
        mismatched_ready_status_path = tmpdir / "mismatched-ready-estimator-status.json"
        write_report(mismatched_ready_status_path, mismatched_ready_estimator_status)
        expect_checker_failure(
            mismatched_ready_status_path,
            "external_lattice_estimator_request.status must be ready_for_external_estimator",
        )

    print(json.dumps({"gate": "confidential-parameter-readiness-regressions", "status": "passed"}))


if __name__ == "__main__":
    main()
