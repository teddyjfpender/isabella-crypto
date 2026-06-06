#!/usr/bin/env python3
"""Generate external lattice-estimator report collections.

The runner consumes the machine-readable estimator requests emitted by
confidential_parameter_screen.py. It records blocked requests as evidence and
only calls malb/lattice-estimator once the formal SIS precondition is true.
"""

from __future__ import annotations

import argparse
import json
import math
import re
import sys
from datetime import UTC, datetime
from pathlib import Path
from typing import Any


PARAMETER_FIELDS = ("n1", "n2", "m", "q", "beta", "gamma", "range_bits", "fs_rounds")
POWER_OF_TWO_RE = re.compile(r"2\^(-?\d+(?:\.\d+)?)")


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
    candidate_name = candidate.get("name", "<unknown>")
    for field in PARAMETER_FIELDS:
        value = candidate.get(field)
        if not isinstance(value, int) or isinstance(value, bool) or value <= 0:
            raise SystemExit(f"{candidate_name}.{field} must be a positive integer")
        snapshot[field] = value
    return snapshot


def jsonable(value: Any) -> Any:
    if value is None or isinstance(value, (str, int, float, bool)):
        return value
    if isinstance(value, dict):
        return {str(key): jsonable(item) for key, item in value.items()}
    if isinstance(value, (list, tuple)):
        return [jsonable(item) for item in value]
    items = getattr(value, "items", None)
    if callable(items):
        return {str(key): jsonable(item) for key, item in items()}
    return str(value)


def value_log2(value: Any) -> float | None:
    if value is None:
        return None
    log_method = getattr(value, "log", None)
    if callable(log_method):
        try:
            return float(log_method(2))
        except Exception:
            pass
    try:
        numeric = float(value)
    except Exception:
        numeric = None
    if numeric is not None and math.isfinite(numeric) and numeric > 0:
        return math.log2(numeric)
    match = POWER_OF_TWO_RE.search(str(value))
    if match:
        return float(match.group(1))
    return None


def cost_rop_bits(cost: Any) -> float | None:
    getter = getattr(cost, "get", None)
    if callable(getter):
        return value_log2(getter("rop"))
    if isinstance(cost, dict):
        return value_log2(cost.get("rop"))
    return None


def result_security_bits(result: Any) -> float | None:
    bits: list[float] = []
    items = result.items() if hasattr(result, "items") else []
    for _, cost in items:
        cost_bits = cost_rop_bits(cost)
        if cost_bits is not None and math.isfinite(cost_bits):
            bits.append(cost_bits)
    if not bits:
        return None
    return min(bits)


def call_path(root: Any, dotted: str) -> Any:
    current = root
    for part in dotted.split("."):
        current = getattr(current, part)
    return current


def run_estimator(request: dict[str, Any]) -> tuple[float, dict[str, Any]]:
    try:
        from estimator import SIS  # type: ignore
    except Exception as exc:  # noqa: BLE001 - report local estimator availability exactly.
        raise RuntimeError(f"could not import estimator.SIS: {type(exc).__name__}: {exc}") from exc
    try:
        from sage.all import oo  # type: ignore
    except Exception as exc:  # noqa: BLE001 - lattice-estimator uses Sage infinity for norm=oo.
        raise RuntimeError(f"could not import sage.all.oo: {type(exc).__name__}: {exc}") from exc

    mapping = request["parameter_mapping"]
    params = SIS.Parameters(
        n=mapping["n"],
        q=mapping["q"],
        length_bound=mapping["length_bound"],
        m=mapping["m"],
        norm=oo,
    )

    estimates: dict[str, Any] = {}
    security_bits: list[float] = []
    for call in request["estimator_api"]["estimate_calls"]:
        if not call.startswith("SIS."):
            raise RuntimeError(f"unsupported estimator call path: {call}")
        fn = call_path(SIS, call[len("SIS."):])
        result = fn(params, quiet=True)
        estimates[call] = jsonable(result)
        call_bits = result_security_bits(result)
        if call_bits is not None:
            security_bits.append(call_bits)

    if not security_bits:
        raise RuntimeError("estimator returned no finite rop values")
    return min(security_bits), estimates


def report_for_candidate(
    candidate: dict[str, Any],
    generated_at: str,
    command: list[str],
) -> dict[str, Any]:
    name = candidate.get("name")
    if not isinstance(name, str) or not name:
        raise SystemExit("candidate.name must be a non-empty string")
    request = candidate.get("external_lattice_estimator_request")
    if not isinstance(request, dict):
        raise SystemExit(f"{name}.external_lattice_estimator_request must be an object")

    base = {
        "candidate": name,
        "tool": "malb/lattice-estimator",
        "source": "scripts/run_confidential_lattice_estimator.py",
        "generated_at": generated_at,
        "command": command,
        "parameters": parameter_snapshot(candidate),
        "estimator_request": request,
    }

    if not request.get("applicable", False):
        return {
            **base,
            "status": "not_applicable",
            "reason": request.get("reason", "external SIS estimator request is not applicable"),
            "assumptions": [
                "No SIS estimate was run because this candidate has no formal SIS-margin request.",
            ],
        }

    request_status = request.get("status")
    if request_status != "ready_for_external_estimator":
        return {
            **base,
            "status": request_status,
            "reason": (
                "No lattice-estimator run was attempted because the formal SIS "
                "request precondition is not satisfied."
            ),
            "assumptions": [
                "No security estimate was run because 2 * length_bound < q - 1 is false.",
            ],
        }

    try:
        security_bits, estimates = run_estimator(request)
    except Exception as exc:  # noqa: BLE001 - the failed run is the evidence.
        return {
            **base,
            "status": "failed",
            "reason": str(exc),
            "assumptions": [
                "The formal SIS request precondition passed, but the estimator run failed locally.",
            ],
        }

    return {
        **base,
        "status": "estimated",
        "security_level_bits": round(security_bits, 2),
        "estimates": estimates,
        "assumptions": [
            "malb/lattice-estimator SIS model with norm=+Infinity.",
            "security_level_bits is the minimum log2(rop) across recorded estimator calls.",
            "The formal SIS request precondition 2 * length_bound < q - 1 passed before invocation.",
        ],
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--parameter-screen",
        default="bench/data/confidential-parameter-screen.json",
        help="parameter-screen JSON containing external_lattice_estimator_request entries",
    )
    parser.add_argument(
        "--out",
        default="bench/data/confidential-lattice-estimator-reports.json",
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
        "tool": "confidential_lattice_estimator_runner",
        "source": "scripts/run_confidential_lattice_estimator.py",
        "generated_at": generated_at,
        "parameter_screen": str(args.parameter_screen),
        "reports": reports,
    }

    out = Path(args.out)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(output, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(output, indent=2))


if __name__ == "__main__":
    main()
