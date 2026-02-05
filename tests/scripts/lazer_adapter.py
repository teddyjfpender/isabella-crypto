#!/usr/bin/env python3
"""
Deterministic LaZer fixture generator for cross-library comparison tests.

This script is intentionally side-effect free: it only emits JSON.
If LaZer is unavailable (not built / not importable), it emits
{"available": false, "error": "..."} and exits 0 so tests can skip safely.
"""

from __future__ import annotations

import hashlib
import json
import os
import sys
from typing import Any, Dict, List, Tuple


def _load_lazer() -> Tuple[bool, str]:
    """
    Resolve and import the LaZer python module.

    Search order:
    1) LAZER_PYTHON (exact python/ dir containing lazer.py + _lazer_cffi*)
    2) LAZER_ROOT/python
    """
    lazer_python = os.environ.get("LAZER_PYTHON")
    lazer_root = os.environ.get("LAZER_ROOT")

    candidate_paths: List[str] = []
    if lazer_python:
        candidate_paths.append(lazer_python)
    if lazer_root:
        candidate_paths.append(os.path.join(lazer_root, "python"))

    for p in candidate_paths:
        if p and p not in sys.path:
            sys.path.insert(0, p)

    try:
        # noqa: F401 - imported symbols are used by fixture generation below.
        from lazer import _redc, poly_t, polymat_t, polyring_t, polyvec_t  # type: ignore
        return True, ""
    except Exception as exc:  # pragma: no cover - runtime environment specific
        return False, str(exc)


def _shake_seed(label: str) -> bytes:
    return hashlib.shake_128(label.encode("utf-8")).digest(32)


def _poly_centered_list(poly: Any) -> List[int]:
    p = poly.copy()
    p.redc()
    return [int(x) for x in p.to_list()]


def _polyvec_centered_list(vec: Any) -> List[List[int]]:
    out: List[List[int]] = []
    for i in range(vec.dim):
        out.append(_poly_centered_list(vec.get_elem(i)))
    return out


def _sparse_ternary(n: int, tau: int, label: str) -> List[int]:
    if tau < 0 or tau > n:
        raise ValueError(f"invalid tau={tau} for n={n}")

    coeffs = [0] * n
    stream = hashlib.shake_128(label.encode("utf-8")).digest(8192)
    i = 0
    placed = 0

    while placed < tau:
        if i + 3 > len(stream):
            stream += hashlib.shake_128(f"{label}:{i}".encode("utf-8")).digest(1024)

        pos = int.from_bytes(stream[i:i + 2], "little") % n
        i += 2
        if coeffs[pos] != 0:
            continue

        sign = 1 if (stream[i] & 1) == 0 else -1
        i += 1
        coeffs[pos] = sign
        placed += 1

    return coeffs


def _polymat_centered_list(mat: Any) -> List[List[List[int]]]:
    out: List[List[List[int]]] = []
    for r in range(mat.rows):
        row: List[List[int]] = []
        for c in range(mat.cols):
            row.append(_poly_centered_list(mat.get_elem(r, c)))
        out.append(row)
    return out


def _build_fixture() -> Dict[str, Any]:
    from lazer import _redc, poly_t, polymat_t, polyring_t, polyvec_t  # type: ignore

    q = 3329
    n = 64
    rows = 2
    cols = 3
    tau = 16

    seed_a = _shake_seed("isabella-lazer-fixture-A")
    seed_x = _shake_seed("isabella-lazer-fixture-X")

    ring = polyring_t(n, q)
    mat = polymat_t.urandom_static(ring, rows, cols, q, seed_a, 0)
    vec = polyvec_t.brandom_static(ring, cols, 2, seed_x, 0)
    mat_vec = mat * vec
    mat_vec.redc()

    # Single multiplication probe used for focused regression checks.
    a0 = mat.get_elem(0, 0)
    x0 = vec.get_elem(0)
    prod = a0 * x0
    prod.redc()

    # Deterministic sparse ternary challenge for module scaling checks.
    challenge_coeffs = _sparse_ternary(n, tau, "isabella-lazer-fixture-challenge")
    challenge = poly_t(ring, challenge_coeffs)
    challenge.redc()

    scaled_vec = vec * challenge
    scaled_vec.redc()
    mat_vec_scaled_right = mat * scaled_vec
    mat_vec_scaled_right.redc()

    mat_vec_scaled_left = mat_vec * challenge
    mat_vec_scaled_left.redc()

    centered_inputs = [-5000, -3329, -1665, -1, 0, 1, 1664, 1665, 3328, 3329, 5000]
    centered_outputs = [_redc(v, q) for v in centered_inputs]

    return {
        "available": True,
        "schema_version": 1,
        "ring": {"q": q, "n": n},
        "dims": {"rows": rows, "cols": cols},
        "seeds": {
            "A_hex": seed_a.hex(),
            "x_hex": seed_x.hex(),
        },
        "matrix": _polymat_centered_list(mat),
        "vector": _polyvec_centered_list(vec),
        "mat_vec_result": _polyvec_centered_list(mat_vec),
        "ring_case": {
            "a": _poly_centered_list(a0),
            "b": _poly_centered_list(x0),
            "ab": _poly_centered_list(prod),
        },
        "challenge_case": {
            "tau": tau,
            "challenge": _poly_centered_list(challenge),
            "scaled_vector": _polyvec_centered_list(scaled_vec),
            "mat_vec_scaled_right": _polyvec_centered_list(mat_vec_scaled_right),
            "mat_vec_scaled_left": _polyvec_centered_list(mat_vec_scaled_left),
        },
        "centered_samples": {
            "inputs": centered_inputs,
            "outputs": centered_outputs,
        },
    }


def main() -> None:
    ok, err = _load_lazer()
    if not ok:
        print(json.dumps({"available": False, "error": err}))
        return

    fixture = _build_fixture()
    print(json.dumps(fixture))


if __name__ == "__main__":
    main()
