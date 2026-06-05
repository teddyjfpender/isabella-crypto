#!/usr/bin/env python3
"""Screen confidential-transfer parameter candidates.

This is a deterministic repository-local sanity pass, not a replacement for
Albrecht-style lattice-estimator analysis. It records the concrete MVP
dimensions the formalization is targeting and flags whether an external
estimator module is available in the local Python environment.
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any


@dataclass(frozen=True)
class Candidate:
    name: str
    architecture: str
    n1: int
    n2: int
    m: int
    q: int
    beta: int
    gamma: int
    range_bits: int
    fs_rounds: int
    notes: str


def log2(x: float) -> float:
    return math.log(x, 2)


def screen(candidate: Candidate) -> dict[str, Any]:
    total_dim = candidate.n1 + candidate.n2
    syndrome_bits = candidate.m * log2(candidate.q)
    opening_bits = total_dim * log2(2 * candidate.beta + 1)
    response_bits = candidate.n2 * log2(2 * (candidate.gamma + 4 * candidate.beta) + 1)
    return {
        **asdict(candidate),
        "total_opening_dimension": total_dim,
        "syndrome_capacity_bits": round(syndrome_bits, 2),
        "short_opening_volume_bits": round(opening_bits, 2),
        "capacity_minus_opening_bits": round(syndrome_bits - opening_bits, 2),
        "balance_response_volume_bits": round(response_bits, 2),
        "fiat_shamir_soundness_bits": candidate.fs_rounds,
        "screening_status": "screen_only",
    }


def external_estimator_available() -> bool:
    try:
        __import__("estimator")
    except Exception:
        return False
    return True


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--out", default="bench/data/confidential-parameter-screen.json")
    args = parser.parse_args()

    candidates = [
        Candidate(
            name="ct_sis_note_mvp_v0",
            architecture="SIS note commitment MVP",
            n1=1,
            n2=1024,
            m=1024,
            q=8_380_417,
            beta=2**16,
            gamma=2**24,
            range_bits=64,
            fs_rounds=128,
            notes=(
                "Formal MVP target for note commitments/nullifiers/range proofs; "
                "requires external lattice-estimator validation before production."
            ),
        ),
        Candidate(
            name="rlwe_ahe_transfer_research_v0",
            architecture="Separate RLWE/AHE EncryptValid/SamePlaintext/TransferValid layer",
            n1=1,
            n2=2048,
            m=2048,
            q=8_380_417,
            beta=2**16,
            gamma=2**24,
            range_bits=64,
            fs_rounds=128,
            notes=(
                "Research track from idea.md; kept separate from the SIS-note MVP "
                "until EncryptValid/SamePlaintext/TransferValid relations are formalized."
            ),
        ),
    ]

    output = {
        "tool": "confidential_parameter_screen",
        "external_lattice_estimator_available": external_estimator_available(),
        "warning": (
            "This JSON is a deterministic parameter screening artifact. It is not "
            "a production security estimate and does not replace lattice-estimator, "
            "LaZer parameter generation, or implementation benchmarks."
        ),
        "candidates": [screen(candidate) for candidate in candidates],
    }

    out = Path(args.out)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(output, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(output, indent=2))


if __name__ == "__main__":
    main()
