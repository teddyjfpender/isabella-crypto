#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT_DIR"

echo "[formalization] Checking Canon theories for unfinished proofs..."

if rg -n --glob '**/*.thy' '\b(sorry|oops|admit)\b' Canon; then
  echo "[formalization] Found unfinished proof placeholders in Canon theories."
  exit 1
fi

echo "[formalization] Canon proof placeholder check passed."
