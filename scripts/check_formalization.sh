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

BUILD_MODE="${CHECK_FORMALIZATION_BUILD:-auto}"
ISABELLE_BIN="${ISABELLE:-isabelle}"
CANON_DIR="${CANON_DIR:-Canon}"
CANON_SESSIONS="${CANON_SESSIONS:-Canon_Rings Canon_Crypto Canon_ZK}"
ISABELLE_BUILD_OPTS="${ISABELLE_BUILD_OPTS:--j1 -o threads=2 -o parallel_limit=2 -o parallel_proofs=0}"

case "$BUILD_MODE" in
  auto|required|skip)
    ;;
  *)
    echo "[formalization] CHECK_FORMALIZATION_BUILD must be auto, required, or skip; got: $BUILD_MODE"
    exit 1
    ;;
esac

if [[ "$BUILD_MODE" == "skip" ]]; then
  echo "[formalization] Isabelle session build skipped by CHECK_FORMALIZATION_BUILD=skip."
  exit 0
fi

if ! command -v "$ISABELLE_BIN" >/dev/null 2>&1; then
  if [[ "$BUILD_MODE" == "required" ]]; then
    echo "[formalization] Isabelle executable not found but session build is required: $ISABELLE_BIN"
    exit 1
  fi
  echo "[formalization] Isabelle executable not found; session build skipped in auto mode."
  exit 0
fi

read -r -a sessions <<< "$CANON_SESSIONS"
read -r -a build_opts <<< "$ISABELLE_BUILD_OPTS"

if [[ ${#sessions[@]} -eq 0 ]]; then
  echo "[formalization] CANON_SESSIONS must name at least one session."
  exit 1
fi

echo "[formalization] Building Canon sessions with Isabelle: ${sessions[*]}"
"$ISABELLE_BIN" build -d "$CANON_DIR" -b "${build_opts[@]}" "${sessions[@]}"
echo "[formalization] Canon Isabelle session build passed."
