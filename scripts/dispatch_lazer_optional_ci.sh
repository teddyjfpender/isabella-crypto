#!/usr/bin/env bash
set -euo pipefail

# Dispatch the optional LaZer CI job and report whether a suitable runner picks it up.
#
# Usage:
#   ./scripts/dispatch_lazer_optional_ci.sh [ref]
#
# Env overrides:
#   OWNER_REPO=teddyjfpender/isabella-crypto
#   TIMEOUT_SECONDS=300
#   POLL_SECONDS=10

OWNER_REPO="${OWNER_REPO:-teddyjfpender/isabella-crypto}"
TIMEOUT_SECONDS="${TIMEOUT_SECONDS:-300}"
POLL_SECONDS="${POLL_SECONDS:-10}"
REF="${1:-$(git rev-parse --abbrev-ref HEAD)}"

require_cmd() {
  command -v "$1" >/dev/null 2>&1 || {
    echo "missing required command: $1" >&2
    exit 1
  }
}

require_cmd gh

if ! git rev-parse --verify "$REF" >/dev/null 2>&1; then
  echo "unknown git ref: $REF" >&2
  exit 1
fi

HEAD_SHA="$(git rev-parse --verify "$REF")"

echo "Dispatching CI workflow on ref '$REF' (sha: $HEAD_SHA)..."
gh api "repos/$OWNER_REPO/actions/workflows/ci.yml/dispatches" \
  -X POST \
  -f ref="$REF" \
  -f "inputs[run_lazer_optional]=true" >/dev/null

deadline=$((SECONDS + TIMEOUT_SECONDS))
run_id=""
while [[ -z "$run_id" && $SECONDS -lt $deadline ]]; do
  run_id="$(gh run list \
    --workflow ci.yml \
    --branch "$REF" \
    --event workflow_dispatch \
    --limit 20 \
    --json databaseId,headSha \
    --jq ".[] | select(.headSha == \"$HEAD_SHA\") | .databaseId" | head -n1 || true)"
  if [[ -z "$run_id" ]]; then
    sleep "$POLL_SECONDS"
  fi
done

if [[ -z "$run_id" ]]; then
  echo "could not locate dispatched workflow run for sha $HEAD_SHA within timeout" >&2
  exit 1
fi

echo "Dispatched run id: $run_id"

job_id=""
while [[ -z "$job_id" && $SECONDS -lt $deadline ]]; do
  job_id="$(gh run view "$run_id" --json jobs \
    --jq '.jobs[] | select(.name == "LaZer Equivalence (Optional)") | .databaseId' | head -n1 || true)"
  if [[ -z "$job_id" ]]; then
    sleep "$POLL_SECONDS"
  fi
done

if [[ -z "$job_id" ]]; then
  echo "LaZer optional job was not created in run $run_id" >&2
  exit 1
fi

echo "LaZer optional job id: $job_id"

while [[ $SECONDS -lt $deadline ]]; do
  status="$(gh api "repos/$OWNER_REPO/actions/jobs/$job_id" --jq '.status')"
  conclusion="$(gh api "repos/$OWNER_REPO/actions/jobs/$job_id" --jq '.conclusion // ""')"
  runner_name="$(gh api "repos/$OWNER_REPO/actions/jobs/$job_id" --jq '.runner_name // ""')"
  labels="$(gh api "repos/$OWNER_REPO/actions/jobs/$job_id" --jq '.labels | join(",")')"

  echo "status=$status conclusion=${conclusion:-<none>} runner=${runner_name:-<unassigned>} labels=$labels"

  if [[ "$status" == "completed" ]]; then
    if [[ "$conclusion" == "success" ]]; then
      echo "LaZer optional job completed successfully."
      exit 0
    fi
    echo "LaZer optional job completed with conclusion: $conclusion" >&2
    exit 1
  fi

  if [[ -n "$runner_name" ]]; then
    echo "LaZer optional job is running on runner '$runner_name'."
    sleep "$POLL_SECONDS"
    continue
  fi

  sleep "$POLL_SECONDS"
done

echo "timeout waiting for LaZer optional job to be assigned/completed." >&2
echo "runner is still unassigned; ensure a self-hosted runner with labels [self-hosted, linux, x64] is online." >&2
exit 2
