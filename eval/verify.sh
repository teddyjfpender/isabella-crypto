#!/usr/bin/env bash
#
# verify.sh - Verification harness for Isabella (Isabelle + Lattice) projects
#
# Runs verification steps on an Isabelle project and records results.
#
# Usage:
#   ./verify.sh <project_dir> <out_dir> [session_name]
#
# Arguments:
#   project_dir   Directory containing the Isabelle project (ROOT file)
#   out_dir       Directory to write verification results
#   session_name  Optional session name (default: auto-detect from ROOT)
#
# Output Files:
#   steps.jsonl   JSONL file with individual step results
#   verify.json   Summary of verification results
#   check.out/err Syntax check stdout/stderr
#   build.out/err Full build stdout/stderr
#   export.out/err Export stdout/stderr
#
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

# Colors
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
CYAN='\033[0;36m'
MAGENTA='\033[0;35m'
BOLD='\033[1m'
DIM='\033[2m'
NC='\033[0m'

log_ts() {
    echo -e "${DIM}[$(date '+%H:%M:%S')]${NC} $1"
}

log_info() {
    echo -e "${DIM}[$(date '+%H:%M:%S')]${NC} ${BLUE}[VERIFY]${NC} $1"
}

log_step() {
    echo -e "${DIM}[$(date '+%H:%M:%S')]${NC} ${MAGENTA}[STEP]${NC} ${BOLD}$1${NC}"
}

log_success() {
    echo -e "${DIM}[$(date '+%H:%M:%S')]${NC} ${GREEN}[PASS]${NC} $1"
}

log_fail() {
    echo -e "${DIM}[$(date '+%H:%M:%S')]${NC} ${RED}[FAIL]${NC} $1"
}

log_skip() {
    echo -e "${DIM}[$(date '+%H:%M:%S')]${NC} ${YELLOW}[SKIP]${NC} $1"
}

log_isabelle() {
    echo -e "${DIM}[$(date '+%H:%M:%S')]${NC} ${CYAN}[ISABELLE]${NC} $1"
}

# Validate arguments
if [[ $# -lt 2 ]]; then
    echo "Usage: $(basename "$0") <project_dir> <out_dir> [session_name]"
    echo ""
    echo "Arguments:"
    echo "  project_dir   Directory containing the Isabelle project (ROOT file)"
    echo "  out_dir       Directory to write verification results"
    echo "  session_name  Optional session name (default: auto-detect from ROOT)"
    exit 2
fi

PROJECT_DIR="$1"
OUT_DIR="$2"
SESSION_NAME="${3:-}"

# Validate project directory
if [[ ! -d "$PROJECT_DIR" ]]; then
    echo "Error: Project directory not found: $PROJECT_DIR" >&2
    exit 2
fi

# Create output directory
mkdir -p "$OUT_DIR"

# Initialize steps file
STEPS_FILE="${OUT_DIR}/steps.jsonl"
> "$STEPS_FILE"

# Record timestamps
STARTED_AT="$(date -u +%Y-%m-%dT%H:%M:%SZ)"

log_info "Starting verification"
log_info "Project: ${PROJECT_DIR}"
log_info "Output: ${OUT_DIR}"

# Check for ROOT file
if [[ ! -f "${PROJECT_DIR}/ROOT" ]]; then
    log_fail "ROOT file not found in ${PROJECT_DIR}"

    # Record the failure
    if [[ -x "${SCRIPT_DIR}/record_step.py" ]]; then
        python3 "${SCRIPT_DIR}/record_step.py" "$STEPS_FILE" "precheck" "check ROOT file" "fail" "1" "0" "" "" "ROOT file not found"
    else
        echo '{"step":"precheck","cmd":"check ROOT file","status":"fail","exit_code":1,"duration_sec":0,"message":"ROOT file not found"}' >> "$STEPS_FILE"
    fi

    ENDED_AT="$(date -u +%Y-%m-%dT%H:%M:%SZ)"
    if [[ -x "${SCRIPT_DIR}/steps_to_verify.py" ]]; then
        python3 "${SCRIPT_DIR}/steps_to_verify.py" "$STEPS_FILE" "${OUT_DIR}/verify.json" "$STARTED_AT" "$ENDED_AT" "$PROJECT_DIR"
    fi
    exit 1
fi

# Auto-detect session name from ROOT file if not provided
if [[ -z "$SESSION_NAME" ]]; then
    SESSION_NAME=$(grep -oP 'session\s+"\K[^"]+' "${PROJECT_DIR}/ROOT" 2>/dev/null | head -1 || true)
    if [[ -z "$SESSION_NAME" ]]; then
        SESSION_NAME=$(grep -oP "session\s+\K\w+" "${PROJECT_DIR}/ROOT" 2>/dev/null | head -1 || true)
    fi
    if [[ -z "$SESSION_NAME" ]]; then
        # Try alternative pattern
        SESSION_NAME=$(grep -E "^session" "${PROJECT_DIR}/ROOT" | head -1 | sed -E 's/session\s+"?([^"= ]+)"?.*/\1/' || true)
    fi
    if [[ -z "$SESSION_NAME" ]]; then
        log_fail "Could not detect session name from ROOT file"
        exit 1
    fi
fi

log_info "Session: ${SESSION_NAME}"

# Check if isabelle is available
if ! command -v isabelle &> /dev/null; then
    log_fail "Isabelle not found in PATH"
    log_info "Install with: brew install --cask isabelle"
    log_info "Or add to PATH: export PATH=\"/Applications/Isabelle2024.app/bin:\$PATH\""

    if [[ -x "${SCRIPT_DIR}/record_step.py" ]]; then
        python3 "${SCRIPT_DIR}/record_step.py" "$STEPS_FILE" "precheck" "check isabelle" "fail" "127" "0" "" "" "isabelle not found in PATH"
    else
        echo '{"step":"precheck","cmd":"check isabelle","status":"fail","exit_code":127,"duration_sec":0,"message":"isabelle not found in PATH"}' >> "$STEPS_FILE"
    fi

    ENDED_AT="$(date -u +%Y-%m-%dT%H:%M:%SZ)"
    if [[ -x "${SCRIPT_DIR}/steps_to_verify.py" ]]; then
        python3 "${SCRIPT_DIR}/steps_to_verify.py" "$STEPS_FILE" "${OUT_DIR}/verify.json" "$STARTED_AT" "$ENDED_AT" "$PROJECT_DIR"
    fi
    exit 127
fi

ISABELLE_VERSION=$(isabelle version 2>/dev/null || echo "unknown")
log_info "Isabelle version: ${ISABELLE_VERSION}"

# ============================================================================
# Helper function to run a verification step
# ============================================================================
run_step() {
    local step_name="$1"
    local cmd="$2"
    local description="$3"
    local skip_on_missing="${4:-false}"

    local stdout_file="${OUT_DIR}/${step_name}.out"
    local stderr_file="${OUT_DIR}/${step_name}.err"

    log_step "${description}..."
    log_isabelle "Running: ${cmd}"

    # Check if command exists
    local step_start=$(date +%s)

    set +e
    eval "$cmd" > "$stdout_file" 2> "$stderr_file"
    local exit_code=$?
    set -e

    local step_end=$(date +%s)
    local duration=$((step_end - step_start))

    local status="pass"
    local message=""

    if [[ $exit_code -eq 0 ]]; then
        status="pass"
        log_success "${description} (${duration}s)"
    elif [[ $exit_code -eq 127 ]] && [[ "$skip_on_missing" == "true" ]]; then
        status="skipped"
        message="Command not found"
        log_skip "${description} - command not found"
    else
        status="fail"
        message="Exit code: ${exit_code}"
        log_fail "${description} (${duration}s, exit=${exit_code})"

        # Show last few lines of stderr
        if [[ -s "$stderr_file" ]]; then
            echo -e "${DIM}────────────────────────────────────────${NC}"
            tail -15 "$stderr_file" | while IFS= read -r line; do
                echo -e "  ${RED}${line}${NC}"
            done
            echo -e "${DIM}────────────────────────────────────────${NC}"
        fi
    fi

    # Record the step
    if [[ -x "${SCRIPT_DIR}/record_step.py" ]]; then
        python3 "${SCRIPT_DIR}/record_step.py" \
            "$STEPS_FILE" \
            "$step_name" \
            "$cmd" \
            "$status" \
            "$exit_code" \
            "$duration" \
            "$stdout_file" \
            "$stderr_file" \
            "$message"
    else
        # Fallback: write JSON directly
        local json_cmd
        json_cmd=$(printf '%s' "$cmd" | python3 -c "import sys,json; print(json.dumps(sys.stdin.read()))" 2>/dev/null || echo "\"$cmd\"")
        local json_msg
        json_msg=$(printf '%s' "$message" | python3 -c "import sys,json; print(json.dumps(sys.stdin.read()))" 2>/dev/null || echo "\"$message\"")

        echo "{\"step\":\"${step_name}\",\"cmd\":${json_cmd},\"status\":\"${status}\",\"exit_code\":${exit_code},\"duration_sec\":${duration},\"stdout_path\":\"${stdout_file}\",\"stderr_path\":\"${stderr_file}\",\"message\":${json_msg}}" >> "$STEPS_FILE"
    fi

    return $exit_code
}

# ============================================================================
# Run verification steps
# ============================================================================

OVERALL_EXIT=0

# Step 1: Syntax check (isabelle build -n)
log_isabelle "Step 1/3: Syntax check"
if ! run_step "check" "isabelle build -n -d '${PROJECT_DIR}' '${SESSION_NAME}'" "Syntax check"; then
    OVERALL_EXIT=1
fi

# Step 2: Full build (isabelle build)
log_isabelle "Step 2/3: Full build"
if ! run_step "build" "isabelle build -v -d '${PROJECT_DIR}' '${SESSION_NAME}'" "Full build"; then
    OVERALL_EXIT=1
fi

# Step 3: Export Haskell code (isabelle build -e)
# Check if build succeeded by looking for success indicators
BUILD_SUCCESS=false
if [[ -f "${OUT_DIR}/build.out" ]]; then
    if grep -qE "(Finished|Building|Loaded)" "${OUT_DIR}/build.out" 2>/dev/null; then
        BUILD_SUCCESS=true
    fi
fi

if [[ "$BUILD_SUCCESS" == "true" ]] || [[ $OVERALL_EXIT -eq 0 ]]; then
    log_isabelle "Step 3/3: Haskell export"
    if ! run_step "export" "isabelle build -e -d '${PROJECT_DIR}' '${SESSION_NAME}'" "Haskell export"; then
        # Export failure is noted but doesn't fail overall if build passed
        log_info "Export step had issues but build succeeded"
    fi
else
    log_skip "Haskell export - build did not complete successfully"

    if [[ -x "${SCRIPT_DIR}/record_step.py" ]]; then
        python3 "${SCRIPT_DIR}/record_step.py" \
            "$STEPS_FILE" \
            "export" \
            "isabelle build -e -d '${PROJECT_DIR}' '${SESSION_NAME}'" \
            "skipped" \
            "0" \
            "0" \
            "" \
            "" \
            "Skipped due to build failure"
    else
        echo '{"step":"export","cmd":"isabelle build -e","status":"skipped","exit_code":0,"duration_sec":0,"message":"Skipped due to build failure"}' >> "$STEPS_FILE"
    fi
fi

# ============================================================================
# Generate summary
# ============================================================================

ENDED_AT="$(date -u +%Y-%m-%dT%H:%M:%SZ)"

log_info "Generating verification summary..."

if [[ -x "${SCRIPT_DIR}/steps_to_verify.py" ]]; then
    python3 "${SCRIPT_DIR}/steps_to_verify.py" \
        "$STEPS_FILE" \
        "${OUT_DIR}/verify.json" \
        "$STARTED_AT" \
        "$ENDED_AT" \
        "$PROJECT_DIR"
else
    # Fallback: create minimal verify.json
    pass_count=0
    fail_count=0
    skip_count=0
    failed_steps=""

    while IFS= read -r line; do
        status=$(echo "$line" | python3 -c "import sys,json; print(json.loads(sys.stdin.read()).get('status',''))" 2>/dev/null || echo "")
        step=$(echo "$line" | python3 -c "import sys,json; print(json.loads(sys.stdin.read()).get('step',''))" 2>/dev/null || echo "")
        case "$status" in
            pass) ((pass_count++)) || true ;;
            fail)
                ((fail_count++)) || true
                failed_steps+="\"${step}\","
                ;;
            skipped) ((skip_count++)) || true ;;
        esac
    done < "$STEPS_FILE"

    overall="pass"
    [[ $fail_count -gt 0 ]] && overall="fail"

    # Remove trailing comma from failed_steps
    failed_steps="${failed_steps%,}"

    cat > "${OUT_DIR}/verify.json" <<EOF
{
  "version": 1,
  "status": "${overall}",
  "started_at": "${STARTED_AT}",
  "ended_at": "${ENDED_AT}",
  "project_dir": "${PROJECT_DIR}",
  "session_name": "${SESSION_NAME}",
  "isabelle_version": "${ISABELLE_VERSION}",
  "counts": {
    "pass": ${pass_count},
    "fail": ${fail_count},
    "skipped": ${skip_count}
  },
  "failed_steps": [${failed_steps}]
}
EOF
fi

# Print summary
echo ""
log_info "═══════════════════════════════════════════════════════════"

VERIFY_STATUS=$(python3 -c "import sys,json; print(json.load(open('${OUT_DIR}/verify.json')).get('status','unknown'))" 2>/dev/null || echo "unknown")
PASS_COUNT=$(python3 -c "import sys,json; print(json.load(open('${OUT_DIR}/verify.json')).get('counts',{}).get('pass',0))" 2>/dev/null || echo "0")
FAIL_COUNT=$(python3 -c "import sys,json; print(json.load(open('${OUT_DIR}/verify.json')).get('counts',{}).get('fail',0))" 2>/dev/null || echo "0")
SKIP_COUNT=$(python3 -c "import sys,json; print(json.load(open('${OUT_DIR}/verify.json')).get('counts',{}).get('skipped',0))" 2>/dev/null || echo "0")

if [[ "$VERIFY_STATUS" == "pass" ]]; then
    echo -e "${DIM}[$(date '+%H:%M:%S')]${NC} ${GREEN}${BOLD}[RESULT]${NC} ${GREEN}✓ PASS${NC} (${PASS_COUNT} passed, ${FAIL_COUNT} failed, ${SKIP_COUNT} skipped)"
else
    echo -e "${DIM}[$(date '+%H:%M:%S')]${NC} ${RED}${BOLD}[RESULT]${NC} ${RED}✗ FAIL${NC} (${PASS_COUNT} passed, ${FAIL_COUNT} failed, ${SKIP_COUNT} skipped)"

    # List failed steps
    FAILED_STEPS=$(python3 -c "import sys,json; print(', '.join(json.load(open('${OUT_DIR}/verify.json')).get('failed_steps',[])))" 2>/dev/null || true)
    if [[ -n "$FAILED_STEPS" ]]; then
        echo -e "${DIM}[$(date '+%H:%M:%S')]${NC} ${RED}[FAILED]${NC} Steps: ${FAILED_STEPS}"
    fi
fi

log_info "═══════════════════════════════════════════════════════════"
log_info "Results written to: ${OUT_DIR}/verify.json"

# Exit with appropriate code
if [[ "$VERIFY_STATUS" == "pass" ]]; then
    exit 0
else
    exit 1
fi
