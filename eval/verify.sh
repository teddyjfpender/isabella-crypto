#!/usr/bin/env bash
#
# verify.sh - Verification harness for Isabelle HOL projects
#
# Runs three verification steps:
#   1. check  - Syntax check (isabelle build -n)
#   2. build  - Full build (isabelle build)
#   3. export - Export Haskell code (isabelle build -e)
#
# Usage:
#   ./verify.sh --work-dir <dir> --session <name> [options]
#
# Options:
#   --work-dir <dir>      Working directory with Isabelle project (required)
#   --session <name>      Isabelle session name (default: CryptoProofs)
#   --results-dir <dir>   Directory to write verify.json (default: work-dir)
#   --steps <steps>       Comma-separated list of steps to run (default: check,build,export)
#   --timeout <seconds>   Timeout for each step (default: 300)
#   --verbose             Enable verbose output
#   --no-color            Disable colored output
#
set -euo pipefail

# Script directory
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

# Default values
WORK_DIR=""
SESSION_NAME="CryptoProofs"
RESULTS_DIR=""
STEPS="check,build,export"
TIMEOUT=300
VERBOSE=false
NO_COLOR=false

# Colors for output
setup_colors() {
    if [[ "$NO_COLOR" == "false" ]] && [[ -t 1 ]]; then
        RED='\033[0;31m'
        GREEN='\033[0;32m'
        YELLOW='\033[1;33m'
        BLUE='\033[0;34m'
        NC='\033[0m'
    else
        RED=''
        GREEN=''
        YELLOW=''
        BLUE=''
        NC=''
    fi
}

log_info() {
    echo -e "${BLUE}[INFO]${NC} $1"
}

log_success() {
    echo -e "${GREEN}[PASS]${NC} $1"
}

log_warn() {
    echo -e "${YELLOW}[WARN]${NC} $1"
}

log_error() {
    echo -e "${RED}[FAIL]${NC} $1" >&2
}

log_verbose() {
    if [[ "$VERBOSE" == "true" ]]; then
        echo -e "${BLUE}[DEBUG]${NC} $1"
    fi
}

usage() {
    cat <<EOF
Usage: $(basename "$0") --work-dir <dir> [options]

Options:
  --work-dir <dir>      Working directory with Isabelle project (required)
  --session <name>      Isabelle session name (default: CryptoProofs)
  --results-dir <dir>   Directory to write verify.json (default: work-dir)
  --steps <steps>       Comma-separated list of steps (default: check,build,export)
  --timeout <seconds>   Timeout for each step in seconds (default: 300)
  --verbose             Enable verbose output
  --no-color            Disable colored output
  -h, --help            Show this help message

Steps:
  check   - Syntax check using 'isabelle build -n -d . Session'
  build   - Full build using 'isabelle build -d . Session'
  export  - Export Haskell code using 'isabelle build -e -d . Session'

Example:
  $(basename "$0") --work-dir ./work/run_001 --session CryptoProofs
  $(basename "$0") --work-dir ./work/run_001 --steps check,build --verbose
EOF
    exit 1
}

# Parse command line arguments
while [[ $# -gt 0 ]]; do
    case $1 in
        --work-dir)
            WORK_DIR="$2"
            shift 2
            ;;
        --session)
            SESSION_NAME="$2"
            shift 2
            ;;
        --results-dir)
            RESULTS_DIR="$2"
            shift 2
            ;;
        --steps)
            STEPS="$2"
            shift 2
            ;;
        --timeout)
            TIMEOUT="$2"
            shift 2
            ;;
        --verbose)
            VERBOSE=true
            shift
            ;;
        --no-color)
            NO_COLOR=true
            shift
            ;;
        -h|--help)
            usage
            ;;
        *)
            log_error "Unknown option: $1"
            usage
            ;;
    esac
done

setup_colors

# Validate required arguments
if [[ -z "$WORK_DIR" ]]; then
    log_error "Missing required argument: --work-dir"
    usage
fi

if [[ ! -d "$WORK_DIR" ]]; then
    log_error "Work directory not found: $WORK_DIR"
    exit 1
fi

# Default results dir to work dir
if [[ -z "$RESULTS_DIR" ]]; then
    RESULTS_DIR="$WORK_DIR"
fi

mkdir -p "$RESULTS_DIR"

# Check for Isabelle
if ! command -v isabelle &> /dev/null; then
    log_error "Isabelle not found in PATH. Please install Isabelle and add it to your PATH."
    exit 1
fi

log_info "Starting verification for session: ${SESSION_NAME}"
log_verbose "Work directory: ${WORK_DIR}"
log_verbose "Results directory: ${RESULTS_DIR}"
log_verbose "Steps to run: ${STEPS}"

# Initialize results
VERIFY_JSON="${RESULTS_DIR}/verify.json"
OVERALL_STATUS="pass"
TIMESTAMP=$(date -u +%Y-%m-%dT%H:%M:%SZ)

# Create temporary directory for step outputs
TEMP_DIR=$(mktemp -d)
trap "rm -rf $TEMP_DIR" EXIT

# Function to run a verification step
run_step() {
    local step_name="$1"
    local step_cmd="$2"
    local step_output="${TEMP_DIR}/${step_name}.out"
    local step_err="${TEMP_DIR}/${step_name}.err"

    log_info "Running step: ${step_name}"
    log_verbose "Command: ${step_cmd}"

    local start_time=$(date +%s)
    local exit_code=0

    # Run with timeout
    set +e
    if command -v timeout &> /dev/null; then
        timeout "${TIMEOUT}s" bash -c "cd '$WORK_DIR' && $step_cmd" \
            >"$step_output" 2>"$step_err"
        exit_code=$?
        if [[ $exit_code -eq 124 ]]; then
            echo "TIMEOUT: Command exceeded ${TIMEOUT}s" >> "$step_err"
        fi
    elif command -v gtimeout &> /dev/null; then
        # macOS with GNU coreutils
        gtimeout "${TIMEOUT}s" bash -c "cd '$WORK_DIR' && $step_cmd" \
            >"$step_output" 2>"$step_err"
        exit_code=$?
        if [[ $exit_code -eq 124 ]]; then
            echo "TIMEOUT: Command exceeded ${TIMEOUT}s" >> "$step_err"
        fi
    else
        # No timeout command available
        bash -c "cd '$WORK_DIR' && $step_cmd" \
            >"$step_output" 2>"$step_err"
        exit_code=$?
    fi
    set -e

    local end_time=$(date +%s)
    local duration=$((end_time - start_time))

    # Determine status
    local status="pass"
    if [[ $exit_code -ne 0 ]]; then
        status="fail"
        OVERALL_STATUS="fail"
    fi

    # Log result
    if [[ "$status" == "pass" ]]; then
        log_success "${step_name} completed (${duration}s)"
    else
        log_error "${step_name} failed (exit code: ${exit_code}, ${duration}s)"
        if [[ "$VERBOSE" == "true" ]] && [[ -s "$step_err" ]]; then
            echo "--- Error output ---"
            cat "$step_err"
            echo "--- End error output ---"
        fi
    fi

    # Return JSON fragment for this step
    local stdout_content=$(cat "$step_output" 2>/dev/null | head -c 10000 | jq -Rs . 2>/dev/null || echo '""')
    local stderr_content=$(cat "$step_err" 2>/dev/null | head -c 10000 | jq -Rs . 2>/dev/null || echo '""')

    echo "{
      \"name\": \"${step_name}\",
      \"command\": $(echo "$step_cmd" | jq -Rs .),
      \"status\": \"${status}\",
      \"exit_code\": ${exit_code},
      \"duration_seconds\": ${duration},
      \"stdout\": ${stdout_content},
      \"stderr\": ${stderr_content}
    }"

    return $exit_code
}

# Initialize steps array
STEPS_JSON="["
FIRST_STEP=true

# Parse and run steps
IFS=',' read -ra STEP_ARRAY <<< "$STEPS"
for step in "${STEP_ARRAY[@]}"; do
    step=$(echo "$step" | xargs)  # trim whitespace

    case "$step" in
        check)
            CMD="isabelle build -n -d . ${SESSION_NAME}"
            ;;
        build)
            CMD="isabelle build -d . ${SESSION_NAME}"
            ;;
        export)
            CMD="isabelle build -e -d . ${SESSION_NAME}"
            ;;
        *)
            log_warn "Unknown step: ${step}, skipping"
            continue
            ;;
    esac

    # Add comma separator for JSON array
    if [[ "$FIRST_STEP" == "false" ]]; then
        STEPS_JSON+=","
    fi
    FIRST_STEP=false

    # Run step and capture JSON
    set +e
    STEP_RESULT=$(run_step "$step" "$CMD")
    set -e

    STEPS_JSON+="$STEP_RESULT"
done

STEPS_JSON+="]"

# Find theory files
THEORY_FILES=$(find "$WORK_DIR" -name "*.thy" -type f 2>/dev/null | head -20 | jq -R . | jq -s . || echo "[]")

# Write verify.json
cat > "$VERIFY_JSON" <<EOF
{
  "timestamp": "${TIMESTAMP}",
  "session_name": "${SESSION_NAME}",
  "work_dir": "${WORK_DIR}",
  "overall_status": "${OVERALL_STATUS}",
  "isabelle_version": "$(isabelle version 2>/dev/null || echo 'unknown')",
  "theory_files": ${THEORY_FILES},
  "steps": ${STEPS_JSON}
}
EOF

log_info "Verification results written to: ${VERIFY_JSON}"

# Exit with appropriate code
if [[ "$OVERALL_STATUS" == "pass" ]]; then
    log_success "All verification steps passed"
    exit 0
else
    log_error "One or more verification steps failed"
    exit 1
fi
