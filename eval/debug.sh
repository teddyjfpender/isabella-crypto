#!/usr/bin/env bash
#
# debug.sh - Debugging workflow for failed Isabelle evaluations
#
# Analyzes verify.json from failed runs, shows error output, and provides
# suggestions for common Isabelle errors.
#
# Usage:
#   ./debug.sh <run-dir>          Show errors from a specific run
#   ./debug.sh --latest           Debug the most recent failed run
#   ./debug.sh --list-failed      List all failed runs
#
# Options:
#   <run-dir>             Path to the run directory (work or results)
#   --latest              Debug the most recent failed run
#   --list-failed         List all failed runs
#   --step <name>         Show details for specific step (check, build, export)
#   --re-run <step>       Re-run a specific verification step
#   --re-run-all          Re-run all verification steps
#   --show-theory         Display the theory file content
#   --suggest             Show suggestions for the errors
#   --verbose             Enable verbose output
#
set -euo pipefail

# Script directory
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

# Default values
RUN_DIR=""
SHOW_LATEST=false
LIST_FAILED=false
STEP_NAME=""
RE_RUN_STEP=""
RE_RUN_ALL=false
SHOW_THEORY=false
SUGGEST=false
VERBOSE=false

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
CYAN='\033[0;36m'
MAGENTA='\033[0;35m'
NC='\033[0m'

log_info() {
    echo -e "${BLUE}[INFO]${NC} $1"
}

log_success() {
    echo -e "${GREEN}[OK]${NC} $1"
}

log_warn() {
    echo -e "${YELLOW}[WARN]${NC} $1"
}

log_error() {
    echo -e "${RED}[ERROR]${NC} $1"
}

log_header() {
    echo -e "${CYAN}=========================================${NC}"
    echo -e "${CYAN}$1${NC}"
    echo -e "${CYAN}=========================================${NC}"
}

log_suggestion() {
    echo -e "${MAGENTA}[SUGGESTION]${NC} $1"
}

usage() {
    cat <<EOF
Usage: $(basename "$0") <run-dir> [options]

Arguments:
  <run-dir>             Path to the run directory (work or results)

Options:
  --latest              Debug the most recent failed run
  --list-failed         List all failed runs
  --step <name>         Show details for specific step (check, build, export)
  --re-run <step>       Re-run a specific verification step
  --re-run-all          Re-run all verification steps
  --show-theory         Display the theory file content
  --suggest             Show suggestions for the errors (default: on)
  --verbose             Enable verbose output
  -h, --help            Show this help message

Examples:
  $(basename "$0") ./results/20240115_120000_lattice
  $(basename "$0") --latest
  $(basename "$0") --latest --re-run check
  $(basename "$0") ./work/run_001 --step build --suggest
EOF
    exit 1
}

# Parse command line arguments
while [[ $# -gt 0 ]]; do
    case $1 in
        --latest)
            SHOW_LATEST=true
            shift
            ;;
        --list-failed)
            LIST_FAILED=true
            shift
            ;;
        --step)
            STEP_NAME="$2"
            shift 2
            ;;
        --re-run)
            RE_RUN_STEP="$2"
            shift 2
            ;;
        --re-run-all)
            RE_RUN_ALL=true
            shift
            ;;
        --show-theory)
            SHOW_THEORY=true
            shift
            ;;
        --suggest)
            SUGGEST=true
            shift
            ;;
        --verbose)
            VERBOSE=true
            shift
            ;;
        -h|--help)
            usage
            ;;
        -*)
            log_error "Unknown option: $1"
            usage
            ;;
        *)
            RUN_DIR="$1"
            shift
            ;;
    esac
done

# Enable suggestions by default
SUGGEST=true

# Function to find failed runs
find_failed_runs() {
    local search_dir="$1"
    local failed_runs=()

    while IFS= read -r verify_json; do
        if [[ -f "$verify_json" ]]; then
            local status=$(jq -r '.overall_status' "$verify_json" 2>/dev/null || echo "unknown")
            if [[ "$status" == "fail" ]]; then
                failed_runs+=("$(dirname "$verify_json")")
            fi
        fi
    done < <(find "$search_dir" -name "verify.json" 2>/dev/null | sort -r)

    printf '%s\n' "${failed_runs[@]}"
}

# Function to find most recent failed run
find_latest_failed() {
    local results_dir="${SCRIPT_DIR}/results"
    local work_dir="${SCRIPT_DIR}/work"

    # Search both directories
    local latest=""
    local latest_time=0

    for dir in "$results_dir" "$work_dir"; do
        if [[ -d "$dir" ]]; then
            while IFS= read -r verify_json; do
                if [[ -f "$verify_json" ]]; then
                    local status=$(jq -r '.overall_status' "$verify_json" 2>/dev/null || echo "unknown")
                    if [[ "$status" == "fail" ]]; then
                        local mtime=$(stat -f %m "$verify_json" 2>/dev/null || stat -c %Y "$verify_json" 2>/dev/null || echo "0")
                        if [[ $mtime -gt $latest_time ]]; then
                            latest_time=$mtime
                            latest=$(dirname "$verify_json")
                        fi
                    fi
                fi
            done < <(find "$dir" -name "verify.json" 2>/dev/null)
        fi
    done

    echo "$latest"
}

# Function to analyze and suggest fixes for common errors
analyze_error() {
    local error_text="$1"

    echo ""
    log_header "Error Analysis"

    # Check for common Isabelle errors and provide suggestions

    # Syntax errors
    if echo "$error_text" | grep -qi "inner syntax error"; then
        log_error "Inner syntax error detected"
        log_suggestion "Check for typos in terms, types, or expressions"
        log_suggestion "Ensure proper escaping of special characters"
        log_suggestion "Verify parentheses are balanced"
    fi

    if echo "$error_text" | grep -qi "outer syntax error"; then
        log_error "Outer syntax error detected"
        log_suggestion "Check command structure (theory, lemma, definition, etc.)"
        log_suggestion "Ensure 'begin' and 'end' are properly matched"
        log_suggestion "Verify keyword spelling"
    fi

    # Type errors
    if echo "$error_text" | grep -qi "type error\|type unification failed"; then
        log_error "Type error detected"
        log_suggestion "Check that function arguments have correct types"
        log_suggestion "Use 'term' command to inspect types: term \"your_expression\""
        log_suggestion "Add explicit type annotations where needed"
    fi

    if echo "$error_text" | grep -qi "No type arity"; then
        log_error "Type class instance error"
        log_suggestion "The type may need an instance declaration"
        log_suggestion "Check if required type class is imported"
    fi

    # Undefined constants
    if echo "$error_text" | grep -qi "Undefined constant\|Unknown constant"; then
        log_error "Undefined constant referenced"
        log_suggestion "Check if the constant is defined before use"
        log_suggestion "Verify imports include the theory defining this constant"
        log_suggestion "Check for typos in constant names"
    fi

    # Theory loading issues
    if echo "$error_text" | grep -qi "Bad theory import\|Could not find theory"; then
        log_error "Theory import error"
        log_suggestion "Verify the imported theory exists and is accessible"
        log_suggestion "Check the session's ROOT file includes required sessions"
        log_suggestion "Ensure theory file names match their declared names"
    fi

    # Proof failures
    if echo "$error_text" | grep -qi "Failed to finish proof\|Failed to apply"; then
        log_error "Proof method failed"
        log_suggestion "Try breaking down the proof into smaller steps"
        log_suggestion "Use 'sledgehammer' to find applicable lemmas"
        log_suggestion "Check if additional lemmas or assumptions are needed"
    fi

    if echo "$error_text" | grep -qi "Tactic failed\|empty result sequence"; then
        log_error "Tactic failure"
        log_suggestion "The proof method doesn't apply to the current goal"
        log_suggestion "Inspect the goal state with 'print_state'"
        log_suggestion "Try alternative tactics: auto, simp, blast, metis"
    fi

    # Termination issues
    if echo "$error_text" | grep -qi "Could not prove termination"; then
        log_error "Termination proof failed"
        log_suggestion "Add explicit termination proof or measure function"
        log_suggestion "Use 'function' instead of 'fun' for complex recursion"
        log_suggestion "Check that recursive calls are on structurally smaller arguments"
    fi

    # Code generation issues
    if echo "$error_text" | grep -qi "No code equations\|Cannot generate code"; then
        log_error "Code generation error"
        log_suggestion "Ensure all functions have executable code equations"
        log_suggestion "Use 'code_datatype' for abstract types"
        log_suggestion "Check for axioms that prevent code generation"
    fi

    # Session/ROOT issues
    if echo "$error_text" | grep -qi "Unknown session\|Bad session"; then
        log_error "Session configuration error"
        log_suggestion "Check ROOT file syntax"
        log_suggestion "Verify parent session exists"
        log_suggestion "Run 'isabelle sessions -d .' to list available sessions"
    fi

    # Missing files
    if echo "$error_text" | grep -qi "No such file\|File not found"; then
        log_error "Missing file"
        log_suggestion "Check that all files referenced in ROOT exist"
        log_suggestion "Verify file permissions"
    fi

    # Timeout
    if echo "$error_text" | grep -qi "TIMEOUT"; then
        log_error "Verification timed out"
        log_suggestion "The proof may be too complex or non-terminating"
        log_suggestion "Try simplifying the theory"
        log_suggestion "Increase timeout with --timeout option in verify.sh"
    fi

    echo ""
}

# Function to show step details
show_step_details() {
    local verify_json="$1"
    local step_name="$2"

    if [[ -z "$step_name" ]]; then
        # Show all steps
        local steps=$(jq -r '.steps[] | .name' "$verify_json" 2>/dev/null)
        for step in $steps; do
            show_single_step "$verify_json" "$step"
        done
    else
        show_single_step "$verify_json" "$step_name"
    fi
}

show_single_step() {
    local verify_json="$1"
    local step_name="$2"

    local step_data=$(jq -r ".steps[] | select(.name == \"$step_name\")" "$verify_json" 2>/dev/null)

    if [[ -z "$step_data" ]]; then
        log_error "Step not found: $step_name"
        return 1
    fi

    local status=$(echo "$step_data" | jq -r '.status')
    local exit_code=$(echo "$step_data" | jq -r '.exit_code')
    local duration=$(echo "$step_data" | jq -r '.duration_seconds')
    local command=$(echo "$step_data" | jq -r '.command')
    local stdout=$(echo "$step_data" | jq -r '.stdout')
    local stderr=$(echo "$step_data" | jq -r '.stderr')

    echo ""
    log_header "Step: ${step_name}"

    if [[ "$status" == "pass" ]]; then
        log_success "Status: PASSED"
    else
        log_error "Status: FAILED"
    fi

    echo "Exit code: ${exit_code}"
    echo "Duration: ${duration}s"
    echo "Command: ${command}"

    if [[ -n "$stdout" ]] && [[ "$stdout" != "null" ]] && [[ "$stdout" != "" ]]; then
        echo ""
        echo "--- stdout ---"
        echo "$stdout"
    fi

    if [[ -n "$stderr" ]] && [[ "$stderr" != "null" ]] && [[ "$stderr" != "" ]]; then
        echo ""
        echo "--- stderr ---"
        echo "$stderr"

        if [[ "$SUGGEST" == "true" ]] && [[ "$status" == "fail" ]]; then
            analyze_error "$stderr"
        fi
    fi
}

# List failed runs mode
if [[ "$LIST_FAILED" == "true" ]]; then
    log_header "Failed Runs"

    results_dir="${SCRIPT_DIR}/results"
    work_dir="${SCRIPT_DIR}/work"

    found_any=false

    for dir in "$results_dir" "$work_dir"; do
        if [[ -d "$dir" ]]; then
            echo ""
            log_info "In $(basename "$dir")/"

            while IFS= read -r failed_dir; do
                if [[ -n "$failed_dir" ]]; then
                    found_any=true
                    local verify_json="${failed_dir}/verify.json"
                    local timestamp=$(jq -r '.timestamp' "$verify_json" 2>/dev/null || echo "unknown")
                    local session=$(jq -r '.session_name' "$verify_json" 2>/dev/null || echo "unknown")
                    echo "  - $(basename "$failed_dir") (${session}, ${timestamp})"
                fi
            done < <(find_failed_runs "$dir")
        fi
    done

    if [[ "$found_any" == "false" ]]; then
        log_success "No failed runs found"
    fi

    exit 0
fi

# Find latest failed if requested
if [[ "$SHOW_LATEST" == "true" ]]; then
    RUN_DIR=$(find_latest_failed)
    if [[ -z "$RUN_DIR" ]]; then
        log_error "No failed runs found"
        exit 1
    fi
    log_info "Debugging latest failed run: ${RUN_DIR}"
fi

# Validate run directory
if [[ -z "$RUN_DIR" ]]; then
    log_error "No run directory specified"
    usage
fi

if [[ ! -d "$RUN_DIR" ]]; then
    log_error "Run directory not found: ${RUN_DIR}"
    exit 1
fi

# Find verify.json
VERIFY_JSON="${RUN_DIR}/verify.json"
if [[ ! -f "$VERIFY_JSON" ]]; then
    log_error "verify.json not found in: ${RUN_DIR}"
    log_info "Run verification first: ./verify.sh --work-dir ${RUN_DIR}"
    exit 1
fi

# Load verification results
log_header "Debug: $(basename "$RUN_DIR")"

OVERALL_STATUS=$(jq -r '.overall_status' "$VERIFY_JSON")
SESSION_NAME=$(jq -r '.session_name' "$VERIFY_JSON")
TIMESTAMP=$(jq -r '.timestamp' "$VERIFY_JSON")
ISABELLE_VERSION=$(jq -r '.isabelle_version' "$VERIFY_JSON")

echo "Session: ${SESSION_NAME}"
echo "Timestamp: ${TIMESTAMP}"
echo "Isabelle: ${ISABELLE_VERSION}"

if [[ "$OVERALL_STATUS" == "pass" ]]; then
    log_success "Overall Status: PASSED"
else
    log_error "Overall Status: FAILED"
fi

# Show theory file if requested
if [[ "$SHOW_THEORY" == "true" ]]; then
    echo ""
    log_header "Theory Files"

    theory_files=$(jq -r '.theory_files[]' "$VERIFY_JSON" 2>/dev/null || true)
    for thy_file in $theory_files; do
        if [[ -f "$thy_file" ]]; then
            echo ""
            echo "--- ${thy_file} ---"
            cat "$thy_file"
            echo "--- end ---"
        fi
    done
fi

# Show step details
show_step_details "$VERIFY_JSON" "$STEP_NAME"

# Re-run verification if requested
if [[ -n "$RE_RUN_STEP" ]] || [[ "$RE_RUN_ALL" == "true" ]]; then
    echo ""
    log_header "Re-running Verification"

    VERIFY_ARGS=("--work-dir" "$RUN_DIR" "--session" "$SESSION_NAME")

    if [[ -n "$RE_RUN_STEP" ]]; then
        VERIFY_ARGS+=("--steps" "$RE_RUN_STEP")
    fi

    [[ "$VERBOSE" == "true" ]] && VERIFY_ARGS+=("--verbose")

    log_info "Running: verify.sh ${VERIFY_ARGS[*]}"

    "${SCRIPT_DIR}/verify.sh" "${VERIFY_ARGS[@]}"
fi

exit 0
