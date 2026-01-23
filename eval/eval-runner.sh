#!/usr/bin/env bash
#
# eval-runner.sh - Batch runner for Isabelle HOL evaluations
#
# Runs evaluations across all prompt files or work directories,
# collecting results for analysis.
#
# Usage:
#   ./eval-runner.sh [options]
#
# Modes:
#   --prompts-dir <dir>   Run all prompts in directory (default mode)
#   --work-dirs           Re-verify all existing work directories
#   --failed-only         Re-run only failed evaluations
#
# Options:
#   --prompts-dir <dir>   Directory containing prompt files (default: ./prompts)
#   --skills-dir <dir>    Directory containing skill files (default: ../skills)
#   --schema <file>       JSON schema file for all runs
#   --model <model>       Claude model to use
#   --parallel <n>        Number of parallel runs (default: 1)
#   --results-dir <dir>   Directory for results (default: ./results)
#   --work-base <dir>     Base directory for work dirs (default: ./work)
#   --filter <pattern>    Only run prompts matching pattern
#   --dry-run             Show what would be done without executing
#   --verbose             Enable verbose output
#   --continue-on-error   Continue running after failures
#
set -euo pipefail

# Script directory
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

# Default values
MODE="prompts"
PROMPTS_DIR="${SCRIPT_DIR}/prompts"
SKILLS_DIR="${SCRIPT_DIR}/../skills"
SCHEMA_FILE=""
MODEL=""
PARALLEL=1
RESULTS_DIR="${SCRIPT_DIR}/results"
WORK_BASE="${SCRIPT_DIR}/work"
FILTER=""
DRY_RUN=false
VERBOSE=false
CONTINUE_ON_ERROR=false
FAILED_ONLY=false

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
CYAN='\033[0;36m'
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
    echo -e "${RED}[ERROR]${NC} $1" >&2
}

log_header() {
    echo -e "${CYAN}=========================================${NC}"
    echo -e "${CYAN}$1${NC}"
    echo -e "${CYAN}=========================================${NC}"
}

usage() {
    cat <<EOF
Usage: $(basename "$0") [options]

Modes:
  --prompts-dir <dir>   Run all prompts in directory (default mode)
  --work-dirs           Re-verify all existing work directories
  --failed-only         Re-run only failed evaluations

Options:
  --prompts-dir <dir>   Directory containing prompt files (default: ./prompts)
  --skills-dir <dir>    Directory containing skill files (default: ../skills)
  --schema <file>       JSON schema file for all runs
  --model <model>       Claude model to use
  --parallel <n>        Number of parallel runs (default: 1)
  --results-dir <dir>   Directory for results (default: ./results)
  --work-base <dir>     Base directory for work dirs (default: ./work)
  --filter <pattern>    Only run prompts matching pattern (glob)
  --dry-run             Show what would be done without executing
  --verbose             Enable verbose output
  --continue-on-error   Continue running after failures
  -h, --help            Show this help message

Examples:
  $(basename "$0") --prompts-dir ./prompts --model claude-sonnet-4-20250514
  $(basename "$0") --filter "lattice*" --verbose
  $(basename "$0") --work-dirs --failed-only
  $(basename "$0") --parallel 4 --continue-on-error
EOF
    exit 1
}

# Parse command line arguments
while [[ $# -gt 0 ]]; do
    case $1 in
        --prompts-dir)
            PROMPTS_DIR="$2"
            shift 2
            ;;
        --work-dirs)
            MODE="work-dirs"
            shift
            ;;
        --failed-only)
            FAILED_ONLY=true
            shift
            ;;
        --skills-dir)
            SKILLS_DIR="$2"
            shift 2
            ;;
        --schema)
            SCHEMA_FILE="$2"
            shift 2
            ;;
        --model)
            MODEL="$2"
            shift 2
            ;;
        --parallel)
            PARALLEL="$2"
            shift 2
            ;;
        --results-dir)
            RESULTS_DIR="$2"
            shift 2
            ;;
        --work-base)
            WORK_BASE="$2"
            shift 2
            ;;
        --filter)
            FILTER="$2"
            shift 2
            ;;
        --dry-run)
            DRY_RUN=true
            shift
            ;;
        --verbose)
            VERBOSE=true
            shift
            ;;
        --continue-on-error)
            CONTINUE_ON_ERROR=true
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

# Summary file
SUMMARY_FILE="${RESULTS_DIR}/batch_summary.json"

# Counters
TOTAL=0
PASSED=0
FAILED=0
SKIPPED=0

# Results array for summary
declare -a RUN_RESULTS=()

# Function to run a single prompt
run_prompt() {
    local prompt_file="$1"
    local prompt_name=$(basename "$prompt_file" .md)

    log_info "Running evaluation: ${prompt_name}"

    # Build arguments for run-prompt.sh
    local args=("--prompt" "$prompt_file")

    # Add skill file if exists
    local skill_file="${SKILLS_DIR}/isabelle.md"
    if [[ -f "$skill_file" ]]; then
        args+=("--skill" "$skill_file")
    fi

    # Add optional arguments
    [[ -n "$SCHEMA_FILE" ]] && args+=("--schema" "$SCHEMA_FILE")
    [[ -n "$MODEL" ]] && args+=("--model" "$MODEL")
    [[ "$VERBOSE" == "true" ]] && args+=("--verbose")

    args+=("--results-dir" "$RESULTS_DIR")

    if [[ "$DRY_RUN" == "true" ]]; then
        log_info "[DRY-RUN] Would run: ${SCRIPT_DIR}/run-prompt.sh ${args[*]}"
        return 0
    fi

    # Run and capture result
    set +e
    "${SCRIPT_DIR}/run-prompt.sh" "${args[@]}"
    local exit_code=$?
    set -e

    return $exit_code
}

# Function to verify existing work directory
verify_work_dir() {
    local work_dir="$1"
    local dir_name=$(basename "$work_dir")

    log_info "Verifying work directory: ${dir_name}"

    # Check for verify.json to determine previous status
    local verify_json="${work_dir}/verify.json"
    if [[ "$FAILED_ONLY" == "true" ]]; then
        if [[ -f "$verify_json" ]]; then
            local prev_status=$(jq -r '.overall_status' "$verify_json" 2>/dev/null || echo "unknown")
            if [[ "$prev_status" == "pass" ]]; then
                log_info "Skipping ${dir_name} (previously passed)"
                ((SKIPPED++))
                return 0
            fi
        fi
    fi

    # Determine session name from ROOT file
    local session_name="CryptoProofs"
    local root_file="${work_dir}/ROOT"
    if [[ -f "$root_file" ]]; then
        session_name=$(grep -oP 'session\s+"\K[^"]+' "$root_file" 2>/dev/null | head -1 || echo "CryptoProofs")
    fi

    if [[ "$DRY_RUN" == "true" ]]; then
        log_info "[DRY-RUN] Would verify: ${work_dir} (session: ${session_name})"
        return 0
    fi

    # Run verification
    set +e
    "${SCRIPT_DIR}/verify.sh" \
        --work-dir "$work_dir" \
        --session "$session_name" \
        ${VERBOSE:+--verbose}
    local exit_code=$?
    set -e

    return $exit_code
}

# Main execution
log_header "Isabelle Evaluation Batch Runner"

mkdir -p "$RESULTS_DIR"

START_TIME=$(date +%s)

if [[ "$MODE" == "prompts" ]]; then
    # Run all prompts
    log_info "Mode: Run prompts from ${PROMPTS_DIR}"

    if [[ ! -d "$PROMPTS_DIR" ]]; then
        log_error "Prompts directory not found: ${PROMPTS_DIR}"
        exit 1
    fi

    # Find prompt files
    if [[ -n "$FILTER" ]]; then
        PROMPT_FILES=($(find "$PROMPTS_DIR" -name "${FILTER}.md" -o -name "${FILTER}" 2>/dev/null | sort))
    else
        PROMPT_FILES=($(find "$PROMPTS_DIR" -name "*.md" 2>/dev/null | sort))
    fi

    if [[ ${#PROMPT_FILES[@]} -eq 0 ]]; then
        log_warn "No prompt files found"
        exit 0
    fi

    log_info "Found ${#PROMPT_FILES[@]} prompt files"

    for prompt_file in "${PROMPT_FILES[@]}"; do
        ((TOTAL++))
        prompt_name=$(basename "$prompt_file" .md)

        if run_prompt "$prompt_file"; then
            ((PASSED++))
            RUN_RESULTS+=("{\"name\": \"${prompt_name}\", \"status\": \"pass\"}")
            log_success "${prompt_name}: PASSED"
        else
            ((FAILED++))
            RUN_RESULTS+=("{\"name\": \"${prompt_name}\", \"status\": \"fail\"}")
            log_error "${prompt_name}: FAILED"

            if [[ "$CONTINUE_ON_ERROR" == "false" ]] && [[ "$DRY_RUN" == "false" ]]; then
                log_error "Stopping due to failure (use --continue-on-error to continue)"
                break
            fi
        fi
    done

elif [[ "$MODE" == "work-dirs" ]]; then
    # Re-verify existing work directories
    log_info "Mode: Re-verify work directories in ${WORK_BASE}"

    if [[ ! -d "$WORK_BASE" ]]; then
        log_error "Work base directory not found: ${WORK_BASE}"
        exit 1
    fi

    # Find work directories (those with ROOT files)
    WORK_DIRS=($(find "$WORK_BASE" -name "ROOT" -exec dirname {} \; 2>/dev/null | sort))

    if [[ ${#WORK_DIRS[@]} -eq 0 ]]; then
        log_warn "No work directories found"
        exit 0
    fi

    log_info "Found ${#WORK_DIRS[@]} work directories"

    for work_dir in "${WORK_DIRS[@]}"; do
        ((TOTAL++))
        dir_name=$(basename "$work_dir")

        if verify_work_dir "$work_dir"; then
            ((PASSED++))
            RUN_RESULTS+=("{\"name\": \"${dir_name}\", \"status\": \"pass\"}")
        else
            ((FAILED++))
            RUN_RESULTS+=("{\"name\": \"${dir_name}\", \"status\": \"fail\"}")

            if [[ "$CONTINUE_ON_ERROR" == "false" ]] && [[ "$DRY_RUN" == "false" ]]; then
                log_error "Stopping due to failure (use --continue-on-error to continue)"
                break
            fi
        fi
    done
fi

END_TIME=$(date +%s)
DURATION=$((END_TIME - START_TIME))

# Generate summary
log_header "Evaluation Summary"

log_info "Total:   ${TOTAL}"
log_success "Passed:  ${PASSED}"
log_error "Failed:  ${FAILED}"
[[ $SKIPPED -gt 0 ]] && log_warn "Skipped: ${SKIPPED}"
log_info "Duration: ${DURATION}s"

# Calculate pass rate
if [[ $TOTAL -gt 0 ]]; then
    PASS_RATE=$(echo "scale=1; ${PASSED} * 100 / ${TOTAL}" | bc)
    log_info "Pass rate: ${PASS_RATE}%"
else
    PASS_RATE=0
fi

# Write summary JSON
if [[ "$DRY_RUN" == "false" ]]; then
    RESULTS_JSON=$(IFS=,; echo "[${RUN_RESULTS[*]:-}]")
    cat > "$SUMMARY_FILE" <<EOF
{
  "timestamp": "$(date -u +%Y-%m-%dT%H:%M:%SZ)",
  "mode": "${MODE}",
  "total": ${TOTAL},
  "passed": ${PASSED},
  "failed": ${FAILED},
  "skipped": ${SKIPPED},
  "pass_rate": ${PASS_RATE},
  "duration_seconds": ${DURATION},
  "options": {
    "prompts_dir": "${PROMPTS_DIR}",
    "results_dir": "${RESULTS_DIR}",
    "model": "${MODEL:-default}",
    "filter": "${FILTER:-none}",
    "continue_on_error": ${CONTINUE_ON_ERROR},
    "failed_only": ${FAILED_ONLY}
  },
  "results": ${RESULTS_JSON}
}
EOF
    log_info "Summary written to: ${SUMMARY_FILE}"
fi

# Exit with appropriate code
if [[ $FAILED -gt 0 ]]; then
    exit 1
else
    exit 0
fi
