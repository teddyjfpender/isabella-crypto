#!/usr/bin/env bash
#
# run-prompt.sh - Main orchestration script for Isabelle HOL evaluation
#
# Runs a single evaluation prompt through Claude and verifies the output
# using Isabelle's build system.
#
# Usage:
#   ./run-prompt.sh --prompt <prompt-file> [options]
#
# Options:
#   --prompt <file>       Path to the prompt file (required)
#   --skill <file>        Path to skill file to prepend to prompt
#   --disable-skills      Do not load any skill prefixes
#   --schema <file>       Path to JSON schema for structured output
#   --model <model>       Claude model to use (default: claude-sonnet-4-20250514)
#   --out-file <file>     Output file name (default: output.json)
#   --work-dir <dir>      Working directory for Isabelle project
#   --results-dir <dir>   Directory for results (default: ./results)
#   --no-verify           Skip verification step
#   --no-scaffold         Skip project scaffolding
#   --session <name>      Isabelle session name (default: CryptoProofs)
#   --verbose             Enable verbose output
#   --dry-run             Show what would be done without executing
#
set -euo pipefail

# Script directory
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"

# Default values
PROMPT_FILE=""
SKILL_FILE=""
DISABLE_SKILLS=false
SCHEMA_FILE=""
MODEL="claude-sonnet-4-20250514"
OUT_FILE="output.json"
WORK_DIR=""
RESULTS_DIR="${SCRIPT_DIR}/results"
NO_VERIFY=false
NO_SCAFFOLD=false
SESSION_NAME="CryptoProofs"
VERBOSE=false
DRY_RUN=false

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

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

log_verbose() {
    if [[ "$VERBOSE" == "true" ]]; then
        echo -e "${BLUE}[DEBUG]${NC} $1"
    fi
}

usage() {
    cat <<EOF
Usage: $(basename "$0") --prompt <prompt-file> [options]

Options:
  --prompt <file>       Path to the prompt file (required)
  --skill <file>        Path to skill file to prepend to prompt
  --disable-skills      Do not load any skill prefixes
  --schema <file>       Path to JSON schema for structured output
  --model <model>       Claude model to use (default: claude-sonnet-4-20250514)
  --out-file <file>     Output file name (default: output.json)
  --work-dir <dir>      Working directory for Isabelle project
  --results-dir <dir>   Directory for results (default: ./results)
  --no-verify           Skip verification step
  --no-scaffold         Skip project scaffolding
  --session <name>      Isabelle session name (default: CryptoProofs)
  --verbose             Enable verbose output
  --dry-run             Show what would be done without executing
  -h, --help            Show this help message

Example:
  $(basename "$0") --prompt prompts/lattice-crypto.md --skill skills/isabelle.md
EOF
    exit 1
}

# Parse command line arguments
while [[ $# -gt 0 ]]; do
    case $1 in
        --prompt)
            PROMPT_FILE="$2"
            shift 2
            ;;
        --skill)
            SKILL_FILE="$2"
            shift 2
            ;;
        --disable-skills)
            DISABLE_SKILLS=true
            shift
            ;;
        --schema)
            SCHEMA_FILE="$2"
            shift 2
            ;;
        --model)
            MODEL="$2"
            shift 2
            ;;
        --out-file)
            OUT_FILE="$2"
            shift 2
            ;;
        --work-dir)
            WORK_DIR="$2"
            shift 2
            ;;
        --results-dir)
            RESULTS_DIR="$2"
            shift 2
            ;;
        --no-verify)
            NO_VERIFY=true
            shift
            ;;
        --no-scaffold)
            NO_SCAFFOLD=true
            shift
            ;;
        --session)
            SESSION_NAME="$2"
            shift 2
            ;;
        --verbose)
            VERBOSE=true
            shift
            ;;
        --dry-run)
            DRY_RUN=true
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

# Validate required arguments
if [[ -z "$PROMPT_FILE" ]]; then
    log_error "Missing required argument: --prompt"
    usage
fi

if [[ ! -f "$PROMPT_FILE" ]]; then
    log_error "Prompt file not found: $PROMPT_FILE"
    exit 1
fi

# Generate run ID based on timestamp
RUN_ID="$(date +%Y%m%d_%H%M%S)_$(basename "$PROMPT_FILE" .md)"

# Set up work directory
if [[ -z "$WORK_DIR" ]]; then
    WORK_DIR="${SCRIPT_DIR}/work/${RUN_ID}"
fi

# Set up results directory
RUN_RESULTS_DIR="${RESULTS_DIR}/${RUN_ID}"

log_info "Starting evaluation run: ${RUN_ID}"
log_verbose "Prompt file: ${PROMPT_FILE}"
log_verbose "Work directory: ${WORK_DIR}"
log_verbose "Results directory: ${RUN_RESULTS_DIR}"

# Create directories
if [[ "$DRY_RUN" == "false" ]]; then
    mkdir -p "$WORK_DIR"
    mkdir -p "$RUN_RESULTS_DIR"
fi

# Scaffold Isabelle project if needed
if [[ "$NO_SCAFFOLD" == "false" ]]; then
    log_info "Scaffolding Isabelle project..."
    if [[ "$DRY_RUN" == "false" ]]; then
        "${SCRIPT_DIR}/scaffold.sh" \
            --work-dir "$WORK_DIR" \
            --session "$SESSION_NAME" \
            ${VERBOSE:+--verbose}
    else
        log_info "[DRY-RUN] Would run scaffold.sh"
    fi
fi

# Build the full prompt
log_info "Building prompt..."

FULL_PROMPT=""

# Add schema preamble if provided
if [[ -n "$SCHEMA_FILE" ]] && [[ -f "$SCHEMA_FILE" ]]; then
    log_verbose "Adding schema preamble from: ${SCHEMA_FILE}"
    SCHEMA_CONTENT=$(cat "$SCHEMA_FILE")
    FULL_PROMPT+="You must respond with valid JSON matching this schema:

\`\`\`json
${SCHEMA_CONTENT}
\`\`\`

"
fi

# Add skill prefix if provided and not disabled
if [[ "$DISABLE_SKILLS" == "false" ]] && [[ -n "$SKILL_FILE" ]]; then
    if [[ -f "$SKILL_FILE" ]]; then
        log_verbose "Adding skill prefix from: ${SKILL_FILE}"
        SKILL_CONTENT=$(cat "$SKILL_FILE")
        FULL_PROMPT+="${SKILL_CONTENT}

---

"
    else
        log_warn "Skill file not found: ${SKILL_FILE}"
    fi
fi

# Add main prompt
PROMPT_CONTENT=$(cat "$PROMPT_FILE")
FULL_PROMPT+="${PROMPT_CONTENT}"

# Save combined prompt
COMBINED_PROMPT_FILE="${RUN_RESULTS_DIR}/combined_prompt.md"
if [[ "$DRY_RUN" == "false" ]]; then
    echo "$FULL_PROMPT" > "$COMBINED_PROMPT_FILE"
    log_verbose "Combined prompt saved to: ${COMBINED_PROMPT_FILE}"
fi

# Run Claude
log_info "Running Claude (model: ${MODEL})..."

OUTPUT_FILE="${RUN_RESULTS_DIR}/${OUT_FILE}"
CLAUDE_LOG="${RUN_RESULTS_DIR}/claude.log"

if [[ "$DRY_RUN" == "false" ]]; then
    # Run claude with the prompt
    set +e
    if command -v claude &> /dev/null; then
        # Use claude CLI
        echo "$FULL_PROMPT" | claude \
            --model "$MODEL" \
            --output-format json \
            2>"$CLAUDE_LOG" > "$OUTPUT_FILE"
        CLAUDE_EXIT_CODE=$?
    else
        # Fallback: check for anthropic CLI or API
        log_error "Claude CLI not found. Please install claude CLI."
        CLAUDE_EXIT_CODE=1
    fi
    set -e

    if [[ $CLAUDE_EXIT_CODE -ne 0 ]]; then
        log_error "Claude execution failed (exit code: ${CLAUDE_EXIT_CODE})"
        log_error "See log: ${CLAUDE_LOG}"
    else
        log_success "Claude execution completed"
    fi
else
    log_info "[DRY-RUN] Would run Claude with combined prompt"
    CLAUDE_EXIT_CODE=0
fi

# Create run metadata
RUN_JSON="${RUN_RESULTS_DIR}/run.json"
if [[ "$DRY_RUN" == "false" ]]; then
    cat > "$RUN_JSON" <<EOF
{
  "run_id": "${RUN_ID}",
  "timestamp": "$(date -u +%Y-%m-%dT%H:%M:%SZ)",
  "prompt_file": "${PROMPT_FILE}",
  "skill_file": "${SKILL_FILE:-null}",
  "schema_file": "${SCHEMA_FILE:-null}",
  "model": "${MODEL}",
  "session_name": "${SESSION_NAME}",
  "work_dir": "${WORK_DIR}",
  "results_dir": "${RUN_RESULTS_DIR}",
  "claude_exit_code": ${CLAUDE_EXIT_CODE},
  "options": {
    "disable_skills": ${DISABLE_SKILLS},
    "no_verify": ${NO_VERIFY},
    "no_scaffold": ${NO_SCAFFOLD}
  }
}
EOF
    log_verbose "Run metadata saved to: ${RUN_JSON}"
fi

# Extract code from JSON output
if [[ "$DRY_RUN" == "false" ]] && [[ -f "$OUTPUT_FILE" ]]; then
    log_info "Extracting code from output..."

    # Try to extract Isabelle theory from JSON output
    if command -v jq &> /dev/null; then
        # Extract code field if present, otherwise look for theory content
        CODE_CONTENT=$(jq -r '.code // .theory // .content // empty' "$OUTPUT_FILE" 2>/dev/null || true)

        if [[ -n "$CODE_CONTENT" ]] && [[ "$CODE_CONTENT" != "null" ]]; then
            # Write to theory file in work directory
            THEORY_FILE="${WORK_DIR}/${SESSION_NAME}.thy"
            echo "$CODE_CONTENT" > "$THEORY_FILE"
            log_success "Theory code extracted to: ${THEORY_FILE}"
        else
            # Try to extract from markdown code blocks in raw output
            log_verbose "No structured code field found, checking for code blocks..."

            # Extract content between ```isabelle and ``` or ```theory and ```
            EXTRACTED=$(sed -n '/^```\(isabelle\|theory\)/,/^```$/p' "$OUTPUT_FILE" 2>/dev/null | sed '1d;$d' || true)

            if [[ -n "$EXTRACTED" ]]; then
                THEORY_FILE="${WORK_DIR}/${SESSION_NAME}.thy"
                echo "$EXTRACTED" > "$THEORY_FILE"
                log_success "Theory code extracted from code block to: ${THEORY_FILE}"
            else
                log_warn "Could not extract theory code from output"
            fi
        fi
    else
        log_warn "jq not installed, skipping code extraction"
    fi
fi

# Run verification
if [[ "$NO_VERIFY" == "false" ]]; then
    log_info "Running verification..."
    if [[ "$DRY_RUN" == "false" ]]; then
        "${SCRIPT_DIR}/verify.sh" \
            --work-dir "$WORK_DIR" \
            --session "$SESSION_NAME" \
            --results-dir "$RUN_RESULTS_DIR" \
            ${VERBOSE:+--verbose}
        VERIFY_EXIT_CODE=$?

        if [[ $VERIFY_EXIT_CODE -eq 0 ]]; then
            log_success "Verification passed"
        else
            log_error "Verification failed (exit code: ${VERIFY_EXIT_CODE})"
        fi
    else
        log_info "[DRY-RUN] Would run verify.sh"
    fi
else
    log_info "Skipping verification (--no-verify)"
fi

# Summary
log_info "========================================="
log_info "Run complete: ${RUN_ID}"
log_info "Results directory: ${RUN_RESULTS_DIR}"
log_info "========================================="

if [[ -f "${RUN_RESULTS_DIR}/verify.json" ]]; then
    log_info "Verification results:"
    cat "${RUN_RESULTS_DIR}/verify.json"
fi

exit 0
