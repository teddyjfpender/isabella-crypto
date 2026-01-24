#!/bin/bash
#
# isabella-loop.sh - Ralph Loop for Isabella (Isabelle + Lattice) proofs
#
# Iteratively generates Isabelle theories until they compile with valid proofs.
# Uses multi-model work/review cycle to achieve working formal proofs.
#
# Usage:
#   ./isabella-loop.sh --prompt <prompt-id> [options]
#
# Options:
#   --prompt <id>         Prompt ID (required)
#   --skill <name>        Skill to use (can be repeated)
#   --iterations <n>      Max iterations (default: 5)
#   --provider <name>     AI provider: openai, anthropic (default: openai)
#   --model <model>       Model for work phase (default: gpt-5.2-codex)
#   --review-provider     Provider for review/fix phase (default: openai)
#   --review-model        Model for review/fix phase (default: gpt-5.2-codex)
#   --session <name>      Isabelle session name (default: LatticeCrypto)
#   --output-dir <path>   Output directory (default: eval/work/<prompt-id>)
#   --theory-name <name>  Theory name (default: same as session)
#   --theory-path <path>  Subdirectory for theory (e.g., Linear for Canon/Linear/)
#   --root-dir <path>     Directory containing ROOT file (default: same as output-dir)
#   --verbose             Verbose output
#
# Example:
#   ./isabella-loop.sh --prompt isabelle-lwe-encryption-01 \
#       --skill isabelle-basics --skill isabelle-lattice-crypto \
#       --iterations 5
#

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"
EVAL_DIR="${PROJECT_ROOT}/eval"

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

# Defaults
PROMPT_ID=""
SKILLS=()
MAX_ITERATIONS=5
PROVIDER="openai"
MODEL="gpt-5.2-codex"
REVIEW_PROVIDER="openai"
REVIEW_MODEL="gpt-5.2-codex"
SESSION_NAME="LatticeCrypto"
OUTPUT_DIR=""
THEORY_NAME=""
THEORY_PATH=""
ROOT_DIR=""
VERBOSE=false

# Logging
log_ts() {
    echo -e "${DIM}[$(date '+%H:%M:%S')]${NC} $1"
}

log_info() {
    echo -e "${DIM}[$(date '+%H:%M:%S')]${NC} ${BLUE}[RALPH]${NC} $1"
}

log_iteration() {
    echo -e "${DIM}[$(date '+%H:%M:%S')]${NC} ${MAGENTA}[ITER]${NC} ${BOLD}$1${NC}"
}

log_success() {
    echo -e "${DIM}[$(date '+%H:%M:%S')]${NC} ${GREEN}[OK]${NC} $1"
}

log_warn() {
    echo -e "${DIM}[$(date '+%H:%M:%S')]${NC} ${YELLOW}[WARN]${NC} $1"
}

log_error() {
    echo -e "${DIM}[$(date '+%H:%M:%S')]${NC} ${RED}[ERROR]${NC} $1" >&2
}

log_phase() {
    echo -e "${DIM}[$(date '+%H:%M:%S')]${NC} ${CYAN}[$1]${NC} $2"
}

usage() {
    cat <<EOF
Usage: $(basename "$0") --prompt <prompt-id> [options]

Isabella Ralph Loop - Iterate until Isabelle proofs compile.

Options:
  --prompt <id>           Prompt ID from eval/prompts/ (required)
  --skill <name>          Skill to include (can be repeated)
  --iterations <n>        Max iterations (default: 5)
  --provider <name>       Work phase provider: openai, anthropic (default: openai)
  --model <model>         Work phase model (default: gpt-5.2-codex)
  --review-provider <p>   Review phase provider (default: openai)
  --review-model <m>      Review phase model (default: gpt-5.2-codex)
  --session <name>        Isabelle session name (default: LatticeCrypto)
  --output-dir <path>     Output directory (default: eval/work/<prompt-id>)
  --theory-name <name>    Theory name (default: same as session)
  --theory-path <path>    Subdirectory for theory (e.g., Linear)
  --root-dir <path>       Directory containing ROOT file
  --verbose               Enable verbose output
  -h, --help              Show this help

Examples:
  # Standard usage
  $(basename "$0") --prompt isabelle-lwe-encryption-01 \\
      --skill isabelle-basics \\
      --skill isabelle-code-generation \\
      --iterations 5

  # Canon usage with custom output
  $(basename "$0") --prompt canon-linear-listvec \\
      --output-dir Canon \\
      --theory-name ListVec \\
      --theory-path Linear \\
      --session Canon_Base \\
      --iterations 5
EOF
    exit 0
}

# Parse arguments
while [[ $# -gt 0 ]]; do
    case $1 in
        --prompt)
            PROMPT_ID="$2"
            shift 2
            ;;
        --skill)
            SKILLS+=("$2")
            shift 2
            ;;
        --iterations)
            MAX_ITERATIONS="$2"
            shift 2
            ;;
        --provider)
            PROVIDER="$2"
            shift 2
            ;;
        --model)
            MODEL="$2"
            shift 2
            ;;
        --review-provider)
            REVIEW_PROVIDER="$2"
            shift 2
            ;;
        --review-model)
            REVIEW_MODEL="$2"
            shift 2
            ;;
        --session)
            SESSION_NAME="$2"
            shift 2
            ;;
        --output-dir)
            OUTPUT_DIR="$2"
            shift 2
            ;;
        --theory-name)
            THEORY_NAME="$2"
            shift 2
            ;;
        --theory-path)
            THEORY_PATH="$2"
            shift 2
            ;;
        --root-dir)
            ROOT_DIR="$2"
            shift 2
            ;;
        --verbose)
            VERBOSE=true
            shift
            ;;
        -h|--help)
            usage
            ;;
        *)
            log_error "Unknown option: $1"
            exit 1
            ;;
    esac
done

# Validate
if [[ -z "$PROMPT_ID" ]]; then
    log_error "Missing required --prompt argument"
    usage
fi

# Build skill arguments
SKILL_ARGS=""
for skill in "${SKILLS[@]}"; do
    SKILL_ARGS+=" --skill $skill"
done

# State directory
STATE_DIR="${PROJECT_ROOT}/.ralph/${PROMPT_ID}"
mkdir -p "$STATE_DIR"

# Derive theory name from session if not specified
if [[ -z "$THEORY_NAME" ]]; then
    THEORY_NAME="$SESSION_NAME"
fi

# Work and results directories
if [[ -n "$OUTPUT_DIR" ]]; then
    # Custom output directory (e.g., Canon)
    if [[ "$OUTPUT_DIR" != /* ]]; then
        OUTPUT_DIR="${PROJECT_ROOT}/${OUTPUT_DIR}"
    fi
    if [[ -n "$THEORY_PATH" ]]; then
        WORK_DIR="${OUTPUT_DIR}/${THEORY_PATH}"
        mkdir -p "$WORK_DIR"
        THEORY_FILE="${WORK_DIR}/${THEORY_NAME}.thy"
    else
        WORK_DIR="$OUTPUT_DIR"
        mkdir -p "$WORK_DIR"
        THEORY_FILE="${WORK_DIR}/${THEORY_NAME}.thy"
    fi
    # ROOT directory - where the ROOT file is
    if [[ -n "$ROOT_DIR" ]]; then
        if [[ "$ROOT_DIR" != /* ]]; then
            ROOT_DIR="${PROJECT_ROOT}/${ROOT_DIR}"
        fi
    else
        ROOT_DIR="$OUTPUT_DIR"
    fi
else
    # Default: eval/work/<prompt-id>
    WORK_DIR="${EVAL_DIR}/work/${PROMPT_ID}"
    THEORY_FILE="${WORK_DIR}/${THEORY_NAME}.thy"
    ROOT_DIR="$WORK_DIR"
fi
RESULTS_DIR="${EVAL_DIR}/results/$(date +%Y-%m-%d)/${PROMPT_ID}"

# Banner
echo ""
echo -e "${BOLD}╔════════════════════════════════════════════════════════════╗${NC}"
echo -e "${BOLD}║${NC}           ${MAGENTA}Isabella Ralph Loop${NC}                              ${BOLD}║${NC}"
echo -e "${BOLD}║${NC}     ${DIM}Iterate until Isabelle proofs compile${NC}                  ${BOLD}║${NC}"
echo -e "${BOLD}╚════════════════════════════════════════════════════════════╝${NC}"
echo ""
log_info "Prompt: ${BOLD}${PROMPT_ID}${NC}"
log_info "Skills: ${CYAN}${SKILLS[*]:-none}${NC}"
log_info "Max iterations: ${MAX_ITERATIONS}"
log_info "Work: ${PROVIDER}/${MODEL}"
log_info "Review: ${REVIEW_PROVIDER}/${REVIEW_MODEL}"
log_info "Output: ${THEORY_FILE}"
log_info "Session: ${SESSION_NAME}"
echo ""

# Initialize state
echo "" > "${STATE_DIR}/feedback.md"
echo "0" > "${STATE_DIR}/iteration.txt"

# Main loop
for i in $(seq 1 "$MAX_ITERATIONS"); do
    echo "$i" > "${STATE_DIR}/iteration.txt"

    echo -e "${BLUE}═══════════════════════════════════════════════════════════════${NC}"
    log_iteration "Iteration $i / $MAX_ITERATIONS"
    echo -e "${BLUE}═══════════════════════════════════════════════════════════════${NC}"

    # =========================================================================
    # WORK PHASE: Generate Isabelle theory
    # =========================================================================
    log_phase "WORK" "Generating Isabelle theory..."

    # Check for feedback from previous iteration
    FEEDBACK_FILE="${STATE_DIR}/feedback.md"
    if [[ -s "$FEEDBACK_FILE" ]] && [[ $i -gt 1 ]]; then
        log_info "Incorporating feedback from previous iteration"

        # Create augmented prompt with feedback
        AUGMENTED_PROMPT_DIR="${STATE_DIR}/augmented"
        mkdir -p "$AUGMENTED_PROMPT_DIR"

        ORIGINAL_PROMPT="${EVAL_DIR}/prompts/${PROMPT_ID}.md"
        AUGMENTED_PROMPT="${AUGMENTED_PROMPT_DIR}/${PROMPT_ID}.md"

        cat > "$AUGMENTED_PROMPT" <<EOF
$(cat "$ORIGINAL_PROMPT")

---

## Previous Attempt Feedback (Iteration $((i-1)))

The previous attempt failed Isabelle verification. Here are the errors to fix:

\`\`\`
$(cat "$FEEDBACK_FILE")
\`\`\`

**IMPORTANT**: You MUST fix these errors. Do NOT use \`sorry\` - provide complete proofs.
Focus on addressing the specific errors mentioned above.
EOF

        # Clean work directory for fresh attempt
        rm -rf "$WORK_DIR"

        # Run with augmented prompt
        PROMPT_ARG="$AUGMENTED_PROMPT"
    else
        # First iteration - use original prompt
        rm -rf "$WORK_DIR"
        PROMPT_ARG="${PROMPT_ID}"
    fi

    # Run the work phase
    WORK_START=$(date +%s)
    set +e
    "${EVAL_DIR}/run-prompt.sh" \
        --prompt "$PROMPT_ARG" \
        $SKILL_ARGS \
        --schema default \
        --provider "$PROVIDER" \
        --model "$MODEL" \
        --session "$SESSION_NAME" \
        --no-verify \
        2>&1 | tee "${STATE_DIR}/work-${i}.log"
    WORK_EXIT=$?
    set -e
    WORK_END=$(date +%s)
    WORK_DURATION=$((WORK_END - WORK_START))

    if [[ $WORK_EXIT -ne 0 ]]; then
        log_error "Work phase failed (exit $WORK_EXIT)"
        continue
    fi

    log_success "Work phase completed in ${WORK_DURATION}s"

    # =========================================================================
    # REVIEW PHASE: Verify with Isabelle
    # =========================================================================
    log_phase "REVIEW" "Running Isabelle verification..."

    REVIEW_START=$(date +%s)

    # Run Isabelle build (strict mode - no quick_and_dirty)
    # Use ROOT_DIR for session root (where ROOT file lives)
    set +e
    isabelle build -v -d "$ROOT_DIR" "$SESSION_NAME" > "${STATE_DIR}/isabelle-${i}.log" 2>&1
    ISABELLE_EXIT=$?
    set -e

    REVIEW_END=$(date +%s)
    REVIEW_DURATION=$((REVIEW_END - REVIEW_START))

    if [[ $ISABELLE_EXIT -eq 0 ]]; then
        # SUCCESS!
        echo ""
        echo -e "${GREEN}═══════════════════════════════════════════════════════════════${NC}"
        echo -e "${GREEN}  ✓ SHIPPED after $i iteration(s)${NC}"
        echo -e "${GREEN}═══════════════════════════════════════════════════════════════${NC}"
        echo ""
        log_success "Isabelle verification passed in ${REVIEW_DURATION}s"
        log_success "Theory file: ${THEORY_FILE}"

        # Export Haskell code
        log_phase "EXPORT" "Generating Haskell code..."
        isabelle build -e -d "$ROOT_DIR" "$SESSION_NAME" 2>&1 || true

        # Mark complete
        echo "COMPLETE: $(date)" > "${STATE_DIR}/.ralph-complete"
        echo "$i" > "${STATE_DIR}/successful-iteration.txt"

        exit 0
    else
        # REVISE - extract errors as feedback
        log_warn "Isabelle verification failed (exit $ISABELLE_EXIT)"

        # Extract error messages for feedback
        log_phase "FEEDBACK" "Extracting error messages..."

        # Get the last 100 lines of errors, focusing on actual error content
        ERRORS=$(grep -E "(^\*\*\*|^Type error|^Illegal|^Bad|^Unknown|^Undefined|^Failed|sorry|cheating)" "${STATE_DIR}/isabelle-${i}.log" 2>/dev/null | tail -50 || cat "${STATE_DIR}/isabelle-${i}.log" | tail -50)

        # Also get the theory file for context
        THEORY_CONTENT=""
        if [[ -f "${THEORY_FILE}" ]]; then
            THEORY_CONTENT=$(cat "${THEORY_FILE}")
        fi

        # Prepare feedback for next iteration
        cat > "$FEEDBACK_FILE" <<EOF
## Isabelle Build Errors

$ERRORS

## Current Theory (with errors)

\`\`\`isabelle
$THEORY_CONTENT
\`\`\`
EOF

        log_info "Feedback saved for next iteration"
        echo ""
        echo -e "${YELLOW}↻ REVISE - Key errors:${NC}"
        echo "$ERRORS" | head -20
        echo ""
    fi

    # Cleanup for next iteration
    rm -f "${STATE_DIR}/work-complete.txt"
done

# Max iterations reached
echo ""
echo -e "${RED}═══════════════════════════════════════════════════════════════${NC}"
echo -e "${RED}  ✗ Max iterations ($MAX_ITERATIONS) reached without success${NC}"
echo -e "${RED}═══════════════════════════════════════════════════════════════${NC}"
echo ""
log_error "Failed to produce valid Isabelle proofs after $MAX_ITERATIONS attempts"
log_info "Last attempt logs: ${STATE_DIR}/isabelle-${MAX_ITERATIONS}.log"
log_info "Last theory: ${WORK_DIR}/${SESSION_NAME}.thy"

exit 1
