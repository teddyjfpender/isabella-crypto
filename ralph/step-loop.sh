#!/bin/bash
#
# step-loop.sh - Step-based Ralph Loop for incremental Isabelle theory development
#
# Features:
# - Processes prompts step-by-step with verification after each step
# - Persists progress to .ralph/<prompt>/ for resume capability
# - On failure, prompts to continue with more attempts
# - On success, writes final theory to output directory
#
# Usage:
#   ./step-loop.sh --prompt <prompt-id> [options]
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
MAX_ATTEMPTS=7
PROVIDER="anthropic"
MODEL="claude-sonnet-4-20250514"
OUTPUT_DIR=""
THEORY_NAME=""
THEORY_PATH=""
SESSION_NAME=""
THEORY_IMPORTS='Main "HOL-Library.Code_Target_Numeral" "HOL-Number_Theory.Number_Theory"'
VERBOSE=false
RESET=false

# Logging
log_info() { echo -e "${DIM}[$(date '+%H:%M:%S')]${NC} ${BLUE}[INFO]${NC} $1"; }
log_step() { echo -e "${DIM}[$(date '+%H:%M:%S')]${NC} ${MAGENTA}[STEP]${NC} ${BOLD}$1${NC}"; }
log_success() { echo -e "${DIM}[$(date '+%H:%M:%S')]${NC} ${GREEN}[OK]${NC} $1"; }
log_warn() { echo -e "${DIM}[$(date '+%H:%M:%S')]${NC} ${YELLOW}[WARN]${NC} $1"; }
log_error() { echo -e "${DIM}[$(date '+%H:%M:%S')]${NC} ${RED}[ERROR]${NC} $1" >&2; }

usage() {
    cat <<EOF
Usage: $(basename "$0") --prompt <prompt-id> [options]

Step-based Ralph Loop - Incremental theory development with per-step verification.
Progress is saved and can be resumed if interrupted or on failure.

Options:
  --prompt <id>           Prompt ID from eval/prompts/ (required)
  --skill <name>          Skill to include (can be repeated)
  --max-attempts <n>      Max attempts per step (default: 7)
  --provider <name>       AI provider (default: anthropic)
  --model <model>         Model (default: claude-sonnet-4-20250514)
  --output-dir <path>     Output directory for theory file
  --theory-name <name>    Theory name
  --theory-path <path>    Subdirectory (e.g., Linear)
  --session <name>        Isabelle session name
  --imports <string>      Theory imports (default: Main + HOL-Library + HOL-Number_Theory)
  --reset                 Clear previous progress and start fresh
  --verbose               Verbose output
  -h, --help              Show this help

Example:
  $(basename "$0") --prompt canon-linear-listvec \\
      --output-dir Canon \\
      --theory-name ListVec \\
      --theory-path Linear \\
      --session Canon_Base \\
      --imports 'Canon_Base.Prelude'
EOF
    exit 0
}

# Parse arguments
while [[ $# -gt 0 ]]; do
    case $1 in
        --prompt) PROMPT_ID="$2"; shift 2 ;;
        --skill) SKILLS+=("$2"); shift 2 ;;
        --max-attempts) MAX_ATTEMPTS="$2"; shift 2 ;;
        --provider) PROVIDER="$2"; shift 2 ;;
        --model) MODEL="$2"; shift 2 ;;
        --output-dir) OUTPUT_DIR="$2"; shift 2 ;;
        --theory-name) THEORY_NAME="$2"; shift 2 ;;
        --theory-path) THEORY_PATH="$2"; shift 2 ;;
        --session) SESSION_NAME="$2"; shift 2 ;;
        --imports) THEORY_IMPORTS="$2"; shift 2 ;;
        --reset) RESET=true; shift ;;
        --verbose) VERBOSE=true; shift ;;
        -h|--help) usage ;;
        *) log_error "Unknown option: $1"; exit 1 ;;
    esac
done

# Validate
if [[ -z "$PROMPT_ID" ]]; then
    log_error "Missing required --prompt argument"
    usage
fi

# Resolve prompt file
PROMPT_FILE="${EVAL_DIR}/prompts/${PROMPT_ID}.md"
if [[ ! -f "$PROMPT_FILE" ]]; then
    log_error "Prompt not found: $PROMPT_FILE"
    exit 1
fi

# Persistent state directory
STATE_DIR="${PROJECT_ROOT}/.ralph/${PROMPT_ID}"
mkdir -p "$STATE_DIR"

# Temp directory for ephemeral build files
TEMP_DIR=$(mktemp -d)
trap "rm -rf $TEMP_DIR" EXIT

# Determine output location
if [[ -z "$OUTPUT_DIR" ]]; then
    OUTPUT_DIR="${EVAL_DIR}/work/${PROMPT_ID}"
fi
if [[ "$OUTPUT_DIR" != /* ]]; then
    OUTPUT_DIR="${PROJECT_ROOT}/${OUTPUT_DIR}"
fi

if [[ -n "$THEORY_PATH" ]]; then
    mkdir -p "${OUTPUT_DIR}/${THEORY_PATH}"
    THEORY_FILE="${OUTPUT_DIR}/${THEORY_PATH}/${THEORY_NAME}.thy"
else
    mkdir -p "$OUTPUT_DIR"
    THEORY_FILE="${OUTPUT_DIR}/${THEORY_NAME:-LatticeCrypto}.thy"
fi

SESSION_NAME="${SESSION_NAME:-LatticeCrypto}"
THEORY_NAME="${THEORY_NAME:-LatticeCrypto}"

# Build skill content
SKILL_CONTENT=""
for skill in "${SKILLS[@]}"; do
    skill_file="${PROJECT_ROOT}/skills/${skill}/SKILL.md"
    if [[ -f "$skill_file" ]]; then
        SKILL_CONTENT+="$(cat "$skill_file")"$'\n\n'
    fi
done

# Extract steps from prompt
count_steps() {
    grep -c "^### Step [0-9]" "$1" || echo "0"
}

get_step_content() {
    local prompt_file="$1"
    local step_num="$2"
    local step_lines
    step_lines=$(grep -n "^### Step [0-9]" "$prompt_file" | cut -d: -f1)
    local start_line end_line
    start_line=$(echo "$step_lines" | sed -n "${step_num}p")
    end_line=$(echo "$step_lines" | sed -n "$((step_num + 1))p")
    if [[ -z "$end_line" ]]; then
        end_line=$(awk "NR>$start_line && /^## [^#]/{print NR; exit}" "$prompt_file")
        if [[ -z "$end_line" ]]; then
            end_line=$(wc -l < "$prompt_file" | tr -d ' ')
        fi
    fi
    sed -n "${start_line},$((end_line - 1))p" "$prompt_file"
}

# State files
ACCUMULATED_FILE="${STATE_DIR}/accumulated.thy"
CURRENT_STEP_FILE="${STATE_DIR}/current_step.txt"
LAST_FEEDBACK_FILE="${STATE_DIR}/last_feedback.txt"

# Reset if requested
if [[ "$RESET" == "true" ]]; then
    log_info "Resetting progress..."
    rm -f "$ACCUMULATED_FILE" "$CURRENT_STEP_FILE" "$LAST_FEEDBACK_FILE"
fi

# Banner
echo ""
echo -e "${BOLD}╔════════════════════════════════════════════════════════════╗${NC}"
echo -e "${BOLD}║${NC}           ${CYAN}Step-Based Ralph Loop${NC}                           ${BOLD}║${NC}"
echo -e "${BOLD}╚════════════════════════════════════════════════════════════╝${NC}"
echo ""
log_info "Prompt: ${BOLD}${PROMPT_ID}${NC}"
log_info "Output: ${THEORY_FILE}"
log_info "Session: ${SESSION_NAME}"

TOTAL_STEPS=$(count_steps "$PROMPT_FILE")
log_info "Total steps: ${TOTAL_STEPS}"

if [[ "$TOTAL_STEPS" -eq 0 ]]; then
    log_error "No steps found in prompt (looking for '### Step N:' markers)"
    exit 1
fi

# Check if already complete
if [[ -f "${STATE_DIR}/.complete" ]]; then
    echo ""
    log_success "This prompt was already completed!"
    log_info "Output: ${THEORY_FILE}"
    log_info "State: ${STATE_DIR}"
    echo ""
    read -p "Re-run from scratch? [y/N] " -n 1 -r
    echo
    if [[ $REPLY =~ ^[Yy]$ ]]; then
        log_info "Clearing previous run..."
        rm -f "$ACCUMULATED_FILE" "$CURRENT_STEP_FILE" "$LAST_FEEDBACK_FILE" "${STATE_DIR}/.complete"
    else
        log_info "Exiting. Use --reset to force a fresh run."
        exit 0
    fi
fi

# Check for existing progress
START_STEP=1
if [[ -f "$CURRENT_STEP_FILE" ]]; then
    SAVED_STEP=$(cat "$CURRENT_STEP_FILE")
    if [[ "$SAVED_STEP" -gt 1 ]] && [[ "$SAVED_STEP" -le "$TOTAL_STEPS" ]]; then
        echo ""
        log_info "Found existing progress: step ${SAVED_STEP}/${TOTAL_STEPS}"
        if [[ -f "$ACCUMULATED_FILE" ]]; then
            LINES=$(wc -l < "$ACCUMULATED_FILE" | tr -d ' ')
            log_info "Accumulated code: ${LINES} lines"
        fi
        echo ""
        read -p "Resume from step ${SAVED_STEP}? [Y/n] " -n 1 -r
        echo
        if [[ ! $REPLY =~ ^[Nn]$ ]]; then
            START_STEP=$SAVED_STEP
            log_info "Resuming from step ${START_STEP}"
        else
            log_info "Starting fresh"
            rm -f "$ACCUMULATED_FILE" "$CURRENT_STEP_FILE" "$LAST_FEEDBACK_FILE"
        fi
    fi
fi

# Initialize accumulated file if starting fresh
if [[ ! -f "$ACCUMULATED_FILE" ]]; then
    echo "" > "$ACCUMULATED_FILE"
fi

echo ""

# Process each step
for step_num in $(seq "$START_STEP" "$TOTAL_STEPS"); do
    echo "$step_num" > "$CURRENT_STEP_FILE"

    echo -e "${BLUE}───────────────────────────────────────────────────────────────${NC}"
    log_step "Step $step_num / $TOTAL_STEPS"

    STEP_CONTENT=$(get_step_content "$PROMPT_FILE" "$step_num")
    echo -e "${DIM}$(echo "$STEP_CONTENT" | head -1)${NC}"

    # Load feedback from previous failed attempt on this step
    FEEDBACK=""
    if [[ -f "$LAST_FEEDBACK_FILE" ]]; then
        FEEDBACK=$(cat "$LAST_FEEDBACK_FILE")
    fi

    STEP_PASSED=false
    ATTEMPT=1

    while [[ "$STEP_PASSED" == "false" ]]; do
        if [[ $ATTEMPT -gt 1 ]]; then
            log_info "Attempt $ATTEMPT"
        fi

        # Build prompt
        cat > "${TEMP_DIR}/prompt.md" <<EOF
${SKILL_CONTENT}

# Current Task: Step ${step_num} of ${TOTAL_STEPS}

${STEP_CONTENT}

## Code So Far (verified working)

\`\`\`isabelle
$(cat "$ACCUMULATED_FILE")
\`\`\`

## Instructions

Write ONLY the Isabelle code for this step. Output just the code, no explanation.

### CRITICAL: Use Exact Code
- If the step provides **USE THIS EXACT CODE**, copy it EXACTLY - do not simplify or modify
- The provided proofs have been verified to work; simplified versions often fail

### Proof Robustness
- Do NOT rely on \`auto\` or \`simp\` for complex goals - they are non-deterministic
- Use explicit case splits for conditionals: \`proof (cases "condition")\`
- Type annotations like \`(n::int)\` are required for numeric lemmas to work
- Prefer \`arith\` over \`auto\` for div/mod arithmetic
- Name intermediate facts for debugging

### Output Format
- Do NOT repeat the accumulated code above
- NO sorry or oops - complete proofs only
- Code will be appended to what's above
- Use proper Isabelle syntax (=> not ⇒ unless in strings)
EOF

        if [[ -n "$FEEDBACK" ]]; then
            cat >> "${TEMP_DIR}/prompt.md" <<EOF

## Fix Required

Previous attempt failed:
\`\`\`
${FEEDBACK}
\`\`\`
EOF
        fi

        # Generate code
        set +e
        if [[ "$PROVIDER" == "anthropic" ]]; then
            claude --model "$MODEL" --print < "${TEMP_DIR}/prompt.md" > "${TEMP_DIR}/response.txt" 2>/dev/null
        else
            codex --model "$MODEL" < "${TEMP_DIR}/prompt.md" > "${TEMP_DIR}/response.txt" 2>/dev/null
        fi
        set -e

        # Extract isabelle code to persistent current_attempt.thy
        CURRENT_ATTEMPT_FILE="${STATE_DIR}/current_attempt.thy"
        {
            echo "(* Step ${step_num}, Attempt ${ATTEMPT} - $(date) *)"
            if grep -q '```isabelle' "${TEMP_DIR}/response.txt"; then
                sed -n '/```isabelle/,/```/p' "${TEMP_DIR}/response.txt" | sed '1d;$d'
            elif grep -q '```' "${TEMP_DIR}/response.txt"; then
                sed -n '/```/,/```/p' "${TEMP_DIR}/response.txt" | sed '1d;$d'
            else
                cat "${TEMP_DIR}/response.txt"
            fi
        } > "$CURRENT_ATTEMPT_FILE"
        log_info "Attempt written to ${CURRENT_ATTEMPT_FILE}"

        # Build test theory using current_attempt.thy
        cat > "${TEMP_DIR}/test.thy" <<EOF
theory ${THEORY_NAME}
  imports Main "HOL-Library.Code_Target_Numeral" "HOL-Number_Theory.Number_Theory"
begin

$(cat "$ACCUMULATED_FILE")

(* Step ${step_num} *)
$(cat "$CURRENT_ATTEMPT_FILE")

end
EOF

        # Create test session
        mkdir -p "${TEMP_DIR}/test"
        cp "${TEMP_DIR}/test.thy" "${TEMP_DIR}/test/${THEORY_NAME}.thy"
        cat > "${TEMP_DIR}/test/ROOT" <<EOF
session Test = HOL +
  options [document = false]
  sessions "HOL-Library" "HOL-Number_Theory"
  theories "${THEORY_NAME}"
EOF

        # Verify
        set +e
        isabelle build -d "${TEMP_DIR}/test" Test > "${TEMP_DIR}/build.log" 2>&1
        BUILD_EXIT=$?
        set -e

        if [[ $BUILD_EXIT -eq 0 ]]; then
            # Check for sorry
            if grep -qE '\bsorry\b|\boops\b' "$CURRENT_ATTEMPT_FILE"; then
                FEEDBACK="Code contains 'sorry' or 'oops'. Provide complete proofs."
                echo "$FEEDBACK" > "$LAST_FEEDBACK_FILE"
            else
                log_success "Step $step_num passed"

                # Append current_attempt to accumulated (verified code)
                echo "" >> "$ACCUMULATED_FILE"
                echo "(* === Step ${step_num} === *)" >> "$ACCUMULATED_FILE"
                # Skip the metadata comment line when appending
                tail -n +2 "$CURRENT_ATTEMPT_FILE" >> "$ACCUMULATED_FILE"

                # Clear feedback and current attempt (step passed)
                rm -f "$LAST_FEEDBACK_FILE"
                rm -f "$CURRENT_ATTEMPT_FILE"

                STEP_PASSED=true
            fi
        else
            # Extract errors
            FEEDBACK=$(grep -E "(^\*\*\*|Type error|Illegal|Bad|Unknown|Undefined|Failed|Inner lexical)" "${TEMP_DIR}/build.log" | head -20 || tail -20 "${TEMP_DIR}/build.log")
            echo "$FEEDBACK" > "$LAST_FEEDBACK_FILE"
            log_warn "Build failed (see current_attempt.thy and last_feedback.txt)"
            if [[ "$VERBOSE" == "true" ]]; then
                echo -e "${DIM}--- Attempted code ---${NC}"
                cat "$CURRENT_ATTEMPT_FILE" | head -20
                echo -e "${DIM}--- Error ---${NC}"
                echo "$FEEDBACK" | head -10
            fi
        fi

        # Check if we've exhausted attempts
        if [[ "$STEP_PASSED" == "false" ]]; then
            ATTEMPT=$((ATTEMPT + 1))
            if [[ $ATTEMPT -gt $MAX_ATTEMPTS ]]; then
                echo ""
                log_error "Step $step_num failed after $MAX_ATTEMPTS attempts"
                echo ""
                echo -e "${YELLOW}Last error:${NC}"
                echo "$FEEDBACK" | head -10
                echo ""

                # Prompt to continue
                read -p "Continue with more attempts? [Y/n] " -n 1 -r
                echo
                if [[ $REPLY =~ ^[Nn]$ ]]; then
                    log_info "Progress saved. Run same command to resume."
                    log_info "State dir: ${STATE_DIR}"
                    exit 1
                fi

                read -p "How many more attempts? [7] " MORE_ATTEMPTS
                MORE_ATTEMPTS=${MORE_ATTEMPTS:-7}
                MAX_ATTEMPTS=$((ATTEMPT + MORE_ATTEMPTS - 1))
                log_info "Continuing with ${MORE_ATTEMPTS} more attempts..."
            fi
        fi
    done
done

# All steps done - write final theory
echo ""
echo -e "${GREEN}═══════════════════════════════════════════════════════════════${NC}"
log_success "All $TOTAL_STEPS steps completed!"
echo -e "${GREEN}═══════════════════════════════════════════════════════════════${NC}"

cat > "$THEORY_FILE" <<EOF
theory ${THEORY_NAME}
  imports ${THEORY_IMPORTS}
begin

$(cat "$ACCUMULATED_FILE")

end
EOF

log_success "Written: $THEORY_FILE"

# Mark complete
echo "COMPLETE: $(date)" > "${STATE_DIR}/.complete"
rm -f "$CURRENT_STEP_FILE" "$LAST_FEEDBACK_FILE"

# Final verification against real session
if [[ -f "${OUTPUT_DIR}/ROOT" ]]; then
    log_info "Final verification against ${SESSION_NAME}..."
    set +e
    isabelle build -d "$OUTPUT_DIR" "$SESSION_NAME" > "${TEMP_DIR}/final.log" 2>&1
    FINAL_EXIT=$?
    set -e
    if [[ $FINAL_EXIT -eq 0 ]]; then
        log_success "Session build passed"
    else
        log_warn "Session build had issues - theory may need import adjustments"
        [[ "$VERBOSE" == "true" ]] && tail -10 "${TEMP_DIR}/final.log"
    fi
fi

exit 0
