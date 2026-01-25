#!/bin/bash
#
# step-loop-v2.sh - Enhanced Step-based Ralph Loop with code review
#
# Improvements over v1:
# - Pre-build validation (proof/qed balance, syntax checks)
# - Exact code extraction when "USE THIS EXACT CODE" is specified
# - Two-LLM review system before Isabelle build
# - Intelligent error analysis with fix suggestions
# - Attempt history tracking to avoid repeating mistakes
#
# Usage:
#   ./step-loop-v2.sh --prompt <prompt-id> [options]
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
REVIEW_MODEL="claude-sonnet-4-20250514"  # Reviewer model
OUTPUT_DIR=""
THEORY_NAME=""
THEORY_PATH=""
SESSION_NAME=""
THEORY_IMPORTS='Main "HOL-Library.Code_Target_Numeral" "HOL-Number_Theory.Number_Theory"'
PARENT_SESSION=""
SESSION_DIR=""
VERBOSE=false
RESET=false
SKIP_REVIEW=false

# Logging
log_info() { echo -e "${DIM}[$(date '+%H:%M:%S')]${NC} ${BLUE}[INFO]${NC} $1"; }
log_step() { echo -e "${DIM}[$(date '+%H:%M:%S')]${NC} ${MAGENTA}[STEP]${NC} ${BOLD}$1${NC}"; }
log_success() { echo -e "${DIM}[$(date '+%H:%M:%S')]${NC} ${GREEN}[OK]${NC} $1"; }
log_warn() { echo -e "${DIM}[$(date '+%H:%M:%S')]${NC} ${YELLOW}[WARN]${NC} $1"; }
log_error() { echo -e "${DIM}[$(date '+%H:%M:%S')]${NC} ${RED}[ERROR]${NC} $1" >&2; }
log_review() { echo -e "${DIM}[$(date '+%H:%M:%S')]${NC} ${CYAN}[REVIEW]${NC} $1"; }

usage() {
    cat <<EOF
Usage: $(basename "$0") --prompt <prompt-id> [options]

Enhanced Step-based Ralph Loop with code review system.

Options:
  --prompt <id>           Prompt ID from eval/prompts/ (required)
  --skill <name>          Skill to include (can be repeated)
  --max-attempts <n>      Max attempts per step (default: 7)
  --provider <name>       AI provider (default: anthropic)
  --model <model>         Generator model (default: claude-sonnet-4-20250514)
  --review-model <model>  Reviewer model (default: claude-haiku-4-20250514)
  --output-dir <path>     Output directory for theory file
  --theory-name <name>    Theory name
  --theory-path <path>    Subdirectory (e.g., Linear)
  --session <name>        Isabelle session name
  --imports <string>      Theory imports
  --parent-session <name> Parent session for verification
  --session-dir <path>    Directory containing parent session ROOT file
  --skip-review           Skip LLM review (faster but less reliable)
  --reset                 Clear previous progress and start fresh
  --verbose               Verbose output
  -h, --help              Show this help

New in v2:
  - Automatic exact code extraction from prompts
  - Pre-build syntax validation
  - LLM code review before Isabelle build
  - Intelligent error analysis
  - Attempt history to avoid repeating mistakes
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
        --review-model) REVIEW_MODEL="$2"; shift 2 ;;
        --output-dir) OUTPUT_DIR="$2"; shift 2 ;;
        --theory-name) THEORY_NAME="$2"; shift 2 ;;
        --theory-path) THEORY_PATH="$2"; shift 2 ;;
        --session) SESSION_NAME="$2"; shift 2 ;;
        --imports) THEORY_IMPORTS="$2"; shift 2 ;;
        --parent-session) PARENT_SESSION="$2"; shift 2 ;;
        --session-dir) SESSION_DIR="$2"; shift 2 ;;
        --skip-review) SKIP_REVIEW=true; shift ;;
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
if [[ ${#SKILLS[@]} -gt 0 ]]; then
    for skill in "${SKILLS[@]}"; do
        skill_file="${PROJECT_ROOT}/skills/${skill}/SKILL.md"
        if [[ -f "$skill_file" ]]; then
            SKILL_CONTENT+="$(cat "$skill_file")"$'\n\n'
        fi
    done
fi

# ============================================================================
# NEW: Validation and Review Functions
# ============================================================================

# Check for balanced proof/qed pairs
check_proof_balance() {
    local file="$1"
    local proof_count
    local qed_count

    # Use grep -c with proper error handling
    proof_count=$(grep -cE '^\s*proof\b' "$file" 2>/dev/null) || proof_count=0
    qed_count=$(grep -cE '^\s*qed\b' "$file" 2>/dev/null) || qed_count=0

    # Trim whitespace and ensure numeric
    proof_count=$(echo "$proof_count" | tr -d '[:space:]')
    qed_count=$(echo "$qed_count" | tr -d '[:space:]')

    # Default to 0 if empty
    proof_count=${proof_count:-0}
    qed_count=${qed_count:-0}

    if [[ "$proof_count" -ne "$qed_count" ]]; then
        echo "UNBALANCED: $proof_count proof(s) vs $qed_count qed(s)"
        return 1
    fi
    return 0
}

# Check for common syntax issues
check_syntax_issues() {
    local file="$1"
    local issues=""

    # Check for unclosed proof blocks
    if ! check_proof_balance "$file" > /dev/null 2>&1; then
        issues+="- Unbalanced proof/qed pairs\n"
    fi

    # Check for sorry/oops
    if grep -qE '\bsorry\b|\boops\b' "$file"; then
        issues+="- Contains 'sorry' or 'oops' (incomplete proofs)\n"
    fi

    # Check for common Isabelle syntax errors
    if grep -qE '^\s*by\s*$' "$file"; then
        issues+="- Empty 'by' statement without method\n"
    fi

    # Check for backtick fact references (deprecated/problematic)
    if grep -qE '`[^`]+`' "$file"; then
        issues+="- Uses backtick fact references (use named facts instead)\n"
    fi

    if [[ -n "$issues" ]]; then
        echo -e "$issues"
        return 1
    fi
    return 0
}

# Extract exact code blocks from step content
extract_exact_code() {
    local step_content="$1"
    local output_file="$2"

    # Check if step contains "USE THIS EXACT CODE"
    if echo "$step_content" | grep -q "USE THIS EXACT CODE"; then
        # Extract the isabelle code block that follows
        echo "$step_content" | awk '
            /USE THIS EXACT CODE/,/```$/ {
                if (/```isabelle/) { in_code=1; next }
                if (/```$/ && in_code) { in_code=0; exit }
                if (in_code) print
            }
        ' > "$output_file"

        if [[ -s "$output_file" ]]; then
            return 0
        fi
    fi
    return 1
}

# LLM-based code review
review_code() {
    local code_file="$1"
    local step_content="$2"
    local review_output="$3"

    if [[ "$SKIP_REVIEW" == "true" ]]; then
        echo "VALID" > "$review_output"
        return 0
    fi

    cat > "${TEMP_DIR}/review_prompt.md" <<EOF
You are an Isabelle/HOL code reviewer. Review the following code for issues.

## Step Requirements
$step_content

## Generated Code
\`\`\`isabelle
$(cat "$code_file")
\`\`\`

## Review Checklist
1. **Syntactic completeness**: Are all proof/qed pairs balanced? All lemmas complete?
2. **Proof methods**: Does 'by (rule X)' need to be 'from facts by (intro X)' or 'using facts by blast'?
3. **Exact code**: If requirements say "USE THIS EXACT CODE", does the code match exactly?
4. **Common patterns**:
   - Max_in requires: from ne fin have ... by (intro Max_in)  NOT: ultimately have ... by (rule Max_in)
   - Named theorem attributes like [norm_simp] require: named_theorems norm_simp "..." first
   - Fact references should use named facts, not backticks

## Output Format
If code is valid, output exactly: VALID

If code has issues, output:
INVALID
Issue 1: [description]
Fix 1: [specific fix]
Issue 2: [description]
Fix 2: [specific fix]
...

Be concise. Only report actual issues that would cause Isabelle to fail.
EOF

    # Run review
    set +e
    claude --model "$REVIEW_MODEL" --print < "${TEMP_DIR}/review_prompt.md" > "$review_output" 2>/dev/null
    set -e
}

# Analyze build errors and provide structured feedback
analyze_error() {
    local build_log="$1"
    local analysis_output="$2"

    cat > "${TEMP_DIR}/error_prompt.md" <<EOF
Analyze this Isabelle build error and provide a specific fix.

## Build Log
\`\`\`
$(cat "$build_log" | grep -E "(^\*\*\*|error|failed|Undefined|Unknown)" | head -30)
\`\`\`

## Common Error Patterns and Fixes

1. "Undefined attribute: X"
   Fix: Add 'named_theorems X "description"' before using [X] attribute

2. "Failed to apply initial proof method" with "by (rule X)"
   Fix: Use 'from fact1 fact2 by (intro X)' or 'using fact1 fact2 by blast'

3. "Malformed command syntax"
   Fix: Usually means truncated proof - ensure all proof blocks end with 'qed'

4. "Type unification failed"
   Fix: Add type annotations like (n::nat) or (x::int)

5. "Outer syntax error: command expected but keyword ) found"
   Fix: Incomplete proof - add missing 'qed' or proof steps

## Output Format
Provide a brief, actionable fix (1-3 sentences). Be specific about what to change.
EOF

    set +e
    claude --model "$REVIEW_MODEL" --print < "${TEMP_DIR}/error_prompt.md" > "$analysis_output" 2>/dev/null
    set -e
}

# ============================================================================
# Step extraction functions
# ============================================================================

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

# ============================================================================
# State files
# ============================================================================
ACCUMULATED_FILE="${STATE_DIR}/accumulated.thy"
CURRENT_STEP_FILE="${STATE_DIR}/current_step.txt"
LAST_FEEDBACK_FILE="${STATE_DIR}/last_feedback.txt"
ATTEMPT_HISTORY_FILE="${STATE_DIR}/attempt_history.txt"

# Reset if requested
if [[ "$RESET" == "true" ]]; then
    log_info "Resetting progress..."
    rm -f "$ACCUMULATED_FILE" "$CURRENT_STEP_FILE" "$LAST_FEEDBACK_FILE" "$ATTEMPT_HISTORY_FILE" "${STATE_DIR}/.complete"
fi

# Banner
echo ""
echo -e "${BOLD}╔════════════════════════════════════════════════════════════╗${NC}"
echo -e "${BOLD}║${NC}     ${CYAN}Step-Based Ralph Loop v2${NC} ${DIM}(with code review)${NC}         ${BOLD}║${NC}"
echo -e "${BOLD}╚════════════════════════════════════════════════════════════╝${NC}"
echo ""
log_info "Prompt: ${BOLD}${PROMPT_ID}${NC}"
log_info "Output: ${THEORY_FILE}"
log_info "Generator: ${MODEL}"
log_info "Reviewer: ${REVIEW_MODEL}"
if [[ -n "$PARENT_SESSION" ]]; then
    log_info "Verification: builds on ${BOLD}${PARENT_SESSION}${NC}"
fi

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
    echo ""
    read -p "Re-run from scratch? [y/N] " -n 1 -r
    echo
    if [[ $REPLY =~ ^[Yy]$ ]]; then
        log_info "Clearing previous run..."
        rm -f "$ACCUMULATED_FILE" "$CURRENT_STEP_FILE" "$LAST_FEEDBACK_FILE" "$ATTEMPT_HISTORY_FILE" "${STATE_DIR}/.complete"
    else
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
        read -p "Resume from step ${SAVED_STEP}? [Y/n] " -n 1 -r
        echo
        if [[ ! $REPLY =~ ^[Nn]$ ]]; then
            START_STEP=$SAVED_STEP
            log_info "Resuming from step ${START_STEP}"
        else
            log_info "Starting fresh"
            rm -f "$ACCUMULATED_FILE" "$CURRENT_STEP_FILE" "$LAST_FEEDBACK_FILE" "$ATTEMPT_HISTORY_FILE"
        fi
    fi
fi

# Initialize files if starting fresh
if [[ ! -f "$ACCUMULATED_FILE" ]]; then
    echo "" > "$ACCUMULATED_FILE"
fi
if [[ ! -f "$ATTEMPT_HISTORY_FILE" ]]; then
    echo "" > "$ATTEMPT_HISTORY_FILE"
fi

echo ""

# ============================================================================
# Main loop
# ============================================================================
for step_num in $(seq "$START_STEP" "$TOTAL_STEPS"); do
    echo "$step_num" > "$CURRENT_STEP_FILE"

    # Clear attempt history for new step
    echo "" > "$ATTEMPT_HISTORY_FILE"

    echo -e "${BLUE}───────────────────────────────────────────────────────────────${NC}"
    log_step "Step $step_num / $TOTAL_STEPS"

    STEP_CONTENT=$(get_step_content "$PROMPT_FILE" "$step_num")
    echo -e "${DIM}$(echo "$STEP_CONTENT" | head -1)${NC}"

    # NEW: Check for exact code requirement
    EXACT_CODE_FILE="${TEMP_DIR}/exact_code.thy"
    USE_EXACT_CODE=false
    if extract_exact_code "$STEP_CONTENT" "$EXACT_CODE_FILE"; then
        USE_EXACT_CODE=true
        log_info "Found exact code requirement - will use provided code"
    fi

    # Load feedback from previous failed attempt
    FEEDBACK=""
    if [[ -f "$LAST_FEEDBACK_FILE" ]]; then
        FEEDBACK=$(cat "$LAST_FEEDBACK_FILE")
    fi

    STEP_PASSED=false
    ATTEMPT=1

    while [[ "$STEP_PASSED" == "false" ]]; do
        log_info "Attempt $ATTEMPT"

        CURRENT_ATTEMPT_FILE="${STATE_DIR}/current_attempt.thy"

        # ============================================================
        # GENERATION PHASE
        # ============================================================
        if [[ "$USE_EXACT_CODE" == "true" ]] && [[ $ATTEMPT -eq 1 ]]; then
            # Use exact code from prompt
            log_info "Using exact code from prompt"
            {
                echo "(* Step ${step_num}, Attempt ${ATTEMPT} - exact code from prompt *)"
                cat "$EXACT_CODE_FILE"
            } > "$CURRENT_ATTEMPT_FILE"
        else
            # Generate code with LLM
            cat > "${TEMP_DIR}/prompt.md" <<EOF
${SKILL_CONTENT}

# Current Task: Step ${step_num} of ${TOTAL_STEPS}

${STEP_CONTENT}

## Code So Far (verified working)

\`\`\`isabelle
$(cat "$ACCUMULATED_FILE")
\`\`\`

## Instructions

Write ONLY the Isabelle code for this step. Output just the code in a single \`\`\`isabelle code block.

### CRITICAL Requirements
- If the step provides **USE THIS EXACT CODE**, you MUST copy it EXACTLY character-for-character
- Every 'proof' must have a matching 'qed'
- Use 'from fact1 fact2 by (intro X)' instead of 'ultimately by (rule X)'
- Named attributes like [norm_simp] require 'named_theorems norm_simp "..."' first
- Name intermediate facts instead of using backtick references

### Output Format
- Output ONLY the new code for this step
- Do NOT repeat accumulated code
- NO sorry or oops
- Single \`\`\`isabelle code block
EOF

            if [[ -n "$FEEDBACK" ]]; then
                cat >> "${TEMP_DIR}/prompt.md" <<EOF

## Previous Attempt Failed

Error:
\`\`\`
${FEEDBACK}
\`\`\`

## Previous Attempts (avoid repeating these approaches)
$(cat "$ATTEMPT_HISTORY_FILE" | tail -20)

Make a DIFFERENT fix than previous attempts.
EOF
            fi

            # Generate
            set +e
            if [[ "$PROVIDER" == "anthropic" ]]; then
                claude --model "$MODEL" --print < "${TEMP_DIR}/prompt.md" > "${TEMP_DIR}/response.txt" 2>/dev/null
            else
                codex --model "$MODEL" < "${TEMP_DIR}/prompt.md" > "${TEMP_DIR}/response.txt" 2>/dev/null
            fi
            set -e

            # Extract code
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
        fi

        # ============================================================
        # PRE-BUILD VALIDATION PHASE
        # ============================================================
        log_info "Pre-build validation..."

        VALIDATION_ISSUES=""

        # Check proof/qed balance
        BALANCE_CHECK=$(check_proof_balance "$CURRENT_ATTEMPT_FILE" 2>&1) || true
        if [[ -n "$BALANCE_CHECK" ]]; then
            VALIDATION_ISSUES+="$BALANCE_CHECK\n"
            log_warn "Proof/qed imbalance detected: $BALANCE_CHECK"
        fi

        # Check for other syntax issues
        SYNTAX_CHECK=$(check_syntax_issues "$CURRENT_ATTEMPT_FILE" 2>&1) || true
        if [[ -n "$SYNTAX_CHECK" ]]; then
            VALIDATION_ISSUES+="$SYNTAX_CHECK"
            log_warn "Syntax issues detected"
        fi

        # If validation failed, skip to next attempt with feedback
        if [[ -n "$VALIDATION_ISSUES" ]]; then
            FEEDBACK="Pre-build validation failed:\n${VALIDATION_ISSUES}\n\nFix these issues before the code can be tested."
            echo -e "$FEEDBACK" > "$LAST_FEEDBACK_FILE"
            echo "Attempt $ATTEMPT: Pre-build validation failed - ${VALIDATION_ISSUES}" >> "$ATTEMPT_HISTORY_FILE"

            if [[ "$VERBOSE" == "true" ]]; then
                echo -e "${DIM}--- Validation Issues ---${NC}"
                echo -e "$VALIDATION_ISSUES"
            fi

            ATTEMPT=$((ATTEMPT + 1))
            if [[ $ATTEMPT -gt $MAX_ATTEMPTS ]]; then
                log_error "Step $step_num failed after $MAX_ATTEMPTS attempts"
                read -p "Continue with more attempts? [Y/n] " -n 1 -r
                echo
                if [[ $REPLY =~ ^[Nn]$ ]]; then
                    exit 1
                fi
                read -p "How many more attempts? [7] " MORE_ATTEMPTS
                MORE_ATTEMPTS=${MORE_ATTEMPTS:-7}
                MAX_ATTEMPTS=$((ATTEMPT + MORE_ATTEMPTS - 1))
            fi
            continue
        fi

        log_success "Pre-build validation passed"

        # ============================================================
        # LLM REVIEW PHASE
        # ============================================================
        if [[ "$SKIP_REVIEW" != "true" ]]; then
            log_review "Running code review..."
            REVIEW_FILE="${TEMP_DIR}/review_result.txt"
            review_code "$CURRENT_ATTEMPT_FILE" "$STEP_CONTENT" "$REVIEW_FILE"

            if grep -q "^INVALID" "$REVIEW_FILE"; then
                REVIEW_FEEDBACK=$(cat "$REVIEW_FILE" | tail -n +2)
                log_warn "Code review found issues"

                if [[ "$VERBOSE" == "true" ]]; then
                    echo -e "${DIM}--- Review Feedback ---${NC}"
                    echo "$REVIEW_FEEDBACK"
                fi

                FEEDBACK="Code review identified issues:\n${REVIEW_FEEDBACK}"
                echo -e "$FEEDBACK" > "$LAST_FEEDBACK_FILE"
                echo "Attempt $ATTEMPT: Review failed - $(echo "$REVIEW_FEEDBACK" | head -1)" >> "$ATTEMPT_HISTORY_FILE"

                ATTEMPT=$((ATTEMPT + 1))
                if [[ $ATTEMPT -gt $MAX_ATTEMPTS ]]; then
                    log_error "Step $step_num failed after $MAX_ATTEMPTS attempts"
                    read -p "Continue with more attempts? [Y/n] " -n 1 -r
                    echo
                    if [[ $REPLY =~ ^[Nn]$ ]]; then
                        exit 1
                    fi
                    read -p "How many more attempts? [7] " MORE_ATTEMPTS
                    MORE_ATTEMPTS=${MORE_ATTEMPTS:-7}
                    MAX_ATTEMPTS=$((ATTEMPT + MORE_ATTEMPTS - 1))
                fi
                continue
            fi
            log_success "Code review passed"
        fi

        # ============================================================
        # BUILD PHASE
        # ============================================================
        log_info "Building with Isabelle..."

        # Build test theory
        cat > "${TEMP_DIR}/test.thy" <<EOF
theory ${THEORY_NAME}
  imports ${THEORY_IMPORTS}
begin

$(cat "$ACCUMULATED_FILE")

(* Step ${step_num} *)
$(cat "$CURRENT_ATTEMPT_FILE")

end
EOF

        # Create test session
        mkdir -p "${TEMP_DIR}/test"
        cp "${TEMP_DIR}/test.thy" "${TEMP_DIR}/test/${THEORY_NAME}.thy"

        if [[ -n "$PARENT_SESSION" ]]; then
            cat > "${TEMP_DIR}/test/ROOT" <<EOF
session Test = ${PARENT_SESSION} +
  options [document = false]
  theories "${THEORY_NAME}"
EOF
        else
            cat > "${TEMP_DIR}/test/ROOT" <<EOF
session Test = HOL +
  options [document = false]
  sessions "HOL-Library" "HOL-Number_Theory"
  theories "${THEORY_NAME}"
EOF
        fi

        # Build
        set +e
        if [[ -n "$SESSION_DIR" ]]; then
            if [[ "$SESSION_DIR" != /* ]]; then
                SESSION_DIR="${PROJECT_ROOT}/${SESSION_DIR}"
            fi
            isabelle build -d "${SESSION_DIR}" -d "${TEMP_DIR}/test" Test > "${TEMP_DIR}/build.log" 2>&1
        else
            isabelle build -d "${TEMP_DIR}/test" Test > "${TEMP_DIR}/build.log" 2>&1
        fi
        BUILD_EXIT=$?
        set -e

        if [[ $BUILD_EXIT -eq 0 ]]; then
            # Final sorry check
            if grep -qE '\bsorry\b|\boops\b' "$CURRENT_ATTEMPT_FILE"; then
                FEEDBACK="Code contains 'sorry' or 'oops'. Provide complete proofs."
                echo "$FEEDBACK" > "$LAST_FEEDBACK_FILE"
                echo "Attempt $ATTEMPT: Contains sorry/oops" >> "$ATTEMPT_HISTORY_FILE"
            else
                log_success "Step $step_num passed!"

                # Append to accumulated
                echo "" >> "$ACCUMULATED_FILE"
                echo "(* === Step ${step_num} === *)" >> "$ACCUMULATED_FILE"
                tail -n +2 "$CURRENT_ATTEMPT_FILE" >> "$ACCUMULATED_FILE"

                rm -f "$LAST_FEEDBACK_FILE" "$CURRENT_ATTEMPT_FILE"
                STEP_PASSED=true
            fi
        else
            # Build failed - analyze error
            log_warn "Build failed"

            RAW_ERROR=$(grep -E "(^\*\*\*|Type error|Illegal|Bad|Unknown|Undefined|Failed|Inner lexical)" "${TEMP_DIR}/build.log" | head -20 || tail -20 "${TEMP_DIR}/build.log")

            # Get intelligent error analysis
            ANALYSIS_FILE="${TEMP_DIR}/error_analysis.txt"
            analyze_error "${TEMP_DIR}/build.log" "$ANALYSIS_FILE"

            ANALYZED_FIX=$(cat "$ANALYSIS_FILE" 2>/dev/null || echo "")

            FEEDBACK="Build error:\n${RAW_ERROR}\n\nSuggested fix:\n${ANALYZED_FIX}"
            echo -e "$FEEDBACK" > "$LAST_FEEDBACK_FILE"
            echo "Attempt $ATTEMPT: Build failed - $(echo "$RAW_ERROR" | head -1)" >> "$ATTEMPT_HISTORY_FILE"

            if [[ "$VERBOSE" == "true" ]]; then
                echo -e "${DIM}--- Build Error ---${NC}"
                echo "$RAW_ERROR" | head -10
                echo -e "${DIM}--- Suggested Fix ---${NC}"
                echo "$ANALYZED_FIX"
            fi
        fi

        # Check attempts
        if [[ "$STEP_PASSED" == "false" ]]; then
            ATTEMPT=$((ATTEMPT + 1))
            if [[ $ATTEMPT -gt $MAX_ATTEMPTS ]]; then
                echo ""
                log_error "Step $step_num failed after $MAX_ATTEMPTS attempts"
                echo ""
                echo -e "${YELLOW}Last error:${NC}"
                echo -e "$FEEDBACK" | head -15
                echo ""

                read -p "Continue with more attempts? [Y/n] " -n 1 -r
                echo
                if [[ $REPLY =~ ^[Nn]$ ]]; then
                    log_info "Progress saved. Run same command to resume."
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

# ============================================================================
# Completion
# ============================================================================
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

echo "COMPLETE: $(date)" > "${STATE_DIR}/.complete"
rm -f "$CURRENT_STEP_FILE" "$LAST_FEEDBACK_FILE" "$ATTEMPT_HISTORY_FILE"

# Final verification
if [[ -f "${OUTPUT_DIR}/ROOT" ]]; then
    log_info "Final verification against ${SESSION_NAME}..."
    set +e
    isabelle build -d "$OUTPUT_DIR" "$SESSION_NAME" > "${TEMP_DIR}/final.log" 2>&1
    FINAL_EXIT=$?
    set -e
    if [[ $FINAL_EXIT -eq 0 ]]; then
        log_success "Session build passed"
    else
        log_warn "Session build had issues - check imports"
    fi
fi

exit 0
