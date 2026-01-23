#!/usr/bin/env bash
#
# run-prompt.sh - Main orchestration script for Isabella (Isabelle + Lattice) evaluation
#
# Runs a single evaluation prompt through an AI model and verifies the output
# using Isabelle's build system.
#
# Usage:
#   ./run-prompt.sh --prompt <id|path> [options]
#
# Options:
#   --prompt <id|path>      Prompt ID or path (required). If just an ID, looks in prompts/
#   --skill <name>          Skill name to prepend (can be used multiple times)
#   --disable-skills        Do not load any skill prefixes
#   --schema <path|default> Path to JSON schema, or "default" for code-output schema
#   --provider <provider>   AI provider: openai, anthropic (default: openai)
#   --model <model>         Model to use (default: gpt-5.2-codex for openai)
#   --out-file <file>       Output theory file path
#   --work-dir <dir>        Working directory for Isabelle project
#   --results-dir <dir>     Directory for results (default: ./results/YYYY-MM-DD)
#   --no-verify             Skip verification step
#   --no-scaffold           Skip project scaffolding
#   --session <name>        Isabelle session name (default: LatticeCrypto)
#   --verbose               Enable verbose output
#   --dry-run               Show what would be done without executing
#   --tail                  Tail output in real-time
#
# Examples:
#   ./run-prompt.sh --prompt isabelle-vector-ops-01 --skill isabelle-basics --schema default
#   ./run-prompt.sh --prompt isabelle-lwe-encryption-01 \
#       --skill isabelle-basics \
#       --skill isabelle-code-generation \
#       --schema default --tail
#   ./run-prompt.sh --prompt isabelle-vector-ops-01 --provider anthropic --model claude-sonnet-4-20250514
#
set -euo pipefail

# Script directory
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"

# Default values
PROMPT_INPUT=""
SKILLS=()
DISABLE_SKILLS=false
SCHEMA_FILE=""
PROVIDER="openai"
MODEL=""  # Will be set based on provider if not specified
OUT_FILE=""
WORK_DIR=""
RESULTS_DIR=""
NO_VERIFY=false
NO_SCAFFOLD=false
SESSION_NAME="LatticeCrypto"
VERBOSE=false
DRY_RUN=false
TAIL_OUTPUT=false

# Default models per provider
DEFAULT_MODEL_OPENAI="gpt-5.2-codex"
DEFAULT_MODEL_ANTHROPIC="claude-sonnet-4-20250514"

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
CYAN='\033[0;36m'
MAGENTA='\033[0;35m'
BOLD='\033[1m'
DIM='\033[2m'
NC='\033[0m' # No Color

# Logging functions with timestamps
log_ts() {
    echo -e "${DIM}[$(date '+%H:%M:%S')]${NC} $1"
}

log_info() {
    echo -e "${DIM}[$(date '+%H:%M:%S')]${NC} ${BLUE}[INFO]${NC} $1"
}

log_step() {
    echo -e "${DIM}[$(date '+%H:%M:%S')]${NC} ${MAGENTA}[STEP]${NC} ${BOLD}$1${NC}"
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

log_verbose() {
    if [[ "$VERBOSE" == "true" ]]; then
        echo -e "${DIM}[$(date '+%H:%M:%S')]${NC} ${CYAN}[DEBUG]${NC} $1"
    fi
}

log_ai() {
    echo -e "${DIM}[$(date '+%H:%M:%S')]${NC} ${GREEN}[AI]${NC} $1"
}

usage() {
    cat <<EOF
Usage: $(basename "$0") --prompt <id|path> [options]

Run an Isabella evaluation prompt through an AI model and verify with Isabelle.

Options:
  --prompt <id|path>      Prompt ID or path (required)
                          If just an ID, looks in ${SCRIPT_DIR}/prompts/<id>.md
  --skill <name>          Skill to prepend to prompt (can be repeated)
                          Looks in ${PROJECT_ROOT}/skills/<name>/
  --disable-skills        Do not load any skill prefixes
  --schema <path|default> JSON schema for output ("default" uses code-output schema)
  --provider <name>       AI provider: openai, anthropic (default: openai)
  --model <model>         Model name (default: gpt-5.2-codex for openai, claude-sonnet-4-20250514 for anthropic)
  --out-file <file>       Output theory file path
  --work-dir <dir>        Isabelle project directory
  --results-dir <dir>     Results directory (default: eval/results/YYYY-MM-DD)
  --no-verify             Skip Isabelle verification
  --no-scaffold           Skip project scaffolding
  --session <name>        Isabelle session name (default: ${SESSION_NAME})
  --verbose               Verbose output
  --dry-run               Preview without executing
  --tail                  Show output in real-time
  -h, --help              Show this help

Providers:
  openai      Use OpenAI Codex CLI (default)
  anthropic   Use Anthropic Claude CLI

Examples:
  # Run with OpenAI Codex (default)
  $(basename "$0") --prompt isabelle-vector-ops-01 --skill isabelle-basics --schema default

  # Run with specific provider and model
  $(basename "$0") --prompt isabelle-lwe-encryption-01 --provider openai --model gpt-5.2-codex

  # Run with Anthropic Claude
  $(basename "$0") --prompt isabelle-vector-ops-01 --provider anthropic --model claude-sonnet-4-20250514

  # Run with multiple skills and real-time output
  $(basename "$0") --prompt isabelle-lwe-encryption-01 \\
      --skill isabelle-basics \\
      --skill isabelle-code-generation \\
      --schema default --tail
EOF
    exit 0
}

# Resolve prompt path from ID or path
resolve_prompt() {
    local input="$1"

    # If it's already a file path
    if [[ -f "$input" ]]; then
        echo "$input"
        return 0
    fi

    # Try as ID in prompts directory
    local prompt_path="${SCRIPT_DIR}/prompts/${input}.md"
    if [[ -f "$prompt_path" ]]; then
        echo "$prompt_path"
        return 0
    fi

    # Try without .md extension
    prompt_path="${SCRIPT_DIR}/prompts/${input}"
    if [[ -f "$prompt_path" ]]; then
        echo "$prompt_path"
        return 0
    fi

    return 1
}

# Resolve skill path from name
resolve_skill() {
    local name="$1"
    local skill_dir="${PROJECT_ROOT}/skills/${name}"
    local skill_file="${skill_dir}/SKILL.md"

    if [[ -f "$skill_file" ]]; then
        echo "$skill_file"
        return 0
    fi

    # Try direct path
    if [[ -f "$name" ]]; then
        echo "$name"
        return 0
    fi

    return 1
}

# Parse command line arguments
while [[ $# -gt 0 ]]; do
    case $1 in
        --prompt)
            PROMPT_INPUT="$2"
            shift 2
            ;;
        --skill)
            SKILLS+=("$2")
            shift 2
            ;;
        --disable-skills)
            DISABLE_SKILLS=true
            shift
            ;;
        --schema)
            if [[ "$2" == "default" ]]; then
                SCHEMA_FILE="${SCRIPT_DIR}/schema/code-output.schema.json"
            else
                SCHEMA_FILE="$2"
            fi
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
        --tail)
            TAIL_OUTPUT=true
            shift
            ;;
        -h|--help)
            usage
            ;;
        --)
            shift
            break
            ;;
        *)
            log_error "Unknown option: $1"
            echo "Use --help for usage information"
            exit 1
            ;;
    esac
done

# Validate required arguments
if [[ -z "$PROMPT_INPUT" ]]; then
    log_error "Missing required argument: --prompt"
    echo "Use --help for usage information"
    exit 2
fi

# Validate and normalize provider
PROVIDER=$(echo "$PROVIDER" | tr '[:upper:]' '[:lower:]')
case "$PROVIDER" in
    openai|codex)
        PROVIDER="openai"
        ;;
    anthropic|claude)
        PROVIDER="anthropic"
        ;;
    *)
        log_error "Unknown provider: $PROVIDER"
        log_error "Supported providers: openai, anthropic"
        exit 2
        ;;
esac

# Set default model based on provider if not specified
if [[ -z "$MODEL" ]]; then
    case "$PROVIDER" in
        openai)
            MODEL="$DEFAULT_MODEL_OPENAI"
            ;;
        anthropic)
            MODEL="$DEFAULT_MODEL_ANTHROPIC"
            ;;
    esac
fi

# Resolve prompt file
PROMPT_FILE=$(resolve_prompt "$PROMPT_INPUT") || {
    log_error "Prompt not found: $PROMPT_INPUT"
    log_error "Looked in: ${SCRIPT_DIR}/prompts/${PROMPT_INPUT}.md"
    exit 2
}

# Extract prompt ID from filename
PROMPT_ID=$(basename "$PROMPT_FILE" .md)

# Set up results directory with date
if [[ -z "$RESULTS_DIR" ]]; then
    RESULTS_DIR="${SCRIPT_DIR}/results/$(date +%Y-%m-%d)"
fi
RUN_RESULTS_DIR="${RESULTS_DIR}/${PROMPT_ID}"

# Set up work directory
if [[ -z "$WORK_DIR" ]]; then
    WORK_DIR="${SCRIPT_DIR}/work/${PROMPT_ID}"
fi

# Set up output file
if [[ -z "$OUT_FILE" ]]; then
    OUT_FILE="${WORK_DIR}/${SESSION_NAME}.thy"
fi

# Print banner
echo ""
echo -e "${BOLD}╔════════════════════════════════════════════════════════════╗${NC}"
echo -e "${BOLD}║${NC}              ${MAGENTA}Isabella Evaluation Runner${NC}                   ${BOLD}║${NC}"
echo -e "${BOLD}╚════════════════════════════════════════════════════════════╝${NC}"
echo ""

log_info "Prompt ID: ${BOLD}${PROMPT_ID}${NC}"
log_info "Prompt file: ${PROMPT_FILE}"
if [[ ${#SKILLS[@]} -gt 0 ]]; then
    log_info "Skills: ${CYAN}${SKILLS[*]}${NC}"
else
    log_info "Skills: (none)"
fi
log_info "Provider: ${PROVIDER}"
log_info "Model: ${MODEL}"
log_info "Session: ${SESSION_NAME}"
log_verbose "Work directory: ${WORK_DIR}"
log_verbose "Results directory: ${RUN_RESULTS_DIR}"
log_verbose "Output file: ${OUT_FILE}"
echo ""

# Record start time
RUN_STARTED_AT="$(date -u +%Y-%m-%dT%H:%M:%SZ)"

# Create directories
if [[ "$DRY_RUN" == "false" ]]; then
    mkdir -p "$WORK_DIR"
    mkdir -p "$RUN_RESULTS_DIR"
    log_verbose "Created directories"
fi

# ============================================================================
# STEP 1: Scaffold
# ============================================================================
if [[ "$NO_SCAFFOLD" == "false" ]]; then
    log_step "1/5 Scaffolding Isabelle project..."

    if [[ "$DRY_RUN" == "false" ]]; then
        if [[ ! -f "${WORK_DIR}/ROOT" ]]; then
            if [[ -x "${SCRIPT_DIR}/scaffold.sh" ]]; then
                "${SCRIPT_DIR}/scaffold.sh" --work-dir "$WORK_DIR" --session "$SESSION_NAME"
            else
                log_warn "scaffold.sh not found, creating minimal structure"
                mkdir -p "${WORK_DIR}"
                cat > "${WORK_DIR}/ROOT" <<ROOTEOF
session "${SESSION_NAME}" = HOL +
  options [document = false, timeout = 300]
  sessions
    "HOL-Library"
    "HOL-Number_Theory"
  theories
    ${SESSION_NAME}
  export_files (in "generated") [1]
    "*:**/*.hs"
ROOTEOF
            fi
            log_success "Project scaffolded"
        else
            log_info "ROOT file already exists, skipping scaffold"
        fi
    else
        log_info "[DRY-RUN] Would scaffold project in ${WORK_DIR}"
    fi
else
    log_step "1/5 Scaffolding... SKIPPED (--no-scaffold)"
fi

# ============================================================================
# STEP 2: Build Prompt
# ============================================================================
log_step "2/5 Building combined prompt..."

FULL_PROMPT=""
SKILLS_STRING=""

# Add schema preamble if provided
if [[ -n "$SCHEMA_FILE" ]]; then
    if [[ -f "$SCHEMA_FILE" ]]; then
        log_verbose "Adding schema preamble"
        FULL_PROMPT+='Return JSON only with shape {"code": string, "notes": string}. Put the complete Isabelle theory in "code". Put any caveats or explanation in "notes" (empty string ok). Do not include Markdown or code fences.

'
    else
        log_warn "Schema file not found: ${SCHEMA_FILE}"
    fi
fi

# Add skill prefixes if provided and not disabled
if [[ "$DISABLE_SKILLS" == "false" ]] && [[ ${#SKILLS[@]} -gt 0 ]]; then
    log_info "Loading ${#SKILLS[@]} skill(s)..."

    for skill_name in "${SKILLS[@]}"; do
        SKILL_FILE=$(resolve_skill "$skill_name") || {
            log_warn "Skill not found: ${skill_name}"
            continue
        }

        log_verbose "  Loading: ${skill_name}"
        SKILL_CONTENT=$(cat "$SKILL_FILE")
        SKILLS_STRING+="${skill_name} "

        # Also load references if they exist
        SKILL_DIR=$(dirname "$SKILL_FILE")
        REFS_DIR="${SKILL_DIR}/references"

        FULL_PROMPT+="## Skill: ${skill_name}

${SKILL_CONTENT}

"

        # Include reference files
        if [[ -d "$REFS_DIR" ]]; then
            for ref_file in "${REFS_DIR}"/*.md; do
                if [[ -f "$ref_file" ]]; then
                    ref_name=$(basename "$ref_file" .md)
                    log_verbose "    Reference: ${ref_name}"
                    FULL_PROMPT+="### Reference: ${ref_name}

$(cat "$ref_file")

"
                fi
            done
        fi
    done

    FULL_PROMPT+="---

"
    log_success "Loaded skills: ${SKILLS_STRING}"
fi

# Add main prompt
PROMPT_CONTENT=$(cat "$PROMPT_FILE")
FULL_PROMPT+="${PROMPT_CONTENT}"

# Save combined prompt
COMBINED_PROMPT_FILE="${RUN_RESULTS_DIR}/prompt.txt"
if [[ "$DRY_RUN" == "false" ]]; then
    echo "$FULL_PROMPT" > "$COMBINED_PROMPT_FILE"
    PROMPT_LINES=$(wc -l < "$COMBINED_PROMPT_FILE" | tr -d ' ')
    PROMPT_BYTES=$(wc -c < "$COMBINED_PROMPT_FILE" | tr -d ' ')
    log_success "Combined prompt: ${PROMPT_LINES} lines, ${PROMPT_BYTES} bytes"
fi

# ============================================================================
# STEP 3: Run AI Model
# ============================================================================
log_step "3/5 Running AI (${PROVIDER}/${MODEL})..."

AI_JSONL="${RUN_RESULTS_DIR}/ai.jsonl"
AI_STDERR="${RUN_RESULTS_DIR}/ai.stderr"
ASSISTANT_OUTPUT="${RUN_RESULTS_DIR}/assistant_last.txt"

# Function to run the AI command based on provider
run_ai_command() {
    local prompt="$1"
    local output_file="$2"
    local stderr_file="$3"
    local stream="$4"

    case "$PROVIDER" in
        openai)
            # OpenAI Codex CLI
            # Uses: codex exec -m MODEL [-o OUTPUT_FILE] [PROMPT or - for stdin]
            if command -v codex &> /dev/null; then
                if [[ "$stream" == "true" ]]; then
                    # For streaming, we pipe through tee
                    echo "$prompt" | codex exec \
                        -m "$MODEL" \
                        - \
                        2>"$stderr_file" | tee "$output_file"
                    return ${PIPESTATUS[1]}
                else
                    # Non-streaming: capture output directly
                    echo "$prompt" | codex exec \
                        -m "$MODEL" \
                        - \
                        2>"$stderr_file" > "$output_file"
                    return $?
                fi
            else
                log_error "Codex CLI not found. Please install: npm install -g @openai/codex"
                return 127
            fi
            ;;
        anthropic)
            # Anthropic Claude CLI
            # Uses: claude --model MODEL --print (reads from stdin)
            if command -v claude &> /dev/null; then
                if [[ "$stream" == "true" ]]; then
                    echo "$prompt" | claude \
                        --model "$MODEL" \
                        --print \
                        2>"$stderr_file" | tee "$output_file"
                    return ${PIPESTATUS[1]}
                else
                    echo "$prompt" | claude \
                        --model "$MODEL" \
                        --print \
                        2>"$stderr_file" > "$output_file"
                    return $?
                fi
            else
                log_error "Claude CLI not found. Please install: npm install -g @anthropic-ai/claude-code"
                return 127
            fi
            ;;
    esac
}

if [[ "$DRY_RUN" == "false" ]]; then
    log_info "Provider: ${PROVIDER}"
    log_info "Model: ${MODEL}"
    log_info "Sending prompt..."

    if [[ "$TAIL_OUTPUT" == "true" ]]; then
        log_info "Streaming output (--tail mode):"
        echo -e "${DIM}────────────────────────────────────────────────────────────${NC}"
    fi

    AI_START=$(date +%s)

    set +e
    if [[ "$TAIL_OUTPUT" == "true" ]]; then
        # Stream output while also capturing it
        run_ai_command "$FULL_PROMPT" "$ASSISTANT_OUTPUT" "$AI_STDERR" "true"
        AI_EXIT_CODE=$?
    else
        # Capture output without streaming, but show progress
        log_ai "Working..."

        # Run in background and show spinner
        run_ai_command "$FULL_PROMPT" "$ASSISTANT_OUTPUT" "$AI_STDERR" "false" &
        AI_PID=$!

        # Show spinner while waiting
        SPIN_CHARS='⠋⠙⠹⠸⠼⠴⠦⠧⠇⠏'
        SPIN_IDX=0
        while kill -0 $AI_PID 2>/dev/null; do
            SPIN_CHAR="${SPIN_CHARS:$SPIN_IDX:1}"
            echo -ne "\r${DIM}[$(date '+%H:%M:%S')]${NC} ${GREEN}[AI]${NC} ${SPIN_CHAR} Generating theory...  "
            SPIN_IDX=$(( (SPIN_IDX + 1) % ${#SPIN_CHARS} ))
            sleep 0.1
        done
        wait $AI_PID
        AI_EXIT_CODE=$?
        echo -ne "\r"  # Clear spinner line
    fi
    set -e

    AI_END=$(date +%s)
    AI_DURATION=$((AI_END - AI_START))

    if [[ "$TAIL_OUTPUT" == "true" ]]; then
        echo -e "${DIM}────────────────────────────────────────────────────────────${NC}"
    fi

    if [[ $AI_EXIT_CODE -ne 0 ]]; then
        log_error "AI failed (exit code: ${AI_EXIT_CODE}) after ${AI_DURATION}s"
        if [[ -f "$AI_STDERR" ]] && [[ -s "$AI_STDERR" ]]; then
            log_error "Stderr: $(head -5 "$AI_STDERR")"
        fi
    else
        OUTPUT_SIZE=$(wc -c < "$ASSISTANT_OUTPUT" | tr -d ' ')
        log_success "AI completed in ${AI_DURATION}s (${OUTPUT_SIZE} bytes output)"
    fi
else
    log_info "[DRY-RUN] Would run ${PROVIDER}/${MODEL} with ${#FULL_PROMPT} char prompt"
    AI_EXIT_CODE=0
    AI_DURATION=0
fi

# ============================================================================
# STEP 4: Extract Code & Write Metadata
# ============================================================================
log_step "4/5 Extracting code and writing metadata..."

RUN_ENDED_AT="$(date -u +%Y-%m-%dT%H:%M:%SZ)"

# Write run metadata
RUN_JSON="${RUN_RESULTS_DIR}/run.json"
if [[ "$DRY_RUN" == "false" ]]; then
    # Export environment variables for write_run_metadata.py
    export RUN_PROMPT_ID="$PROMPT_ID"
    export RUN_PROMPT_PATH="$PROMPT_FILE"
    export RUN_PROMPT_USED="$COMBINED_PROMPT_FILE"
    export RUN_SKILLS="$SKILLS_STRING"
    export RUN_DISABLE_SKILLS="$( [[ "$DISABLE_SKILLS" == "true" ]] && echo "1" || echo "0" )"
    export RUN_SCHEMA_PATH="${SCHEMA_FILE:-}"
    export RUN_WORK_DIR="$WORK_DIR"
    export RUN_OUT_FILE="$OUT_FILE"
    export RUN_RESULTS_DIR="$RUN_RESULTS_DIR"
    export RUN_PROVIDER="$PROVIDER"
    export RUN_MODEL="$MODEL"
    export RUN_CODEX_EXIT="$AI_EXIT_CODE"
    export RUN_STARTED_AT="$RUN_STARTED_AT"
    export RUN_ENDED_AT="$RUN_ENDED_AT"
    export RUN_CODEX_JSONL="$AI_JSONL"
    export RUN_CODEX_STDERR="$AI_STDERR"
    export RUN_LAST_MESSAGE="$ASSISTANT_OUTPUT"
    export RUN_SESSION_NAME="$SESSION_NAME"

    if [[ -x "${SCRIPT_DIR}/write_run_metadata.py" ]]; then
        python3 "${SCRIPT_DIR}/write_run_metadata.py" "$RUN_JSON"
        log_verbose "Wrote run metadata via Python script"
    else
        # Fallback: write JSON directly
        SKILLS_JSON=$(printf '%s\n' "${SKILLS[@]}" 2>/dev/null | jq -R . | jq -s . 2>/dev/null || echo "[]")
        cat > "$RUN_JSON" <<EOF
{
  "prompt_id": "${PROMPT_ID}",
  "prompt_path": "${PROMPT_FILE}",
  "prompt_used": "${COMBINED_PROMPT_FILE}",
  "skills": ${SKILLS_JSON},
  "disable_skills": ${DISABLE_SKILLS},
  "schema_path": "${SCHEMA_FILE:-null}",
  "provider": "${PROVIDER}",
  "model": "${MODEL}",
  "session_name": "${SESSION_NAME}",
  "work_dir": "${WORK_DIR}",
  "out_file": "${OUT_FILE}",
  "results_dir": "${RUN_RESULTS_DIR}",
  "ai_exit_code": ${AI_EXIT_CODE},
  "duration_sec": ${AI_DURATION},
  "started_at": "${RUN_STARTED_AT}",
  "ended_at": "${RUN_ENDED_AT}"
}
EOF
    fi
    log_success "Wrote run.json"
fi

# Extract code from output
if [[ "$DRY_RUN" == "false" ]] && [[ -f "$ASSISTANT_OUTPUT" ]] && [[ -s "$ASSISTANT_OUTPUT" ]]; then
    log_info "Extracting theory code..."

    CODE_EXTRACTED=false

    # Method 1: Try JSON extraction with extract_code.py
    if [[ -n "$SCHEMA_FILE" ]] && [[ -x "${SCRIPT_DIR}/extract_code.py" ]]; then
        if python3 "${SCRIPT_DIR}/extract_code.py" "$ASSISTANT_OUTPUT" "$OUT_FILE" 2>/dev/null; then
            CODE_EXTRACTED=true
            log_success "Extracted code via extract_code.py"
        fi
    fi

    # Method 2: Try JSON extraction with jq
    if [[ "$CODE_EXTRACTED" == "false" ]] && head -1 "$ASSISTANT_OUTPUT" | grep -q '^{'; then
        if command -v jq &> /dev/null; then
            CODE_CONTENT=$(jq -r '.code // empty' "$ASSISTANT_OUTPUT" 2>/dev/null || true)
            if [[ -n "$CODE_CONTENT" ]] && [[ "$CODE_CONTENT" != "null" ]]; then
                echo "$CODE_CONTENT" > "$OUT_FILE"
                CODE_EXTRACTED=true
                log_success "Extracted code from JSON 'code' field"
            fi
        fi
    fi

    # Method 3: Extract from isabelle/theory code blocks
    if [[ "$CODE_EXTRACTED" == "false" ]]; then
        EXTRACTED=$(sed -n '/^```\(isabelle\|theory\|isar\)/,/^```$/p' "$ASSISTANT_OUTPUT" 2>/dev/null | sed '1d;$d' || true)
        if [[ -n "$EXTRACTED" ]]; then
            echo "$EXTRACTED" > "$OUT_FILE"
            CODE_EXTRACTED=true
            log_success "Extracted code from markdown code block"
        fi
    fi

    # Method 4: Look for theory ... end pattern
    if [[ "$CODE_EXTRACTED" == "false" ]]; then
        EXTRACTED=$(sed -n '/^theory /,/^end$/p' "$ASSISTANT_OUTPUT" 2>/dev/null || true)
        if [[ -n "$EXTRACTED" ]]; then
            echo "$EXTRACTED" > "$OUT_FILE"
            CODE_EXTRACTED=true
            log_success "Extracted code from theory...end pattern"
        fi
    fi

    if [[ "$CODE_EXTRACTED" == "false" ]]; then
        log_warn "Could not extract theory code from output"
        log_warn "Raw output saved to: ${ASSISTANT_OUTPUT}"
        # Copy raw output as theory file anyway
        cp "$ASSISTANT_OUTPUT" "$OUT_FILE"
    else
        THEORY_LINES=$(wc -l < "$OUT_FILE" | tr -d ' ')
        log_info "Theory file: ${OUT_FILE} (${THEORY_LINES} lines)"
    fi
elif [[ "$DRY_RUN" == "false" ]]; then
    log_warn "No output from Claude to extract"
fi

# ============================================================================
# STEP 5: Verify
# ============================================================================
if [[ "$NO_VERIFY" == "false" ]]; then
    log_step "5/5 Running Isabelle verification..."

    if [[ "$DRY_RUN" == "false" ]]; then
        if [[ -x "${SCRIPT_DIR}/verify.sh" ]]; then
            set +e
            "${SCRIPT_DIR}/verify.sh" "$WORK_DIR" "$RUN_RESULTS_DIR" "$SESSION_NAME"
            VERIFY_EXIT_CODE=$?
            set -e

            if [[ $VERIFY_EXIT_CODE -eq 0 ]]; then
                log_success "Verification PASSED"
            else
                log_error "Verification FAILED (exit code: ${VERIFY_EXIT_CODE})"
            fi
        else
            log_warn "verify.sh not found or not executable"
            VERIFY_EXIT_CODE=1
        fi
    else
        log_info "[DRY-RUN] Would run verify.sh"
        VERIFY_EXIT_CODE=0
    fi
else
    log_step "5/5 Verification... SKIPPED (--no-verify)"
    VERIFY_EXIT_CODE=0
fi

# ============================================================================
# Summary
# ============================================================================
echo ""
echo -e "${BOLD}╔════════════════════════════════════════════════════════════╗${NC}"
echo -e "${BOLD}║${NC}                      ${MAGENTA}Run Complete${NC}                          ${BOLD}║${NC}"
echo -e "${BOLD}╚════════════════════════════════════════════════════════════╝${NC}"
echo ""
log_info "Prompt: ${BOLD}${PROMPT_ID}${NC}"
log_info "Results: ${RUN_RESULTS_DIR}"
log_info "Theory: ${OUT_FILE}"

if [[ -f "${RUN_RESULTS_DIR}/verify.json" ]]; then
    VERIFY_STATUS=$(jq -r '.status // "unknown"' "${RUN_RESULTS_DIR}/verify.json" 2>/dev/null || echo "unknown")
    VERIFY_COUNTS=$(jq -r '"pass=\(.counts.pass // 0) fail=\(.counts.fail // 0) skip=\(.counts.skipped // 0)"' "${RUN_RESULTS_DIR}/verify.json" 2>/dev/null || echo "")

    if [[ "$VERIFY_STATUS" == "pass" ]]; then
        echo ""
        echo -e "  ${GREEN}${BOLD}✓ STATUS: PASS${NC}  ${DIM}(${VERIFY_COUNTS})${NC}"
    else
        echo ""
        echo -e "  ${RED}${BOLD}✗ STATUS: FAIL${NC}  ${DIM}(${VERIFY_COUNTS})${NC}"

        # Show failed steps
        FAILED_STEPS=$(jq -r '.failed_steps // [] | join(", ")' "${RUN_RESULTS_DIR}/verify.json" 2>/dev/null || echo "")
        if [[ -n "$FAILED_STEPS" ]]; then
            echo -e "  ${RED}Failed steps: ${FAILED_STEPS}${NC}"
        fi
    fi
fi

echo ""

# Exit with appropriate code
if [[ ${AI_EXIT_CODE:-0} -ne 0 ]]; then
    exit $AI_EXIT_CODE
elif [[ "$NO_VERIFY" == "false" ]] && [[ ${VERIFY_EXIT_CODE:-0} -ne 0 ]]; then
    exit 1
fi

exit 0
