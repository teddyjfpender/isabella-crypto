#!/usr/bin/env bash
#
# scaffold.sh - Create/initialize an Isabelle HOL project structure
#
# Creates the necessary files and directories for an Isabelle session:
#   - ROOT file with session configuration
#   - Basic theory file template
#   - document/ directory for LaTeX output
#
# Usage:
#   ./scaffold.sh --work-dir <dir> [options]
#
# Options:
#   --work-dir <dir>      Working directory for the project (required)
#   --session <name>      Session name (default: CryptoProofs)
#   --theory <name>       Main theory file name (default: same as session)
#   --parent <session>    Parent session (default: HOL)
#   --template <file>     Template theory file to use
#   --no-document         Skip document directory setup
#   --force               Overwrite existing files
#   --verbose             Enable verbose output
#
set -euo pipefail

# Script directory
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

# Default values
WORK_DIR=""
SESSION_NAME="CryptoProofs"
THEORY_NAME=""
PARENT_SESSION="HOL"
TEMPLATE_FILE=""
NO_DOCUMENT=false
FORCE=false
VERBOSE=false

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
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

log_verbose() {
    if [[ "$VERBOSE" == "true" ]]; then
        echo -e "${BLUE}[DEBUG]${NC} $1"
    fi
}

usage() {
    cat <<EOF
Usage: $(basename "$0") --work-dir <dir> [options]

Options:
  --work-dir <dir>      Working directory for the project (required)
  --session <name>      Session name (default: CryptoProofs)
  --theory <name>       Main theory file name (default: same as session)
  --parent <session>    Parent session (default: HOL)
  --template <file>     Template theory file to use
  --no-document         Skip document directory setup
  --force               Overwrite existing files
  --verbose             Enable verbose output
  -h, --help            Show this help message

Example:
  $(basename "$0") --work-dir ./work/lattice --session LatticeCrypto
  $(basename "$0") --work-dir ./work/ring --session RingSignatures --parent HOL-Algebra
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
        --theory)
            THEORY_NAME="$2"
            shift 2
            ;;
        --parent)
            PARENT_SESSION="$2"
            shift 2
            ;;
        --template)
            TEMPLATE_FILE="$2"
            shift 2
            ;;
        --no-document)
            NO_DOCUMENT=true
            shift
            ;;
        --force)
            FORCE=true
            shift
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
            usage
            ;;
    esac
done

# Validate required arguments
if [[ -z "$WORK_DIR" ]]; then
    log_error "Missing required argument: --work-dir"
    usage
fi

# Default theory name to session name
if [[ -z "$THEORY_NAME" ]]; then
    THEORY_NAME="$SESSION_NAME"
fi

log_info "Scaffolding Isabelle project: ${SESSION_NAME}"
log_verbose "Work directory: ${WORK_DIR}"
log_verbose "Session name: ${SESSION_NAME}"
log_verbose "Theory name: ${THEORY_NAME}"
log_verbose "Parent session: ${PARENT_SESSION}"

# Create work directory
mkdir -p "$WORK_DIR"

# Create ROOT file
ROOT_FILE="${WORK_DIR}/ROOT"
if [[ -f "$ROOT_FILE" ]] && [[ "$FORCE" == "false" ]]; then
    log_warn "ROOT file already exists, skipping (use --force to overwrite)"
else
    log_info "Creating ROOT file..."
    cat > "$ROOT_FILE" <<EOF
session "${SESSION_NAME}" = "${PARENT_SESSION}" +
  options [document = false, timeout = 600]
  sessions
    "HOL-Library"
  theories
    ${THEORY_NAME}
  export_files (in "generated") [1]
    "*:**.hs"
    "*:**.ML"
    "*:**.ocaml"
    "*:**.scala"
EOF
    log_success "Created ROOT file: ${ROOT_FILE}"
fi

# Create main theory file
THEORY_FILE="${WORK_DIR}/${THEORY_NAME}.thy"
if [[ -f "$THEORY_FILE" ]] && [[ "$FORCE" == "false" ]]; then
    log_warn "Theory file already exists, skipping (use --force to overwrite)"
elif [[ -n "$TEMPLATE_FILE" ]] && [[ -f "$TEMPLATE_FILE" ]]; then
    log_info "Creating theory file from template..."
    cp "$TEMPLATE_FILE" "$THEORY_FILE"
    log_success "Created theory file from template: ${THEORY_FILE}"
else
    log_info "Creating theory file template..."
    cat > "$THEORY_FILE" <<EOF
theory ${THEORY_NAME}
  imports Main "HOL-Library.Code_Target_Numeral"
begin

(* Placeholder - will be replaced by AI-generated code *)

end
EOF
    log_success "Created theory file: ${THEORY_FILE}"
fi

# Create document directory (only if explicitly requested)
if [[ "$NO_DOCUMENT" == "false" ]] && [[ -n "${CREATE_DOCUMENT:-}" ]]; then
    DOC_DIR="${WORK_DIR}/document"
    mkdir -p "$DOC_DIR"
    log_verbose "Created document directory (disabled by default)"
fi

# Create output directories
mkdir -p "${WORK_DIR}/output"
log_verbose "Created output directory"

# Note: ensure_root_file.py is no longer needed since we generate a clean ROOT file
# The generated ROOT is already properly configured for evaluation

# Create .gitignore
GITIGNORE="${WORK_DIR}/.gitignore"
if [[ ! -f "$GITIGNORE" ]]; then
    cat > "$GITIGNORE" <<EOF
# Isabelle generated files
output/
.session/
*.log
*~

# Heap images
*.heap

# Browser info
browser_info/
EOF
    log_verbose "Created .gitignore"
fi

# Summary
log_info "========================================="
log_success "Isabelle project scaffolded successfully"
log_info "========================================="
log_info "Directory: ${WORK_DIR}"
log_info "Session: ${SESSION_NAME}"
log_info "Theory: ${THEORY_NAME}.thy"
log_info ""
log_info "Next steps:"
log_info "  1. Edit ${THEORY_NAME}.thy with your proofs"
log_info "  2. Run: isabelle build -d ${WORK_DIR} ${SESSION_NAME}"
log_info "========================================="

exit 0
