#!/usr/bin/env bash
#
# collect.sh - Collect generated Haskell code into the isabella library
#
# This script finds all Haskell files generated from Isabelle theories
# and copies them into the isabella library structure.
#
# Usage:
#   ./collect.sh [--verbose]
#
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"
WORK_DIR="${PROJECT_ROOT}/eval/work"
LIB_DIR="${SCRIPT_DIR}/isabella/src"

# Colors
GREEN='\033[0;32m'
BLUE='\033[0;34m'
YELLOW='\033[1;33m'
NC='\033[0m'

VERBOSE=false
[[ "${1:-}" == "--verbose" ]] && VERBOSE=true

log_info() {
    echo -e "${BLUE}[INFO]${NC} $1"
}

log_success() {
    echo -e "${GREEN}[OK]${NC} $1"
}

log_warn() {
    echo -e "${YELLOW}[WARN]${NC} $1"
}

echo ""
echo -e "${GREEN}Isabella - Collecting Verified Haskell Code${NC}"
echo "============================================="
echo ""

# Find all generated Haskell files
GENERATED_FILES=$(find "$WORK_DIR" -path "*/generated/code/*/Lattice/*.hs" -type f 2>/dev/null || true)

if [[ -z "$GENERATED_FILES" ]]; then
    log_warn "No generated Haskell files found in ${WORK_DIR}"
    log_info "Run ralph/isabella-loop.sh to generate verified code first"
    exit 1
fi

# Ensure target directory exists
mkdir -p "${LIB_DIR}/Lattice"

# Copy each file
COUNT=0
for src_file in $GENERATED_FILES; do
    filename=$(basename "$src_file")
    dest_file="${LIB_DIR}/Lattice/${filename}"

    # Get source prompt for logging
    prompt_dir=$(echo "$src_file" | sed 's|.*/eval/work/\([^/]*\)/.*|\1|')

    if [[ "$VERBOSE" == "true" ]]; then
        log_info "Copying from ${prompt_dir}: ${filename}"
    fi

    cp "$src_file" "$dest_file"
    ((COUNT++))
done

log_success "Collected ${COUNT} verified Haskell module(s)"
echo ""

# List collected modules
log_info "Modules in isabella library:"
for f in "${LIB_DIR}"/Lattice/*.hs; do
    if [[ -f "$f" ]]; then
        modname=$(basename "$f" .hs)
        lines=$(wc -l < "$f" | tr -d ' ')
        echo "  - Lattice.${modname} (${lines} lines)"
    fi
done

echo ""
log_info "Library location: ${SCRIPT_DIR}/isabella/"
log_info "To build: cd ${SCRIPT_DIR}/isabella && cabal build"
echo ""
