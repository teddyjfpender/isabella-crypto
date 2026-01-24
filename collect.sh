#!/usr/bin/env bash
#
# collect.sh - Collect generated code from Isabelle into language-specific libraries
#
# This script finds all code generated from Isabelle theories and copies them
# into the appropriate language library structures.
#
# Usage:
#   ./collect.sh [--verbose] [--lang <language>]
#
# Languages: haskell (default), sml, ocaml, scala, all
#
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="${SCRIPT_DIR}"
WORK_DIR="${PROJECT_ROOT}/eval/work"

# Colors
GREEN='\033[0;32m'
BLUE='\033[0;34m'
YELLOW='\033[1;33m'
NC='\033[0m'

VERBOSE=false
LANG="haskell"

# Parse args
while [[ $# -gt 0 ]]; do
    case $1 in
        --verbose) VERBOSE=true; shift ;;
        --lang) LANG="$2"; shift 2 ;;
        *) shift ;;
    esac
done

log_info() { echo -e "${BLUE}[INFO]${NC} $1"; }
log_success() { echo -e "${GREEN}[OK]${NC} $1"; }
log_warn() { echo -e "${YELLOW}[WARN]${NC} $1"; }

collect_haskell() {
    local LIB_DIR="${PROJECT_ROOT}/haskell/isabella/src"
    local PATTERN="*/generated/code/*/Lattice/*.hs"

    mkdir -p "${LIB_DIR}/Lattice"

    local count=0
    for src_file in $(find "$WORK_DIR" -path "$PATTERN" -type f 2>/dev/null); do
        filename=$(basename "$src_file")
        cp "$src_file" "${LIB_DIR}/Lattice/${filename}"
        [[ "$VERBOSE" == "true" ]] && log_info "  Haskell: ${filename}"
        ((count++))
    done

    echo "$count"
}

collect_sml() {
    local LIB_DIR="${PROJECT_ROOT}/sml/isabella/src"

    mkdir -p "${LIB_DIR}/Lattice"

    local count=0
    # SML files are exported directly in code/ directory
    for src_file in $(find "$WORK_DIR" -path "*/generated/code/*.ML" -type f 2>/dev/null); do
        # Extract module name from "structure NAME : sig"
        module_name=$(head -1 "$src_file" | sed -n 's/^structure \([^ ]*\) .*/\1/p')
        if [[ -z "$module_name" ]]; then
            module_name=$(basename "$src_file" .ML)
        fi
        cp "$src_file" "${LIB_DIR}/Lattice/${module_name}.ML"
        [[ "$VERBOSE" == "true" ]] && log_info "  SML: ${module_name}.ML"
        ((count++))
    done

    echo "$count"
}

collect_ocaml() {
    local LIB_DIR="${PROJECT_ROOT}/ocaml/isabella/src"

    mkdir -p "${LIB_DIR}/Lattice"

    local count=0
    # Isabelle exports OCaml files with .ocaml extension, directly in code/ directory
    for src_file in $(find "$WORK_DIR" -path "*/generated/code/*.ocaml" -type f 2>/dev/null); do
        # Extract module name from "module NAME : sig"
        module_name=$(head -1 "$src_file" | sed -n 's/^module \([^ ]*\) .*/\1/p')
        if [[ -z "$module_name" ]]; then
            module_name=$(basename "$src_file" .ocaml)
        fi
        # OCaml module files should be lowercase
        ml_filename=$(echo "$module_name" | tr '[:upper:]' '[:lower:]').ml
        cp "$src_file" "${LIB_DIR}/Lattice/${ml_filename}"
        [[ "$VERBOSE" == "true" ]] && log_info "  OCaml: ${ml_filename}"
        ((count++))
    done

    echo "$count"
}

collect_scala() {
    local LIB_DIR="${PROJECT_ROOT}/scala/isabella/src"

    mkdir -p "${LIB_DIR}/Lattice"

    local count=0
    # Scala files are exported directly in code/ directory
    for src_file in $(find "$WORK_DIR" -path "*/generated/code/*.scala" -type f 2>/dev/null); do
        # Extract object name from "object NAME {"
        module_name=$(head -1 "$src_file" | sed -n 's/^object \([^ ]*\) .*/\1/p')
        if [[ -z "$module_name" ]]; then
            module_name=$(basename "$src_file" .scala)
        fi
        cp "$src_file" "${LIB_DIR}/Lattice/${module_name}.scala"
        [[ "$VERBOSE" == "true" ]] && log_info "  Scala: ${module_name}.scala"
        ((count++))
    done

    echo "$count"
}

echo ""
echo -e "${GREEN}Isabella - Collecting Verified Code${NC}"
echo "====================================="
echo ""

case "$LANG" in
    haskell)
        count=$(collect_haskell)
        log_success "Collected ${count} Haskell module(s)"
        ;;
    sml)
        count=$(collect_sml)
        log_success "Collected ${count} SML module(s)"
        ;;
    ocaml)
        count=$(collect_ocaml)
        log_success "Collected ${count} OCaml module(s)"
        ;;
    scala)
        count=$(collect_scala)
        log_success "Collected ${count} Scala module(s)"
        ;;
    all)
        hs=$(collect_haskell)
        sml=$(collect_sml)
        ml=$(collect_ocaml)
        sc=$(collect_scala)
        log_success "Collected: Haskell(${hs}) SML(${sml}) OCaml(${ml}) Scala(${sc})"
        ;;
    *)
        log_warn "Unknown language: $LANG"
        log_info "Supported: haskell, sml, ocaml, scala, all"
        exit 1
        ;;
esac

echo ""
