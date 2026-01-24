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
        local dest_file="${LIB_DIR}/Lattice/${filename}"
        cp "$src_file" "$dest_file"

        # Patch for benchmarks/usability: export type constructors
        # Isabelle generates modules that hide constructors, making types opaque
        patch_haskell_exports "$dest_file"

        [[ "$VERBOSE" == "true" ]] && log_info "  Haskell: ${filename}"
        ((count++))
    done

    echo "$count"
}

# Patch Haskell module exports to include type constructors
# Isabelle generates abstract types (exports type but not constructor)
patch_haskell_exports() {
    local file="$1"
    [[ ! -f "$file" ]] && return

    # Use Python for reliable multi-line replacement
    python3 << PYTHON
import re

with open('$file', 'r') as f:
    content = f.read()

# Match module export list: module\n  Name(exports...\n  )\n  where
def add_constructors(match):
    exports = match.group(0)
    # Add (..) to type names to export constructors
    exports = re.sub(r'\bInt\b(?!_)', 'Int(..)', exports)
    exports = re.sub(r'\bNum\b', 'Num(..)', exports)
    exports = re.sub(r'\bLwe_ciphertext_ext\b', 'Lwe_ciphertext_ext(..)', exports)
    exports = re.sub(r'\bLwe_public_key_ext\b', 'Lwe_public_key_ext(..)', exports)
    exports = re.sub(r'\bLwe_secret_key_ext\b', 'Lwe_secret_key_ext(..)', exports)
    return exports

# Match from "module" to "where {"
content = re.sub(r'module\s+[\w.]+\([^)]+\)\s+where', add_constructors, content, flags=re.DOTALL)

with open('$file', 'w') as f:
    f.write(content)
PYTHON
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

    # Use lowercase 'lattice' for dune compatibility
    mkdir -p "${LIB_DIR}/lattice"

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
        local dest_file="${LIB_DIR}/lattice/${ml_filename}"
        cp "$src_file" "$dest_file"

        # Patch for js_of_ocaml: expose type constructors in module signature
        # Isabelle generates abstract types which prevents JS interop
        patch_ocaml_for_jsoo "$dest_file"

        [[ "$VERBOSE" == "true" ]] && log_info "  OCaml: ${ml_filename}"
        ((count++))
    done

    echo "$count"
}

# Patch OCaml module signatures to expose type constructors for js_of_ocaml
patch_ocaml_for_jsoo() {
    local file="$1"
    [[ ! -f "$file" ]] && return

    # Replace abstract type declarations with concrete ones
    # This is needed because js_of_ocaml bindings need to construct/deconstruct values
    sed -i.bak '
        # Expose int type constructor
        s/^  type int$/  type int = Int_of_integer of Z.t/
        # Expose num type constructors
        s/^  type num$/  type num = One | Bit0 of num | Bit1 of num/
        # Expose ciphertext type constructor
        s/^  type '"'"'a lwe_ciphertext_ext$/  type '"'"'a lwe_ciphertext_ext = Lwe_ciphertext_ext of int list * int * '"'"'a/
        # Expose public key type constructor
        s/^  type '"'"'a lwe_public_key_ext$/  type '"'"'a lwe_public_key_ext = Lwe_public_key_ext of (int list) list * int list * '"'"'a/
        # Expose secret key type constructor
        s/^  type '"'"'a lwe_secret_key_ext$/  type '"'"'a lwe_secret_key_ext = Lwe_secret_key_ext of int list * '"'"'a/
    ' "$file"
    rm -f "${file}.bak"
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
