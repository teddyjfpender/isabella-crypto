#!/bin/bash
#
# generate.sh - Verify/export Canon code and build language libraries
#
# This script is intentionally fail-fast and does NOT synthesize handwritten
# fallback stubs. It only accepts artifacts from Isabelle export plus committed
# generated wrappers in language directories.
#
# Usage:
#   ./generate.sh                  # Build Isabelle sessions, verify exports, build libs
#   ./generate.sh --build-only     # Skip Isabelle, verify existing artifacts, build libs
#   ./generate.sh --lang haskell   # Only Haskell verification/build
#   ./generate.sh --lang ocaml     # Only OCaml verification/build
#   ./generate.sh --run-examples   # Run CLI examples after build
#   ./generate.sh --clean          # Remove build artifacts only

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
CANON_DIR="$SCRIPT_DIR/Canon"
HS_DIR="$SCRIPT_DIR/isabella.hs"
ML_DIR="$SCRIPT_DIR/isabella.ml"

# Colors
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m'

# Options
BUILD_ONLY=false
RUN_EXAMPLES=false
LANG="all"
CLEAN=false
VERBOSE=false

usage() {
    cat <<USAGE
Usage: $0 [OPTIONS]

Options:
  --build-only      Skip Isabelle build/export checks, just verify + compile libraries
  --run-examples    Run examples after building
  --lang LANG       Build specific language (haskell, ocaml, all)
  --clean           Clean build artifacts only
  --verbose         Show detailed output
  -h, --help        Show this help
USAGE
}

log() { echo -e "${BLUE}[generate]${NC} $1"; }
success() { echo -e "${GREEN}[generate]${NC} $1"; }
warn() { echo -e "${YELLOW}[generate]${NC} $1"; }
error() { echo -e "${RED}[generate]${NC} $1"; exit 1; }

while [[ $# -gt 0 ]]; do
    case "$1" in
        --build-only)
            BUILD_ONLY=true
            shift
            ;;
        --run-examples)
            RUN_EXAMPLES=true
            shift
            ;;
        --lang)
            LANG="$2"
            shift 2
            ;;
        --clean)
            CLEAN=true
            shift
            ;;
        --verbose)
            VERBOSE=true
            shift
            ;;
        -h|--help)
            usage
            exit 0
            ;;
        *)
            error "Unknown option: $1"
            ;;
    esac
done

if [[ "$LANG" != "all" && "$LANG" != "haskell" && "$LANG" != "ocaml" ]]; then
    error "Invalid --lang value '$LANG' (expected haskell|ocaml|all)"
fi

clean_artifacts() {
    log "Cleaning build artifacts (preserving generated source files)..."
    rm -rf "$HS_DIR/dist-newstyle"
    rm -rf "$ML_DIR/_build"
    success "Cleaned build artifacts"
}

if $CLEAN; then
    clean_artifacts
    exit 0
fi

require_cmd() {
    command -v "$1" >/dev/null 2>&1 || error "Required command not found: $1"
}

build_isabelle() {
    log "Building Isabelle sessions and validating export availability..."
    require_cmd isabelle

    cd "$SCRIPT_DIR"
    if $VERBOSE; then
        isabelle build -D Canon -v
        isabelle build -e -D Canon -v
    else
        isabelle build -D Canon
        isabelle build -e -D Canon
    fi

    local sessions=(Canon_Base Canon_Hardness Canon_Gadgets Canon_Rings Canon_Crypto Canon_ZK)
    for session in "${sessions[@]}"; do
        if ! isabelle export -d "$CANON_DIR" -n -l "$session" | rg -q "code/export"; then
            error "No code exports found for session $session. Refusing to continue."
        fi
    done

    success "Isabelle build/export checks passed"
}

verify_files_exist() {
    local root="$1"
    shift
    local missing=0
    for rel in "$@"; do
        if [[ ! -f "$root/$rel" ]]; then
            echo "  missing: $root/$rel"
            missing=1
        fi
    done
    if [[ $missing -ne 0 ]]; then
        return 1
    fi
    return 0
}

verify_haskell_surface() {
    log "Verifying Haskell export surface..."
    local required=(
        "src/Canon/Algebra/Zq.hs"
        "src/Canon/Linear/ListVec.hs"
        "src/Canon/Analysis/Norms.hs"
        "src/Canon/Hardness/LWE_Def.hs"
        "src/Canon/Hardness/SIS_Def.hs"
        "src/Canon/Gadgets/Decomp.hs"
        "src/Canon/Rings/PolyMod.hs"
        "src/Canon/Rings/ModuleLWE.hs"
        "src/Canon/Rings/NTT.hs"
        "src/Canon/Crypto/Regev_PKE.hs"
        "src/Canon/Crypto/Commit_SIS.hs"
        "src/Canon/Crypto/Kyber.hs"
        "src/Canon/Crypto/Dilithium.hs"
        "src/Canon.hs"
    )

    if ! verify_files_exist "$HS_DIR" "${required[@]}"; then
        error "Haskell surface incomplete. Run Isabelle exports and commit generated files."
    fi

    if rg -n "legacy stub fallback|Created Haskell modules" "$HS_DIR/src" >/dev/null 2>&1; then
        error "Detected legacy stub markers in Haskell sources. Refusing to continue."
    fi

    success "Haskell export surface verified"
}

verify_ocaml_surface() {
    log "Verifying OCaml export surface..."
    local required=(
        "src/canon/zq.ml"
        "src/canon/listvec.ml"
        "src/canon/norms.ml"
        "src/canon/lwe_def.ml"
        "src/canon/sis_def.ml"
        "src/canon/decomp.ml"
        "src/canon/polymod.ml"
        "src/canon/modulelwe.ml"
        "src/canon/ntt.ml"
        "src/canon/regev_pke.ml"
        "src/canon/commit_sis.ml"
        "src/canon/kyber.ml"
        "src/canon/dilithium.ml"
        "src/canon/canon.ml"
    )

    if ! verify_files_exist "$ML_DIR" "${required[@]}"; then
        error "OCaml surface incomplete. Refusing to continue."
    fi

    if rg -n "legacy stub fallback|Created OCaml modules" "$ML_DIR/src" >/dev/null 2>&1; then
        error "Detected legacy stub markers in OCaml sources. Refusing to continue."
    fi

    success "OCaml export surface verified"
}

build_haskell() {
    if [[ "$LANG" != "all" && "$LANG" != "haskell" ]]; then
        return
    fi

    verify_haskell_surface

    log "Building Haskell library..."
    if ! command -v cabal >/dev/null 2>&1; then
        warn "cabal not found, skipping Haskell build"
        return
    fi
    cd "$HS_DIR"
    cabal build all
    success "Haskell library built"
}

build_ocaml() {
    if [[ "$LANG" != "all" && "$LANG" != "ocaml" ]]; then
        return
    fi

    verify_ocaml_surface

    log "Building OCaml library..."
    if ! command -v dune >/dev/null 2>&1; then
        warn "dune not found, skipping OCaml build"
        return
    fi
    cd "$ML_DIR"
    dune build
    success "OCaml library built"
}

run_haskell_examples() {
    log "Running Haskell examples..."
    cd "$HS_DIR"
    cabal run isabella-cli -- examples
}

run_ocaml_examples() {
    log "Running OCaml examples..."
    cd "$ML_DIR"
    dune exec isabella_cli -- examples
}

run_examples() {
    if [[ "$LANG" == "all" || "$LANG" == "haskell" ]]; then
        run_haskell_examples
    fi
    if [[ "$LANG" == "all" || "$LANG" == "ocaml" ]]; then
        run_ocaml_examples
    fi
}

main() {
    log "Isabella Code Generator"
    log "======================"
    echo ""

    if ! $BUILD_ONLY; then
        build_isabelle
    fi

    build_haskell
    build_ocaml

    if $RUN_EXAMPLES; then
        run_examples
    fi

    echo ""
    success "Generation complete!"
    echo ""
    log "Libraries available at:"
    echo "  Haskell: $HS_DIR"
    echo "  OCaml:   $ML_DIR"
}

main
