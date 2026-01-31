#!/usr/bin/env bash
#
# local-ci.sh - Local CI validation script for Isabella
#
# This script mimics the GitHub Actions CI workflow to give engineers
# a quick heuristic of what CI will likely output before they push.
#
# Usage:
#   ./scripts/local-ci.sh           # Run all checks
#   ./scripts/local-ci.sh --quick   # Skip Isabelle (fast mode)
#   ./scripts/local-ci.sh --canon   # Only run Isabelle Canon build
#   ./scripts/local-ci.sh --ocaml   # Only run OCaml build
#   ./scripts/local-ci.sh --tests   # Only run cross-validation tests
#

set -e

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

# Timing
SECONDS=0

# Script directory
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(dirname "$SCRIPT_DIR")"

# Results tracking (bash 3.x compatible)
RESULTS_NAMES=""
RESULTS_VALUES=""
RESULTS_TIMES=""
RESULT_COUNT=0

# Parse arguments
RUN_CANON=true
RUN_HASKELL=true
RUN_OCAML=true
RUN_TYPESCRIPT=true
RUN_TESTS=true
VERBOSE=false

while [[ $# -gt 0 ]]; do
    case $1 in
        --quick)
            RUN_CANON=false
            RUN_HASKELL=false
            RUN_TYPESCRIPT=false
            shift
            ;;
        --canon)
            RUN_CANON=true
            RUN_HASKELL=false
            RUN_OCAML=false
            RUN_TYPESCRIPT=false
            RUN_TESTS=false
            shift
            ;;
        --ocaml)
            RUN_CANON=false
            RUN_HASKELL=false
            RUN_OCAML=true
            RUN_TYPESCRIPT=false
            RUN_TESTS=false
            shift
            ;;
        --haskell)
            RUN_CANON=false
            RUN_HASKELL=true
            RUN_OCAML=false
            RUN_TYPESCRIPT=false
            RUN_TESTS=false
            shift
            ;;
        --tests)
            RUN_CANON=false
            RUN_HASKELL=false
            RUN_OCAML=true  # Tests need OCaml CLI
            RUN_TYPESCRIPT=false
            RUN_TESTS=true
            shift
            ;;
        --verbose|-v)
            VERBOSE=true
            shift
            ;;
        --help|-h)
            echo "Usage: $0 [OPTIONS]"
            echo ""
            echo "Options:"
            echo "  --quick      Skip Isabelle, Haskell, TypeScript (fast mode)"
            echo "  --canon      Only run Isabelle Canon build"
            echo "  --ocaml      Only run OCaml build"
            echo "  --haskell    Only run Haskell build"
            echo "  --tests      Only run OCaml build + cross-validation tests"
            echo "  --verbose    Show full output from commands"
            echo "  --help       Show this help"
            exit 0
            ;;
        *)
            echo "Unknown option: $1"
            exit 1
            ;;
    esac
done

# Helper functions
print_header() {
    echo ""
    echo -e "${BLUE}═══════════════════════════════════════════════════════════════${NC}"
    echo -e "${BLUE}  $1${NC}"
    echo -e "${BLUE}═══════════════════════════════════════════════════════════════${NC}"
}

print_step() {
    echo -e "${YELLOW}→${NC} $1"
}

print_success() {
    echo -e "${GREEN}✓${NC} $1"
}

print_failure() {
    echo -e "${RED}✗${NC} $1"
}

print_skip() {
    echo -e "${YELLOW}○${NC} $1 (skipped)"
}

# Store result (bash 3.x compatible)
store_result() {
    local name="$1"
    local value="$2"
    local duration="$3"

    RESULTS_NAMES="${RESULTS_NAMES}${name}|"
    RESULTS_VALUES="${RESULTS_VALUES}${value}|"
    RESULTS_TIMES="${RESULTS_TIMES}${duration}|"
    ((RESULT_COUNT++)) || true
}

# Get last result
get_last_result() {
    echo "$RESULTS_VALUES" | awk -F'|' "{print \$(NF-1)}"
}

run_step() {
    local name="$1"
    local cmd="$2"
    local start_time=$SECONDS
    local result="pass"

    print_step "$name"

    set +e
    if $VERBOSE; then
        if eval "$cmd"; then
            result="pass"
        else
            result="fail"
        fi
    else
        if eval "$cmd" > /tmp/local-ci-output.log 2>&1; then
            result="pass"
        else
            result="fail"
            echo -e "${RED}  Output (last 20 lines):${NC}"
            tail -20 /tmp/local-ci-output.log | sed 's/^/    /'
        fi
    fi
    set -e

    local duration=$((SECONDS - start_time))
    store_result "$name" "$result" "$duration"

    if [[ "$result" == "pass" ]]; then
        print_success "$name (${duration}s)"
    else
        print_failure "$name (${duration}s)"
    fi

    # Export for checking in subsequent steps
    export LAST_RESULT="$result"
}

# Check for required tools
check_prerequisites() {
    print_header "Checking Prerequisites"

    local missing=""

    if $RUN_CANON; then
        if ! command -v isabelle &> /dev/null; then
            missing="${missing}isabelle "
        fi
    fi

    if $RUN_HASKELL; then
        if ! command -v cabal &> /dev/null; then
            missing="${missing}cabal "
        fi
        if ! command -v ghc &> /dev/null; then
            missing="${missing}ghc "
        fi
    fi

    if $RUN_OCAML || $RUN_TESTS; then
        if ! command -v opam &> /dev/null; then
            missing="${missing}opam "
        fi
        if ! command -v dune &> /dev/null; then
            # Try with opam env
            if ! eval "$(opam env 2>/dev/null)" || ! command -v dune &> /dev/null; then
                missing="${missing}dune "
            fi
        fi
    fi

    if $RUN_TESTS; then
        if ! command -v node &> /dev/null; then
            missing="${missing}node "
        fi
        if ! command -v npm &> /dev/null; then
            missing="${missing}npm "
        fi
    fi

    if [[ -n "$missing" ]]; then
        print_failure "Missing required tools: $missing"
        echo "  Please install them before running this script."
        exit 1
    fi

    print_success "All required tools found"
}

# Detect what changed
detect_changes() {
    print_header "Detecting Changes"

    # Get the base branch (usually main)
    local base_branch="main"

    # Check if we're on a branch that tracks a remote
    if git rev-parse --abbrev-ref --symbolic-full-name @{u} &>/dev/null; then
        base_branch=$(git merge-base HEAD origin/main 2>/dev/null || echo "HEAD~1")
    fi

    # Check for Canon changes
    if git diff --name-only "$base_branch" HEAD 2>/dev/null | grep -q "^Canon/"; then
        echo -e "  ${YELLOW}Canon/${NC} files changed - Isabelle build recommended"
        export CANON_CHANGED=true
    else
        echo "  Canon/ files unchanged"
        export CANON_CHANGED=false
    fi

    # Check for Haskell changes
    if git diff --name-only "$base_branch" HEAD 2>/dev/null | grep -q "^isabella.hs/"; then
        echo -e "  ${YELLOW}isabella.hs/${NC} files changed - Haskell build recommended"
    else
        echo "  isabella.hs/ files unchanged"
    fi

    # Check for OCaml changes
    if git diff --name-only "$base_branch" HEAD 2>/dev/null | grep -q "^isabella.ml/"; then
        echo -e "  ${YELLOW}isabella.ml/${NC} files changed - OCaml build recommended"
    else
        echo "  isabella.ml/ files unchanged"
    fi

    # Check for test changes
    if git diff --name-only "$base_branch" HEAD 2>/dev/null | grep -q "^tests/"; then
        echo -e "  ${YELLOW}tests/${NC} files changed - Tests recommended"
    else
        echo "  tests/ files unchanged"
    fi
}

# Isabelle Canon build
run_isabelle() {
    if ! $RUN_CANON; then
        print_skip "Isabelle Canon"
        return
    fi

    print_header "Isabelle Canon Build"

    cd "$PROJECT_ROOT/Canon"

    run_step "Build Canon theories" "isabelle build -v -D ."

    if [[ "$LAST_RESULT" == "pass" ]]; then
        run_step "Export code" "isabelle build -e -D . || true"
    fi

    cd "$PROJECT_ROOT"
}

# Haskell build
run_haskell() {
    if ! $RUN_HASKELL; then
        print_skip "Haskell Library"
        return
    fi

    print_header "Haskell Library Build"

    cd "$PROJECT_ROOT/isabella.hs"

    run_step "Cabal update" "cabal update"
    run_step "Build Haskell" "cabal build all"

    if [[ "$LAST_RESULT" == "pass" ]]; then
        run_step "Run Haskell tests" "cabal test all || true"
        run_step "Run CLI examples" "cabal run isabella-cli -- examples"
    fi

    cd "$PROJECT_ROOT"
}

# OCaml build
run_ocaml() {
    if ! $RUN_OCAML; then
        print_skip "OCaml Library"
        return
    fi

    print_header "OCaml Library Build"

    cd "$PROJECT_ROOT/isabella.ml"

    # Ensure opam environment is set up
    eval "$(opam env 2>/dev/null)" || true

    run_step "Build OCaml" "dune build"

    if [[ "$LAST_RESULT" == "pass" ]]; then
        run_step "Run CLI examples" "dune exec isabella_cli -- examples"
        export OCAML_BUILD_OK=true
    else
        export OCAML_BUILD_OK=false
    fi

    cd "$PROJECT_ROOT"
}

# TypeScript build
run_typescript() {
    if ! $RUN_TYPESCRIPT; then
        print_skip "TypeScript Library"
        return
    fi

    print_header "TypeScript Library Build"

    cd "$PROJECT_ROOT/isabella.ml"
    eval "$(opam env 2>/dev/null)" || true

    run_step "Build JavaScript (js_of_ocaml)" "dune build src/js/isabella_js.bc.js"

    if [[ "$LAST_RESULT" == "pass" ]]; then
        cd "$PROJECT_ROOT"
        mkdir -p isabella.ts/src
        cp isabella.ml/_build/default/src/js/isabella_js.bc.js isabella.ts/src/isabella.js 2>/dev/null || true

        cd "$PROJECT_ROOT/isabella.ts"
        run_step "Install TypeScript deps" "npm install"
        run_step "Build TypeScript" "npm run build || true"
    fi

    cd "$PROJECT_ROOT"
}

# Cross-validation tests
run_tests() {
    if ! $RUN_TESTS; then
        print_skip "Cross-Validation Tests"
        return
    fi

    # Tests require OCaml CLI
    if [[ "${OCAML_BUILD_OK:-false}" != "true" ]] && $RUN_OCAML; then
        print_failure "Skipping tests - OCaml build failed"
        return
    fi

    print_header "Cross-Validation Tests"

    cd "$PROJECT_ROOT/tests"

    # Ensure opam environment is set up for dune exec
    eval "$(opam env 2>/dev/null)" || true

    run_step "Install test dependencies" "npm ci 2>/dev/null || npm install"

    if [[ "$LAST_RESULT" == "pass" ]]; then
        run_step "Run cross-validation tests" "npm test"
    fi

    cd "$PROJECT_ROOT"
}

# Print summary
print_summary() {
    print_header "Summary"

    local passed=0
    local failed=0

    # Parse results (bash 3.x compatible)
    IFS='|' read -ra names <<< "$RESULTS_NAMES"
    IFS='|' read -ra values <<< "$RESULTS_VALUES"
    IFS='|' read -ra times <<< "$RESULTS_TIMES"

    for i in "${!names[@]}"; do
        if [[ -n "${names[$i]}" ]]; then
            if [[ "${values[$i]}" == "pass" ]]; then
                ((passed++)) || true
                echo -e "  ${GREEN}✓${NC} ${names[$i]} (${times[$i]}s)"
            else
                ((failed++)) || true
                echo -e "  ${RED}✗${NC} ${names[$i]} (${times[$i]}s)"
            fi
        fi
    done

    echo ""
    local total_time=$SECONDS
    local mins=$((total_time / 60))
    local secs=$((total_time % 60))

    if [[ $failed -eq 0 ]]; then
        echo -e "${GREEN}═══════════════════════════════════════════════════════════════${NC}"
        echo -e "${GREEN}  All $passed checks passed! (${mins}m ${secs}s)${NC}"
        echo -e "${GREEN}  CI is likely to pass. Safe to push.${NC}"
        echo -e "${GREEN}═══════════════════════════════════════════════════════════════${NC}"
        return 0
    else
        echo -e "${RED}═══════════════════════════════════════════════════════════════${NC}"
        echo -e "${RED}  $failed of $((passed + failed)) checks failed (${mins}m ${secs}s)${NC}"
        echo -e "${RED}  CI is likely to fail. Fix issues before pushing.${NC}"
        echo -e "${RED}═══════════════════════════════════════════════════════════════${NC}"
        return 1
    fi
}

# Main
main() {
    echo -e "${BLUE}"
    echo "  ╦╔═╗╔═╗╔╗ ╔═╗╦  ╦  ╔═╗  ╦  ╔═╗╔═╗╔═╗╦    ╔═╗╦"
    echo "  ║╚═╗╠═╣╠╩╗║╣ ║  ║  ╠═╣  ║  ║ ║║  ╠═╣║    ║  ║"
    echo "  ╩╚═╝╩ ╩╚═╝╚═╝╩═╝╩═╝╩ ╩  ╩═╝╚═╝╚═╝╩ ╩╩═╝  ╚═╝╩"
    echo -e "${NC}"
    echo "  Local CI Validation Script"
    echo ""

    cd "$PROJECT_ROOT"

    check_prerequisites
    detect_changes

    run_isabelle
    run_haskell
    run_ocaml
    run_typescript
    run_tests

    print_summary
}

main "$@"
