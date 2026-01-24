#!/usr/bin/env bash
#
# run-benchmarks.sh - Run benchmarks across all language targets
#
# Compares the same functions across Haskell, OCaml, Scala, and JavaScript
# with increasing input complexity.
#
# Usage:
#   ./run-benchmarks.sh [--function <name>] [--languages <list>] [--sizes <list>]
#
# Examples:
#   ./run-benchmarks.sh                           # Run all benchmarks
#   ./run-benchmarks.sh --function inner_prod     # Benchmark specific function
#   ./run-benchmarks.sh --languages "haskell,js"  # Specific languages only
#   ./run-benchmarks.sh --sizes "100,1000,10000"  # Custom input sizes
#
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"
DATA_DIR="${SCRIPT_DIR}/data"
RUNNERS_DIR="${SCRIPT_DIR}/runners"

# Colors
GREEN='\033[0;32m'
BLUE='\033[0;34m'
YELLOW='\033[1;33m'
RED='\033[0;31m'
NC='\033[0m'

log_info() { echo -e "${BLUE}[INFO]${NC} $1"; }
log_success() { echo -e "${GREEN}[OK]${NC} $1"; }
log_warn() { echo -e "${YELLOW}[WARN]${NC} $1"; }
log_error() { echo -e "${RED}[ERROR]${NC} $1"; }

# Default settings
FUNCTIONS="inner_prod,vec_add,mat_vec_mult,lwe_encrypt,lwe_decrypt"
LANGUAGES="haskell,ocaml,javascript,scala"
SIZES="10,50,100,200,350,500,750"
ITERATIONS=4
WARMUP=1

# Parse arguments
while [[ $# -gt 0 ]]; do
    case $1 in
        --function|-f) FUNCTIONS="$2"; shift 2 ;;
        --languages|-l) LANGUAGES="$2"; shift 2 ;;
        --sizes|-s) SIZES="$2"; shift 2 ;;
        --iterations|-i) ITERATIONS="$2"; shift 2 ;;
        --warmup|-w) WARMUP="$2"; shift 2 ;;
        --help|-h)
            echo "Usage: $0 [OPTIONS]"
            echo ""
            echo "Options:"
            echo "  --function, -f    Functions to benchmark (comma-separated)"
            echo "  --languages, -l   Languages to test (comma-separated)"
            echo "  --sizes, -s       Input sizes (comma-separated)"
            echo "  --iterations, -i  Number of iterations per benchmark"
            echo "  --warmup, -w      Number of warmup iterations"
            echo ""
            echo "Functions: inner_prod, mat_vec_mult, vec_add, lwe_encrypt, lwe_decrypt"
            echo "Languages: haskell, ocaml, javascript, scala"
            exit 0
            ;;
        *) log_error "Unknown option: $1"; exit 1 ;;
    esac
done

# Load opam environment if available
if command -v opam &>/dev/null; then
    eval $(opam env 2>/dev/null) || true
fi

# Check which languages are available
check_language() {
    local lang="$1"
    case $lang in
        haskell)
            command -v runhaskell &>/dev/null || return 1
            [[ -f "${PROJECT_ROOT}/haskell/isabella/src/Lattice/LWE_Regev.hs" ]] || return 1
            ;;
        ocaml)
            command -v ocamlfind &>/dev/null || return 1
            [[ -f "${PROJECT_ROOT}/ocaml/isabella/src/lattice/lwe_regev.ml" ]] || return 1
            ;;
        javascript)
            command -v node &>/dev/null || return 1
            [[ -f "${PROJECT_ROOT}/javascript/isabella/dist/isabella.js" ]] || return 1
            ;;
        scala)
            (command -v scala &>/dev/null || command -v scala-cli &>/dev/null) || return 1
            [[ -f "${PROJECT_ROOT}/scala/isabella/src/Lattice/LWE_Regev.scala" ]] || return 1
            ;;
        *)
            return 1
            ;;
    esac
    return 0
}

# Run a single benchmark and return JSON result
# Runners output JSON with elapsed time: {"elapsed": <seconds>}
run_single_benchmark() {
    local lang="$1"
    local func="$2"
    local size="$3"

    local runner="${RUNNERS_DIR}/${lang}-runner.sh"
    if [[ ! -x "$runner" ]]; then
        return 1
    fi

    # Collect timing from runner's internal measurements
    local times=()

    # Warmup runs (discard results)
    for ((i = 0; i < WARMUP; i++)); do
        "$runner" "$func" "$size" >/dev/null 2>&1 || true
    done

    # Timed runs - parse JSON output from runner
    for ((i = 0; i < ITERATIONS; i++)); do
        local result
        result=$("$runner" "$func" "$size" 2>/dev/null) || continue
        local elapsed
        elapsed=$(echo "$result" | python3 -c "import sys, json; print(json.load(sys.stdin)['elapsed'])" 2>/dev/null) || continue
        times+=("$elapsed")
    done

    # Check we got results
    if [[ ${#times[@]} -eq 0 ]]; then
        return 1
    fi

    # Calculate statistics and output JSON
    local times_json
    times_json=$(printf '%s\n' "${times[@]}" | python3 -c "import sys, json; print(json.dumps([float(x) for x in sys.stdin.read().strip().split('\n')]))")

    local timestamp
    timestamp=$(date -u +"%Y-%m-%dT%H:%M:%SZ")

    python3 -c "
import json
import statistics
times = json.loads('${times_json}')
result = {
    'language': '${lang}',
    'input_size': ${size},
    'iterations': len(times),
    'warmup_iterations': ${WARMUP},
    'timing': {
        'unit': 'seconds',
        'min': min(times),
        'max': max(times),
        'mean': statistics.mean(times),
        'median': statistics.median(times),
        'stdev': statistics.stdev(times) if len(times) > 1 else 0
    },
    'timestamp': '${timestamp}'
}
print(json.dumps(result))
"
}

# Main
echo ""
echo -e "${GREEN}Isabella Benchmarks${NC}"
echo "===================="
echo ""
log_info "Functions: $FUNCTIONS"
log_info "Languages: $LANGUAGES"
log_info "Sizes: $SIZES"
log_info "Iterations: $ITERATIONS (warmup: $WARMUP)"
echo ""

# Check available languages
available_langs=()
IFS=',' read -ra lang_array <<< "$LANGUAGES"
for lang in "${lang_array[@]}"; do
    if check_language "$lang"; then
        available_langs+=("$lang")
        log_success "$lang: available"
    else
        log_warn "$lang: not available (skipping)"
    fi
done

if [[ ${#available_langs[@]} -eq 0 ]]; then
    log_error "No languages available for benchmarking"
    exit 1
fi

echo ""

# Create data directory
mkdir -p "$DATA_DIR"

# Run benchmarks and collect results per function
IFS=',' read -ra func_array <<< "$FUNCTIONS"
IFS=',' read -ra size_array <<< "$SIZES"

for func in "${func_array[@]}"; do
    log_info "Benchmarking: $func"

    # Collect all results for this function
    results=()

    for size in "${size_array[@]}"; do
        echo -n "  size=$size: "

        for lang in "${available_langs[@]}"; do
            result=$(run_single_benchmark "$lang" "$func" "$size" 2>/dev/null) || true

            if [[ -n "$result" ]]; then
                results+=("$result")
                # Extract mean time for display
                mean=$(echo "$result" | python3 -c "import sys, json; print(f\"{json.load(sys.stdin)['timing']['mean']*1000:.2f}ms\")")
                echo -n "${lang}=${mean} "
            else
                echo -n "${lang}=FAIL "
            fi
        done
        echo ""
    done

    # Write aggregated results to single JSON file
    output_file="${DATA_DIR}/${func}.json"

    # Build JSON array from results
    results_json="["
    first=true
    for r in "${results[@]}"; do
        if [[ "$first" == "true" ]]; then
            first=false
        else
            results_json+=","
        fi
        results_json+="$r"
    done
    results_json+="]"

    python3 << PYTHON
import json

results_json = '''${results_json}'''
parsed = json.loads(results_json)

output = {
    'function': '${func}',
    'platform': '$(uname -s)-$(uname -m)',
    'benchmark_config': {
        'iterations': ${ITERATIONS},
        'warmup_iterations': ${WARMUP},
        'sizes': [${size_array[@]+"$(IFS=,; echo "${size_array[*]}")"}]
    },
    'results': parsed
}

with open('${output_file}', 'w') as f:
    json.dump(output, f, indent=2)
PYTHON

    log_success "Results written to: ${output_file}"
    echo ""
done

log_success "Benchmarks complete!"
log_info "Results in: ${DATA_DIR}/"

# Generate summary
"${SCRIPT_DIR}/summarize.sh" 2>/dev/null || true
