#!/usr/bin/env bash
#
# summarize.sh - Generate summary report from benchmark results
#
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
DATA_DIR="${SCRIPT_DIR}/data"

if [[ ! -d "$DATA_DIR" ]] || [[ -z "$(ls -A "$DATA_DIR" 2>/dev/null)" ]]; then
    echo "No benchmark data found in ${DATA_DIR}"
    exit 0
fi

export DATA_DIR

python3 << 'EOF'
import json
import os
from pathlib import Path
from collections import defaultdict

data_dir = Path(os.environ.get('DATA_DIR', 'bench/data'))

# Collect all results from aggregated JSON files
# New format: each function has one JSON file with all results
results = defaultdict(lambda: defaultdict(dict))

for json_file in data_dir.glob('*.json'):
    if json_file.name == 'summary.json':
        continue
    try:
        with open(json_file) as f:
            data = json.load(f)

        func_name = data.get('function', json_file.stem)

        # Handle aggregated format with 'results' array
        if 'results' in data:
            for entry in data['results']:
                lang = entry['language']
                size = entry['input_size']
                results[func_name][size][lang] = entry['timing']
        # Handle legacy single-result format
        elif 'language' in data:
            lang = data['language']
            size = data['input_size']
            results[func_name][size][lang] = data['timing']
    except (json.JSONDecodeError, KeyError) as e:
        continue

if not results:
    print("No benchmark results found")
    exit(0)

# Print summary
print("\n" + "=" * 70)
print("BENCHMARK SUMMARY")
print("=" * 70)

for func_name in sorted(results.keys()):
    print(f"\n## {func_name}")
    print("-" * 50)

    sizes = sorted(results[func_name].keys())
    langs = set()
    for size in sizes:
        langs.update(results[func_name][size].keys())
    langs = sorted(langs)

    # Header
    print(f"{'Size':<10}", end="")
    for lang in langs:
        print(f"{lang:<15}", end="")
    print()

    # Data rows
    for size in sizes:
        print(f"{size:<10}", end="")
        for lang in langs:
            if lang in results[func_name][size]:
                mean_ms = results[func_name][size][lang]['mean'] * 1000
                print(f"{mean_ms:>10.2f} ms  ", end="")
            else:
                print(f"{'N/A':>10}     ", end="")
        print()

    # Relative performance (vs fastest)
    print("\nRelative (1.0 = fastest):")
    for size in sizes:
        times = {lang: results[func_name][size][lang]['mean']
                 for lang in langs if lang in results[func_name][size]}
        if not times:
            continue

        fastest = min(times.values())
        print(f"{size:<10}", end="")
        for lang in langs:
            if lang in times:
                relative = times[lang] / fastest if fastest > 0 else 0
                print(f"{relative:>10.2f}x     ", end="")
            else:
                print(f"{'N/A':>10}     ", end="")
        print()

print("\n" + "=" * 70)

# Write JSON summary
summary = {
    'functions': {}
}

for func_name in results:
    summary['functions'][func_name] = {
        'sizes': {}
    }
    for size in results[func_name]:
        summary['functions'][func_name]['sizes'][str(size)] = {}
        for lang in results[func_name][size]:
            summary['functions'][func_name]['sizes'][str(size)][lang] = results[func_name][size][lang]

summary_file = data_dir / 'summary.json'
with open(summary_file, 'w') as f:
    json.dump(summary, f, indent=2)

print(f"\nSummary written to: {summary_file}")
EOF
