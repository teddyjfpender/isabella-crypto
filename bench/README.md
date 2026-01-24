# Isabella Benchmarks

Cross-language performance benchmarks for the verified lattice cryptography library.

## Overview

Compares the same functions across all language targets:
- **Haskell** (native via GHC)
- **OCaml** (native via ocamlopt)
- **JavaScript** (via Node.js + js_of_ocaml)
- **Scala** (via JVM)

## Running Benchmarks

```bash
# Run all benchmarks
./run-benchmarks.sh

# Benchmark specific function
./run-benchmarks.sh --function inner_prod

# Specific languages only
./run-benchmarks.sh --languages "haskell,javascript"

# Custom input sizes
./run-benchmarks.sh --sizes "100,500,1000,2000"

# More iterations for accuracy
./run-benchmarks.sh --iterations 20 --warmup 5
```

## Functions Benchmarked

| Function | Description | Complexity |
|----------|-------------|------------|
| `inner_prod` | Inner product of two vectors | O(n) |
| `vec_add` | Component-wise vector addition | O(n) |
| `mat_vec_mult` | Matrix-vector multiplication | O(n²) |
| `lwe_encrypt` | LWE encryption (Regev scheme) | O(n²) |
| `lwe_decrypt` | LWE decryption | O(n) |

## Output Format

Results are stored as one aggregated JSON file per function in `data/<function>.json`:

```json
{
  "function": "inner_prod",
  "platform": "Darwin-arm64",
  "benchmark_config": {
    "iterations": 10,
    "warmup_iterations": 3,
    "sizes": [10, 100, 1000, 5000]
  },
  "results": [
    {
      "language": "haskell",
      "input_size": 1000,
      "iterations": 10,
      "warmup_iterations": 3,
      "timing": {
        "unit": "seconds",
        "min": 0.0012,
        "max": 0.0018,
        "mean": 0.0015,
        "median": 0.0014,
        "stdev": 0.0002
      },
      "timestamp": "2024-01-24T10:30:00Z"
    },
    // ... more results for other languages and sizes
  ]
}
```

## Summary Report

After running benchmarks, view the summary:

```bash
./summarize.sh
```

Output:
```
======================================================================
BENCHMARK SUMMARY
======================================================================

## inner_prod
--------------------------------------------------
Size      haskell        javascript     ocaml
10             0.12 ms       0.45 ms       0.08 ms
100            0.89 ms       2.34 ms       0.56 ms
1000           8.23 ms      21.45 ms       5.12 ms

Relative (1.0 = fastest):
10             1.50x         5.63x         1.00x
100            1.59x         4.18x         1.00x
1000           1.61x         4.19x         1.00x
```

## Requirements

Each language needs its toolchain installed:

| Language | Requirements |
|----------|-------------|
| Haskell | `ghc`, `runhaskell` |
| OCaml | `opam`, `ocamlfind`, `zarith` |
| JavaScript | `node` (v18+) |
| Scala | `scala` or `scala-cli` |

## CI Integration

Benchmarks run in CI on tagged releases to track performance over time.

## Adding New Benchmarks

1. Add the function to `runners/<language>-runner.sh`
2. Add to the `FUNCTIONS` list in `run-benchmarks.sh`
3. Run `./run-benchmarks.sh --function <new_function>`

## Notes

- **Internal Timing**: Benchmarks use internal timing within each language runtime to measure algorithm execution time only (excludes interpreter startup/compilation overhead)
- **Warmup**: Each benchmark does warmup iterations to avoid cold-start effects
- **Variance**: Multiple iterations are run to calculate mean/median/stdev
- **Fairness**: All languages use the same seeded random data generation (LCG with seed 42)
- **Platform**: Results vary by platform (ARM vs x86, OS, etc.)

## Expected Performance

Typical relative performance (OCaml = 1.0x baseline):

| Language | Relative Speed | Notes |
|----------|---------------|-------|
| OCaml | 1.0x | Fastest - native compiled with Zarith/GMP |
| Haskell | 30-50x | Interpreted via runhaskell, arbitrary precision Integer |
| JavaScript | 50-500x | js_of_ocaml compiled to JS, runs in Node.js |
| Scala | ~100x | JVM startup + BigInt overhead |

Note: Haskell benchmarks use `runhaskell` (interpreted). Compiling with GHC + optimization would be significantly faster.
