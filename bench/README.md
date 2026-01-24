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

### Function-Specific Examples

**Quick benchmark (recommended):**

```bash
# All functions - 7 sizes up to 750, fast settings
./run-benchmarks.sh \
  --function "inner_prod,vec_add,mat_vec_mult,lwe_encrypt,lwe_decrypt" \
  --sizes "10,50,100,200,350,500,750" \
  --iterations 4 --warmup 1
```

**Individual functions:**

```bash
# inner_prod: Inner product of two vectors
./run-benchmarks.sh --function inner_prod --sizes "10,50,100,200,350,500,750"

# vec_add: Component-wise vector addition
./run-benchmarks.sh --function vec_add --sizes "10,50,100,200,350,500,750"

# mat_vec_mult: Matrix-vector multiplication
./run-benchmarks.sh --function mat_vec_mult --sizes "10,50,100,200,350,500,750"

# lwe_encrypt: LWE encryption (Regev scheme)
./run-benchmarks.sh --function lwe_encrypt --sizes "10,50,100,200,350,500,750"

# lwe_decrypt: LWE decryption
./run-benchmarks.sh --function lwe_decrypt --sizes "10,50,100,200,350,500,750"
```

**Extended benchmark (thorough analysis, takes longer):**

```bash
# All functions with more iterations
./run-benchmarks.sh \
  --function "inner_prod,vec_add,mat_vec_mult,lwe_encrypt,lwe_decrypt" \
  --sizes "10,50,100,250,500,750,1000" \
  --iterations 5 --warmup 3
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
| Haskell | `ghc` (compilation with -O2) |
| OCaml | `opam`, `ocamlfind`, `zarith` |
| JavaScript | `node` (v18+) |
| Scala | `scala-cli` (recommended) or `scala` |

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

> **Note:** Benchmarks last run on 2026-01-24 at 12:51 UTC on Darwin-arm64 (Apple Silicon).

**O(n) functions** (inner_prod, vec_add, lwe_decrypt) at n=500:

| Language | Relative Speed | Notes |
|----------|---------------|-------|
| OCaml | 1.0x | Fastest - native compiled with Zarith/GMP |
| Haskell | 5-9x | Compiled with GHC -O2 |
| Scala | 5-8x | JVM with JIT warmup |
| JavaScript | 60-110x | js_of_ocaml compiled to JS |

**O(n²) functions** (mat_vec_mult, lwe_encrypt) at n=500:

| Language | Relative Speed | Notes |
|----------|---------------|-------|
| Haskell | 1.0x | Fastest at larger sizes due to GHC optimizations |
| Scala | 2-2.5x | Competitive with JIT warmup |
| OCaml | 4-6x | Slower for matrix operations at scale |
| JavaScript | 11-14x | Reasonable given JS overhead |

**Key observations:**
- OCaml dominates O(n) operations due to Zarith/GMP for arbitrary precision arithmetic
- Haskell (compiled with -O2) becomes fastest for O(n²) operations at n > 200
- Scala performs consistently in the middle across all functions
- JavaScript is slowest but maintains reasonable scaling behavior

**Technical notes:**
- Haskell benchmarks use compiled code (`ghc -O2`) with proper deep evaluation forcing
- Scala benchmarks run warmup + timed iterations inside a single JVM to exclude startup overhead
- All languages use identical seeded RNG (LCG with BigInt precision) for fair comparison
- Results verified: all implementations produce identical encryption outputs
