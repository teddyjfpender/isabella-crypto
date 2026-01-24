#!/usr/bin/env bash
#
# Scala benchmark runner with JVM warmup inside single invocation
# Removes JVM startup overhead by running warmup + iterations in one process
#
set -uo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "${SCRIPT_DIR}/../.." && pwd)"
SCALA_DIR="${PROJECT_ROOT}/scala/isabella"

FUNC="$1"
SIZE="$2"
# Internal warmup and iterations to let JIT optimize
WARMUP_INTERNAL=5
ITERATIONS_INTERNAL=10

# Create benchmark script with .scala extension (required by scala-cli)
TMPDIR="${TMPDIR:-/tmp}"
BENCH_FILE="${TMPDIR}/bench_$$.scala"
trap "rm -f $BENCH_FILE" EXIT

# Include the LWE_Regev object and benchmark code
cat "${SCALA_DIR}/src/Lattice/LWE_Regev.scala" > "$BENCH_FILE"

# Note: Isabelle generates Scala with lowercase case class names and 'a' suffix
cat >> "$BENCH_FILE" << EOF

object Benchmark {
  import scala.util.Random

  def genVec(seed: Int, n: Int): List[LWE_Regev.int] = {
    val rng = new Random(seed)
    (0 until n).map(_ => LWE_Regev.int_of_integer(BigInt(rng.nextInt(1000) - 500))).toList
  }

  def genMatrix(seed: Int, rows: Int, cols: Int): List[List[LWE_Regev.int]] = {
    (0 until rows).map(i => genVec(seed + i, cols)).toList
  }

  def genBinaryVec(seed: Int, n: Int): List[LWE_Regev.int] = {
    val rng = new Random(seed)
    (0 until n).map(_ => LWE_Regev.int_of_integer(BigInt(rng.nextInt(2)))).toList
  }

  def runBenchmark(func: String, v1: List[LWE_Regev.int], v2: List[LWE_Regev.int],
                   m: List[List[LWE_Regev.int]], pk: LWE_Regev.lwe_public_key_ext[Unit],
                   q: LWE_Regev.int, r: List[LWE_Regev.int],
                   sk: LWE_Regev.lwe_secret_key_ext[Unit], ct: LWE_Regev.lwe_ciphertext_ext[Unit]): Unit = {
    func match {
      case "inner_prod" => LWE_Regev.inner_prod(v1, v2)
      case "mat_vec_mult" => LWE_Regev.mat_vec_mult(m, v1)
      case "vec_add" => LWE_Regev.vec_add(v1, v2)
      case "lwe_encrypt" => LWE_Regev.lwe_encrypt(pk, q, r, true)
      case "lwe_decrypt" => LWE_Regev.lwe_decrypt(sk, q, ct)
      case _ => throw new RuntimeException(s"Unknown function: \$func")
    }
  }

  def main(args: Array[String]): Unit = {
    val func = "${FUNC}"
    val size = ${SIZE}
    val warmupIterations = ${WARMUP_INTERNAL}
    val timedIterations = ${ITERATIONS_INTERNAL}

    // Prepare data before timing
    val v1 = genVec(42, size)
    val v2 = genVec(43, size)
    val m = genMatrix(42, size, size)
    val pkA = genMatrix(42, size, size)
    val pkB = genVec(43, size)
    val pk = LWE_Regev.lwe_public_key_exta(pkA, pkB, ())
    val q = LWE_Regev.int_of_integer(BigInt(97))
    val r = genBinaryVec(44, size)
    val skS = genVec(42, size)
    val sk = LWE_Regev.lwe_secret_key_exta(skS, ())
    val ctU = genVec(43, size)
    val ctV = LWE_Regev.int_of_integer(BigInt(50))
    val ct = LWE_Regev.lwe_ciphertext_exta(ctU, ctV, ())

    // Warmup iterations (let JIT compile hot paths)
    for (_ <- 0 until warmupIterations) {
      runBenchmark(func, v1, v2, m, pk, q, r, sk, ct)
    }

    // Timed iterations
    val times = (0 until timedIterations).map { _ =>
      val start = System.nanoTime()
      runBenchmark(func, v1, v2, m, pk, q, r, sk, ct)
      val end = System.nanoTime()
      (end - start) / 1e9
    }

    // Output median time (more stable than mean)
    val sorted = times.sorted
    val median = if (sorted.length % 2 == 0) {
      (sorted(sorted.length / 2 - 1) + sorted(sorted.length / 2)) / 2
    } else {
      sorted(sorted.length / 2)
    }

    println(s"""{"elapsed": \$median}""")
  }
}
EOF

# Compile and run with scala-cli
if command -v scala-cli &>/dev/null; then
    scala-cli run "$BENCH_FILE" --suppress-experimental-warning 2>/dev/null | grep -E '^\{"elapsed"' || exit 1
elif command -v scala &>/dev/null; then
    scala -deprecation "$BENCH_FILE" 2>/dev/null | grep -E '^\{"elapsed"' || exit 1
else
    echo "ERROR: scala or scala-cli not found" >&2
    exit 1
fi
