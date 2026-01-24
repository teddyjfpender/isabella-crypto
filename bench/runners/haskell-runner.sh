#!/usr/bin/env bash
#
# Haskell benchmark runner with compiled code (ghc -O2)
#
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "${SCRIPT_DIR}/../.." && pwd)"

FUNC="$1"
SIZE="$2"

# Create temp directory for compiled benchmark
TMPDIR="${TMPDIR:-/tmp}"
BENCH_DIR="${TMPDIR}/haskell_bench_$$"
mkdir -p "$BENCH_DIR"
trap "rm -rf $BENCH_DIR" EXIT

BENCH_FILE="${BENCH_DIR}/Bench.hs"

# Generate Haskell benchmark code
cat > "$BENCH_FILE" << EOF
{-# LANGUAGE BangPatterns #-}
module Main where

import qualified Lattice.LWE_Regev as L
import System.CPUTime
import Text.Printf

-- Simple deterministic pseudo-random generator
lcg :: Int -> Int
lcg seed = (seed * 1103515245 + 12345) \`mod\` 2147483648

randoms :: Int -> [Int]
randoms seed = iterate lcg seed

-- Generate test data
genVec :: Int -> Int -> [L.Int]
genVec seed n = take n $ map (\\x -> L.Int_of_integer (fromIntegral (x \`mod\` 1000 - 500))) $ randoms seed

genMatrix :: Int -> Int -> Int -> [[L.Int]]
genMatrix seed rows cols = [genVec (seed + i) cols | i <- [0..rows-1]]

genBinaryVec :: Int -> Int -> [L.Int]
genBinaryVec seed n = take n $ map (\\x -> L.Int_of_integer (fromIntegral (x \`mod\` 2))) $ randoms seed

-- Force full evaluation of L.Int (extract and evaluate the Integer inside)
forceInt :: L.Int -> ()
forceInt (L.Int_of_integer i) = i \`seq\` ()

-- Force full evaluation of a list of L.Int
forceIntList :: [L.Int] -> ()
forceIntList [] = ()
forceIntList (x:xs) = forceInt x \`seq\` forceIntList xs

main :: IO ()
main = do
  let n = ${SIZE}

  -- Prepare data before timing (force evaluation)
  let !v1 = genVec 42 n
      !v2 = genVec 43 n
      !m = genMatrix 42 n n
      !pkA = genMatrix 42 n n
      !pkB = genVec 43 n
      !pk = L.Lwe_public_key_ext pkA pkB ()
      !q = L.Int_of_integer 97
      !r = genBinaryVec 44 n
      !skS = genVec 42 n
      !sk = L.Lwe_secret_key_ext skS ()
      !ctU = genVec 43 n
      !ctV = L.Int_of_integer 50
      !ct = L.Lwe_ciphertext_ext ctU ctV ()

  -- Force data structures (deep evaluation)
  let !_ = forceIntList v1
      !_ = forceIntList v2
      !_ = foldr (\\row acc -> forceIntList row \`seq\` acc) () m

  start <- getCPUTime
  case "${FUNC}" of
    "inner_prod" -> case L.inner_prod v1 v2 of
                      L.Int_of_integer i -> i \`seq\` return ()
    "mat_vec_mult" -> let !result = L.mat_vec_mult m v1 in forceIntList result \`seq\` return ()
    "vec_add" -> let !result = L.vec_add v1 v2 in forceIntList result \`seq\` return ()
    "lwe_encrypt" -> case L.lwe_encrypt pk q r True of
                       L.Lwe_ciphertext_ext u v _ -> forceIntList u \`seq\` forceInt v \`seq\` return ()
    "lwe_decrypt" -> let !result = L.lwe_decrypt sk q ct in result \`seq\` return ()
    _ -> error "Unknown function"
  end <- getCPUTime

  let elapsed :: Double
      elapsed = fromIntegral (end - start) / 1e12
  printf "{\"elapsed\": %.9f}\\n" elapsed
EOF

# Compile with optimization (suppress all output)
if ! ghc -O2 -i"${PROJECT_ROOT}/haskell/isabella/src" "$BENCH_FILE" -o "${BENCH_DIR}/bench" -outputdir "$BENCH_DIR" >/dev/null 2>&1; then
    echo "Compilation failed" >&2
    exit 1
fi

# Run compiled benchmark
"${BENCH_DIR}/bench"
