#!/usr/bin/env bash
#
# verify-outputs.sh - Compare outputs across language implementations
#
# Verifies that all language implementations produce equivalent results
# for the same deterministic inputs.
#
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"

SIZE="${1:-50}"
FUNC="${2:-lwe_encrypt}"

echo "=== Verifying $FUNC outputs across languages (size=$SIZE) ==="
echo ""

# Load opam environment if available (required for OCaml)
if command -v opam &>/dev/null; then
    eval "$(opam env 2>/dev/null)" || true
fi

TMPDIR="${TMPDIR:-/tmp}"

#############################################
# Haskell
#############################################
echo "--- Haskell ---"
HASKELL_DIR="${TMPDIR}/haskell_verify_$$"
mkdir -p "$HASKELL_DIR"

cat > "${HASKELL_DIR}/Verify.hs" << 'HASKELL_EOF'
{-# LANGUAGE BangPatterns #-}
module Main where

import qualified Lattice.LWE_Regev as L
import System.Environment (getArgs)

-- Simple deterministic pseudo-random generator (same as benchmark)
lcg :: Int -> Int
lcg seed = (seed * 1103515245 + 12345) `mod` 2147483648

randoms :: Int -> [Int]
randoms seed = iterate lcg seed

-- Extract integer from L.Int
toInteger' :: L.Int -> Integer
toInteger' (L.Int_of_integer k) = k

-- Generate test data
genVec :: Int -> Int -> [L.Int]
genVec seed n = take n $ map (\x -> L.Int_of_integer (fromIntegral (x `mod` 1000 - 500))) $ randoms seed

genMatrix :: Int -> Int -> Int -> [[L.Int]]
genMatrix seed rows cols = [genVec (seed + i) cols | i <- [0..rows-1]]

genBinaryVec :: Int -> Int -> [L.Int]
genBinaryVec seed n = take n $ map (\x -> L.Int_of_integer (fromIntegral (x `mod` 2))) $ randoms seed

main :: IO ()
main = do
  args <- getArgs
  let n = read (head args) :: Int
      func = args !! 1

  -- Prepare data (same seeds as benchmark)
  let !pkA = genMatrix 42 n n
      !pkB = genVec 43 n
      !pk = L.Lwe_public_key_ext pkA pkB ()
      !q = L.Int_of_integer 97
      !r = genBinaryVec 44 n
      !skS = genVec 42 n
      !sk = L.Lwe_secret_key_ext skS ()
      !ctU = genVec 43 n
      !ctV = L.Int_of_integer 50
      !ct = L.Lwe_ciphertext_ext ctU ctV ()

  case func of
    "lwe_encrypt" -> do
      let !result = L.lwe_encrypt pk q r True
      case result of
        L.Lwe_ciphertext_ext u v _ -> do
          let !uVals = map toInteger' u
              !vVal = toInteger' v
          putStrLn $ "u (first 10): " ++ show (take 10 uVals)
          putStrLn $ "v: " ++ show vVal
          putStrLn $ "u length: " ++ show (length uVals)
    "lwe_decrypt" -> do
      let !result = L.lwe_decrypt sk q ct
      putStrLn $ "decrypted: " ++ show result
    _ -> error "Unknown function"
HASKELL_EOF

if ghc -O2 -i"${PROJECT_ROOT}/haskell/isabella/src" "${HASKELL_DIR}/Verify.hs" -o "${HASKELL_DIR}/verify" -outputdir "$HASKELL_DIR" >/dev/null 2>&1; then
    "${HASKELL_DIR}/verify" "$SIZE" "$FUNC"
else
    echo "Haskell compilation failed"
fi
rm -rf "$HASKELL_DIR"

echo ""

#############################################
# OCaml
#############################################
echo "--- OCaml ---"
OCAML_DIR="${TMPDIR}/ocaml_verify_$$"
mkdir -p "$OCAML_DIR"

cat > "${OCAML_DIR}/verify.ml" << 'OCAML_EOF'
open Lwe_regev.LWE_Regev

(* Simple deterministic pseudo-random generator *)
let lcg seed = (seed * 1103515245 + 12345) mod 2147483648

let rec randoms seed n acc =
  if n <= 0 then List.rev acc
  else let next = lcg seed in randoms next (n-1) (seed :: acc)

let gen_vec seed n =
  List.map (fun x -> Int_of_integer (Z.of_int (x mod 1000 - 500))) (randoms seed n [])

let gen_matrix seed rows cols =
  List.init rows (fun i -> gen_vec (seed + i) cols)

let gen_binary_vec seed n =
  List.map (fun x -> Int_of_integer (Z.of_int (x mod 2))) (randoms seed n [])

let int_to_z i = match i with Int_of_integer z -> z

let () =
  let n = int_of_string Sys.argv.(1) in
  let func = Sys.argv.(2) in

  (* Prepare data - same seeds as benchmark *)
  let pk_a = gen_matrix 42 n n in
  let pk_b = gen_vec 43 n in
  let pk = Lwe_public_key_ext (pk_a, pk_b, ()) in
  let q = Int_of_integer (Z.of_int 97) in
  let r = gen_binary_vec 44 n in
  let sk_s = gen_vec 42 n in
  let sk = Lwe_secret_key_ext (sk_s, ()) in
  let ct_u = gen_vec 43 n in
  let ct_v = Int_of_integer (Z.of_int 50) in
  let ct = Lwe_ciphertext_ext (ct_u, ct_v, ()) in

  match func with
  | "lwe_encrypt" ->
    let result = lwe_encrypt pk q r true in
    (match result with
     | Lwe_ciphertext_ext (u, v, _) ->
       let first_10 = List.filteri (fun i _ -> i < 10) u in
       Printf.printf "u (first 10): [%s]\n"
         (String.concat "; " (List.map (fun i -> Z.to_string (int_to_z i)) first_10));
       Printf.printf "v: %s\n" (Z.to_string (int_to_z v));
       Printf.printf "u length: %d\n" (List.length u))
  | "lwe_decrypt" ->
    let result = lwe_decrypt sk q ct in
    Printf.printf "decrypted: %b\n" result
  | _ -> failwith "Unknown function"
OCAML_EOF

OCAML_SRC="${PROJECT_ROOT}/ocaml/isabella/src/lattice"
if ocamlfind ocamlopt -package zarith -linkpkg -I "$OCAML_SRC" \
    "${OCAML_SRC}/lwe_regev.ml" "${OCAML_DIR}/verify.ml" \
    -o "${OCAML_DIR}/verify" 2>/dev/null; then
    "${OCAML_DIR}/verify" "$SIZE" "$FUNC"
else
    echo "OCaml compilation failed"
fi
rm -rf "$OCAML_DIR"

echo ""

#############################################
# JavaScript
#############################################
echo "--- JavaScript ---"
JS_FILE="${TMPDIR}/verify_$$.js"

cat > "$JS_FILE" << 'JS_EOF'
const { Isabella } = require(process.env.JS_PATH);

// Fixed LCG using BigInt for precision (matches Haskell/Scala)
function lcg(seed) {
  return Number((BigInt(seed) * 1103515245n + 12345n) % 2147483648n);
}

function randoms(seed, n) {
  const result = [];
  let s = seed;
  for (let i = 0; i < n; i++) {
    result.push(s);
    s = lcg(s);
  }
  return result;
}

function genVec(seed, n) {
  return randoms(seed, n).map(x => x % 1000 - 500);
}

function genMatrix(seed, rows, cols) {
  return Array.from({length: rows}, (_, i) => genVec(seed + i, cols));
}

function genBinaryVec(seed, n) {
  return randoms(seed, n).map(x => x % 2);
}

const n = parseInt(process.argv[2]);
const func = process.argv[3];

// Prepare data - same seeds as benchmark
const pkA = genMatrix(42, n, n);
const pkB = genVec(43, n);
const q = 97;
const r = genBinaryVec(44, n);
const skS = genVec(42, n);
const ctU = genVec(43, n);
const ctV = 50;

if (func === "lwe_encrypt") {
  const result = Isabella.lweEncrypt(pkA, pkB, q, r, true);
  console.log(`u (first 10): [${result.u.slice(0, 10).join("; ")}]`);
  console.log(`v: ${result.v}`);
  console.log(`u length: ${result.u.length}`);
} else if (func === "lwe_decrypt") {
  const result = Isabella.lweDecrypt(skS, q, ctU, ctV);
  console.log(`decrypted: ${result}`);
}
JS_EOF

JS_PATH="${PROJECT_ROOT}/javascript/isabella/dist/isabella.js"
if [[ -f "$JS_PATH" ]]; then
    JS_PATH="$JS_PATH" node "$JS_FILE" "$SIZE" "$FUNC" 2>/dev/null || echo "JavaScript execution failed"
else
    echo "JavaScript not available"
fi
rm -f "$JS_FILE"

echo ""

#############################################
# Scala
#############################################
echo "--- Scala ---"
SCALA_FILE="${TMPDIR}/Verify_$$.scala"

cat "${PROJECT_ROOT}/scala/isabella/src/Lattice/LWE_Regev.scala" > "$SCALA_FILE"

cat >> "$SCALA_FILE" << 'SCALA_EOF'

object Verify {
  import scala.util.Random

  def lcg(seed: Int): Int = ((seed.toLong * 1103515245 + 12345) % 2147483648L).toInt

  def randoms(seed: Int, n: Int): List[Int] = {
    var s = seed
    (0 until n).map { _ =>
      val curr = s
      s = lcg(s)
      curr
    }.toList
  }

  def genVec(seed: Int, n: Int): List[LWE_Regev.int] = {
    randoms(seed, n).map(x => LWE_Regev.int_of_integer(BigInt(x % 1000 - 500)))
  }

  def genMatrix(seed: Int, rows: Int, cols: Int): List[List[LWE_Regev.int]] = {
    (0 until rows).map(i => genVec(seed + i, cols)).toList
  }

  def genBinaryVec(seed: Int, n: Int): List[LWE_Regev.int] = {
    randoms(seed, n).map(x => LWE_Regev.int_of_integer(BigInt(x % 2)))
  }

  def main(args: Array[String]): Unit = {
    val n = args(0).toInt
    val func = args(1)

    // Prepare data - same seeds as benchmark
    val pkA = genMatrix(42, n, n)
    val pkB = genVec(43, n)
    val pk = LWE_Regev.lwe_public_key_exta(pkA, pkB, ())
    val q = LWE_Regev.int_of_integer(BigInt(97))
    val r = genBinaryVec(44, n)
    val skS = genVec(42, n)
    val sk = LWE_Regev.lwe_secret_key_exta(skS, ())
    val ctU = genVec(43, n)
    val ctV = LWE_Regev.int_of_integer(BigInt(50))
    val ct = LWE_Regev.lwe_ciphertext_exta(ctU, ctV, ())

    func match {
      case "lwe_encrypt" =>
        val result = LWE_Regev.lwe_encrypt(pk, q, r, true)
        result match {
          case LWE_Regev.lwe_ciphertext_exta(u, v, _) =>
            val first10 = u.take(10).map(i => LWE_Regev.integer_of_int(i).toString)
            println(s"u (first 10): [${first10.mkString("; ")}]")
            println(s"v: ${LWE_Regev.integer_of_int(v)}")
            println(s"u length: ${u.length}")
        }
      case "lwe_decrypt" =>
        val result = LWE_Regev.lwe_decrypt(sk, q, ct)
        println(s"decrypted: $result")
    }
  }
}
SCALA_EOF

if command -v scala-cli &>/dev/null; then
    scala-cli run "$SCALA_FILE" --suppress-experimental-warning -- "$SIZE" "$FUNC" 2>/dev/null || echo "Scala execution failed"
elif command -v scala &>/dev/null; then
    scala "$SCALA_FILE" "$SIZE" "$FUNC" 2>/dev/null || echo "Scala execution failed"
else
    echo "Scala not available"
fi
rm -f "$SCALA_FILE"

echo ""
echo "=== Verification complete ==="
