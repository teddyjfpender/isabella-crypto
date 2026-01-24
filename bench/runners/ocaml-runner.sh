#!/usr/bin/env bash
#
# OCaml benchmark runner with internal timing
#
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "${SCRIPT_DIR}/../.." && pwd)"
OCAML_DIR="${PROJECT_ROOT}/ocaml/isabella"

FUNC="$1"
SIZE="$2"

# Ensure OCaml is built
if [[ ! -d "${OCAML_DIR}/_build" ]]; then
    cd "$OCAML_DIR"
    eval $(opam env 2>/dev/null || true)
    dune build src/lattice/lwe_regev.ml 2>/dev/null || true
fi

# Create and run benchmark
BENCH_FILE=$(mktemp /tmp/bench_XXXXXX.ml)
trap "rm -f $BENCH_FILE" EXIT

cat > "$BENCH_FILE" << 'OCAML_CODE'
(* Include the LWE_Regev module *)
OCAML_CODE

cat "${OCAML_DIR}/src/lattice/lwe_regev.ml" >> "$BENCH_FILE"

cat >> "$BENCH_FILE" << EOF

(* Benchmark harness with internal timing *)
let () =
  Random.init 42;

  let gen_vec n =
    List.init n (fun _ -> LWE_Regev.Int_of_integer (Z.of_int (Random.int 1000 - 500)))
  in

  let gen_matrix rows cols =
    List.init rows (fun _ -> gen_vec cols)
  in

  let gen_binary_vec n =
    List.init n (fun _ -> LWE_Regev.Int_of_integer (Z.of_int (Random.int 2)))
  in

  let func = "${FUNC}" in
  let size = ${SIZE} in

  (* Prepare data before timing *)
  let v1 = gen_vec size in
  let v2 = gen_vec size in
  let m = gen_matrix size size in
  let pkA = gen_matrix size size in
  let pkB = gen_vec size in
  let pk = LWE_Regev.Lwe_public_key_ext (pkA, pkB, ()) in
  let q = LWE_Regev.Int_of_integer (Z.of_int 97) in
  let r = gen_binary_vec size in
  let skS = gen_vec size in
  let sk = LWE_Regev.Lwe_secret_key_ext (skS, ()) in
  let ctU = gen_vec size in
  let ctV = LWE_Regev.Int_of_integer (Z.of_int 50) in
  let ct = LWE_Regev.Lwe_ciphertext_ext (ctU, ctV, ()) in

  (* Time the operation *)
  let start = Unix.gettimeofday () in
  let _ = match func with
    | "inner_prod" -> ignore (LWE_Regev.inner_prod v1 v2)
    | "mat_vec_mult" -> ignore (LWE_Regev.mat_vec_mult m v1)
    | "vec_add" -> ignore (LWE_Regev.vec_add v1 v2)
    | "lwe_encrypt" -> ignore (LWE_Regev.lwe_encrypt pk q r true)
    | "lwe_decrypt" -> ignore (LWE_Regev.lwe_decrypt sk q ct)
    | _ -> failwith ("Unknown function: " ^ func)
  in
  let elapsed = Unix.gettimeofday () -. start in
  Printf.printf "{\"elapsed\": %.9f}\n" elapsed
EOF

# Compile and run
cd "$OCAML_DIR"
eval $(opam env 2>/dev/null || true)
ocamlfind ocamlopt -package zarith,unix -linkpkg -w -a "$BENCH_FILE" -o /tmp/bench_exe 2>/dev/null
/tmp/bench_exe
rm -f /tmp/bench_exe
