(* JavaScript bindings for Isabella lattice crypto library *)
(* Compiled via js_of_ocaml *)

open Js_of_ocaml

(* Convert OCaml int list to JS array *)
let int_list_to_js lst =
  let arr = new%js Js.array_empty in
  List.iter (fun (Lwe_regev.LWE_Regev.Int_of_integer z) ->
    let _ = arr##push (Js.number_of_float (Z.to_float z)) in ()
  ) lst;
  arr

(* Convert JS array to OCaml int list *)
let js_to_int_list arr =
  let len = arr##.length in
  let rec build i acc =
    if i < 0 then acc
    else
      let n = Js.float_of_number (Js.Optdef.get (Js.array_get arr i) (fun () -> Js.number_of_float 0.0)) in
      build (i - 1) (Lwe_regev.LWE_Regev.Int_of_integer (Z.of_float n) :: acc)
  in
  build (len - 1) []

(* Convert OCaml int matrix to JS 2D array *)
let int_matrix_to_js mat =
  let outer = new%js Js.array_empty in
  List.iter (fun row ->
    let _ = outer##push (int_list_to_js row) in ()
  ) mat;
  outer

(* Convert JS 2D array to OCaml int matrix *)
let js_to_int_matrix arr =
  let len = arr##.length in
  let rec build i acc =
    if i < 0 then acc
    else
      let row = Js.Optdef.get (Js.array_get arr i) (fun () -> new%js Js.array_empty) in
      build (i - 1) (js_to_int_list row :: acc)
  in
  build (len - 1) []

(* Export vec_add *)
let vec_add_js v1 v2 =
  let result = Lwe_regev.LWE_Regev.vec_add (js_to_int_list v1) (js_to_int_list v2) in
  int_list_to_js result

(* Export vec_mod *)
let vec_mod_js v q =
  let q_int = Lwe_regev.LWE_Regev.Int_of_integer (Z.of_float (Js.float_of_number q)) in
  let result = Lwe_regev.LWE_Regev.vec_mod (js_to_int_list v) q_int in
  int_list_to_js result

(* Export inner_prod *)
let inner_prod_js v1 v2 =
  let Lwe_regev.LWE_Regev.Int_of_integer result =
    Lwe_regev.LWE_Regev.inner_prod (js_to_int_list v1) (js_to_int_list v2) in
  Js.number_of_float (Z.to_float result)

(* Export mat_vec_mult *)
let mat_vec_mult_js mat vec =
  let result = Lwe_regev.LWE_Regev.mat_vec_mult (js_to_int_matrix mat) (js_to_int_list vec) in
  int_list_to_js result

(* Export transpose *)
let transpose_js mat =
  let result = Lwe_regev.LWE_Regev.transpose (js_to_int_matrix mat) in
  int_matrix_to_js result

(* Export encode_bit *)
let encode_bit_js q b =
  let q_int = Lwe_regev.LWE_Regev.Int_of_integer (Z.of_float (Js.float_of_number q)) in
  let Lwe_regev.LWE_Regev.Int_of_integer result = Lwe_regev.LWE_Regev.encode_bit q_int (Js.to_bool b) in
  Js.number_of_float (Z.to_float result)

(* Export decode_bit *)
let decode_bit_js q d =
  let q_int = Lwe_regev.LWE_Regev.Int_of_integer (Z.of_float (Js.float_of_number q)) in
  let d_int = Lwe_regev.LWE_Regev.Int_of_integer (Z.of_float (Js.float_of_number d)) in
  Js.bool (Lwe_regev.LWE_Regev.decode_bit q_int d_int)

(* Export lwe_encrypt *)
let lwe_encrypt_js pk_a pk_b q r m =
  let pk = Lwe_regev.LWE_Regev.Lwe_public_key_ext (js_to_int_matrix pk_a, js_to_int_list pk_b, ()) in
  let q_int = Lwe_regev.LWE_Regev.Int_of_integer (Z.of_float (Js.float_of_number q)) in
  let ct = Lwe_regev.LWE_Regev.lwe_encrypt pk q_int (js_to_int_list r) (Js.to_bool m) in
  let Lwe_regev.LWE_Regev.Lwe_ciphertext_ext (u, Lwe_regev.LWE_Regev.Int_of_integer v, ()) = ct in
  object%js
    val u = int_list_to_js u
    val v = Js.number_of_float (Z.to_float v)
  end

(* Export lwe_decrypt *)
let lwe_decrypt_js sk_s q ct_u ct_v =
  let sk = Lwe_regev.LWE_Regev.Lwe_secret_key_ext (js_to_int_list sk_s, ()) in
  let q_int = Lwe_regev.LWE_Regev.Int_of_integer (Z.of_float (Js.float_of_number q)) in
  let v_int = Lwe_regev.LWE_Regev.Int_of_integer (Z.of_float (Js.float_of_number ct_v)) in
  let ct = Lwe_regev.LWE_Regev.Lwe_ciphertext_ext (js_to_int_list ct_u, v_int, ()) in
  Js.bool (Lwe_regev.LWE_Regev.lwe_decrypt sk q_int ct)

(* Register all exports *)
let () =
  Js.export "Isabella"
    (object%js
      method vecAdd v1 v2 = vec_add_js v1 v2
      method vecMod v q = vec_mod_js v q
      method innerProd v1 v2 = inner_prod_js v1 v2
      method matVecMult mat vec = mat_vec_mult_js mat vec
      method transpose mat = transpose_js mat
      method encodeBit q b = encode_bit_js q b
      method decodeBit q d = decode_bit_js q d
      method lweEncrypt pkA pkB q r m = lwe_encrypt_js pkA pkB q r m
      method lweDecrypt skS q ctU ctV = lwe_decrypt_js skS q ctU ctV
    end)
