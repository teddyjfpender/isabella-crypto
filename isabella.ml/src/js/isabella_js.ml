(** JavaScript bindings for Isabella Canon library

    This module exposes the verified Canon functions to JavaScript
    via js_of_ocaml. All functions maintain the same semantics as
    their OCaml counterparts.

    Provenance: Wrapper over Isabelle-exported Canon modules only. *)

open Js_of_ocaml
open Canon

(** Convert JS array to OCaml int list *)
let js_array_to_list arr =
  let len = arr##.length in
  let rec aux i acc =
    if i < 0 then acc
    else aux (i - 1) ((Js.to_float (Js.Unsafe.get arr i) |> int_of_float) :: acc)
  in
  aux (len - 1) []

(** Convert OCaml int list to JS array *)
let list_to_js_array lst =
  let arr = new%js Js.array_empty in
  List.iter (fun x -> ignore (arr##push (Js.number_of_float (float_of_int x)))) lst;
  arr

(** Convert JS 2D array to OCaml int list list *)
let js_matrix_to_list mat =
  let len = mat##.length in
  let rec aux i acc =
    if i < 0 then acc
    else
      let row = Js.Unsafe.get mat i in
      aux (i - 1) (js_array_to_list row :: acc)
  in
  aux (len - 1) []

(** Convert OCaml int list list to JS 2D array *)
let list_to_js_matrix mat =
  let arr = new%js Js.array_empty in
  List.iter (fun row -> ignore (arr##push (list_to_js_array row))) mat;
  arr

(** Export the Isabella module to JavaScript *)
let () =
  Js.export "Isabella"
    (object%js
       (** Centered modular reduction *)
       method modCentered x q =
         Zq.mod_centered (int_of_float (Js.to_float x)) (int_of_float (Js.to_float q))
         |> float_of_int |> Js.number_of_float

       (** Vector modular reduction *)
       method vecMod v q =
         let v' = js_array_to_list v in
         let q' = int_of_float (Js.to_float q) in
         Zq.vec_mod v' q' |> list_to_js_array

       (** Centered vector modular reduction *)
       method vecModCentered v q =
         let v' = js_array_to_list v in
         let q' = int_of_float (Js.to_float q) in
         Zq.vec_mod_centered v' q' |> list_to_js_array

       (** Distance from zero in Z_q *)
       method dist0 q x =
         Zq.dist0 (int_of_float (Js.to_float q)) (int_of_float (Js.to_float x))
         |> float_of_int |> Js.number_of_float

       (** Encode a bit for LWE *)
       method encodeBit q b =
         Zq.encode_bit (int_of_float (Js.to_float q)) (Js.to_bool b)
         |> float_of_int |> Js.number_of_float

       (** Decode a bit from LWE *)
       method decodeBit q x =
         Zq.decode_bit (int_of_float (Js.to_float q)) (int_of_float (Js.to_float x))
         |> Js.bool

       (** Vector addition *)
       method vecAdd v1 v2 =
         let v1' = js_array_to_list v1 in
         let v2' = js_array_to_list v2 in
         Listvec.vec_add v1' v2' |> list_to_js_array

       (** Vector subtraction *)
       method vecSub v1 v2 =
         let v1' = js_array_to_list v1 in
         let v2' = js_array_to_list v2 in
         Listvec.vec_sub v1' v2' |> list_to_js_array

       (** Scalar multiplication *)
       method scalarMult c v =
         let c' = int_of_float (Js.to_float c) in
         let v' = js_array_to_list v in
         Listvec.scalar_mult c' v' |> list_to_js_array

       (** Vector negation *)
       method vecNeg v =
         let v' = js_array_to_list v in
         Listvec.vec_neg v' |> list_to_js_array

       (** Inner product *)
       method innerProd v1 v2 =
         let v1' = js_array_to_list v1 in
         let v2' = js_array_to_list v2 in
         Listvec.inner_prod v1' v2' |> float_of_int |> Js.number_of_float

       (** Matrix-vector multiplication *)
       method matVecMult mat vec =
         let mat' = js_matrix_to_list mat in
         let vec' = js_array_to_list vec in
         Listvec.mat_vec_mult mat' vec' |> list_to_js_array

       (** Matrix-vector multiplication mod q *)
       method matVecMultMod mat vec q =
         let mat' = js_matrix_to_list mat in
         let vec' = js_array_to_list vec in
         let q' = int_of_float (Js.to_float q) in
         Zq.mat_vec_mult_mod mat' vec' q' |> list_to_js_array

       (** Matrix transpose *)
       method transpose mat =
         let mat' = js_matrix_to_list mat in
         Listvec.transpose mat' |> list_to_js_matrix

       (** Validate vector dimension *)
       method validVec n v =
         let n' = int_of_float (Js.to_float n) in
         let v' = js_array_to_list v in
         Listvec.valid_vec n' v' |> Js.bool

       (** Validate matrix dimensions *)
       method validMatrix m n mat =
         let m' = int_of_float (Js.to_float m) in
         let n' = int_of_float (Js.to_float n) in
         let mat' = js_matrix_to_list mat in
         Listvec.valid_matrix m' n' mat' |> Js.bool

       (** Vector concatenation *)
       method vecConcat v1 v2 =
         let v1' = js_array_to_list v1 in
         let v2' = js_array_to_list v2 in
         Listvec.vec_concat v1' v2' |> list_to_js_array

       (** Split vector at position *)
       method splitVec n v =
         let n' = int_of_float (Js.to_float n) in
         let v' = js_array_to_list v in
         let (left, right) = Listvec.split_vec n' v' in
         let result = new%js Js.array_empty in
         ignore (result##push (list_to_js_array left));
         ignore (result##push (list_to_js_array right));
         result
     end)
