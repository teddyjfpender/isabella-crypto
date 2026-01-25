(** List-based vectors and matrices

    This module provides vector and matrix operations using OCaml lists.
    While not optimal for performance, this representation directly corresponds
    to the Isabelle formalization and preserves all proven properties.

    Generated from [Canon/Linear/ListVec.thy] *)

(** {1 Types} *)

(** Integer vector (represented as a list) *)
type int_vec = int list

(** Integer matrix (list of row vectors) *)
type int_matrix = int list list

(** {1 Dimension Validation} *)

(** [valid_vec n v] checks if vector [v] has dimension [n]. *)
let valid_vec n v = List.length v = n

(** [valid_matrix m n mat] checks if matrix [mat] has dimensions m x n. *)
let valid_matrix m n mat =
  List.length mat = m && List.for_all (fun row -> List.length row = n) mat

(** {1 Vector Arithmetic} *)

(** [vec_add v1 v2] computes element-wise vector addition. *)
let vec_add v1 v2 = List.map2 ( + ) v1 v2

(** [vec_sub v1 v2] computes element-wise vector subtraction. *)
let vec_sub v1 v2 = List.map2 ( - ) v1 v2

(** [scalar_mult c v] computes scalar multiplication. *)
let scalar_mult c v = List.map (( * ) c) v

(** [vec_neg v] negates each element of the vector. *)
let vec_neg v = List.map (fun x -> -x) v

(** {1 Products} *)

(** [inner_prod v1 v2] computes the inner (dot) product. *)
let inner_prod v1 v2 =
  List.fold_left2 (fun acc x y -> acc + x * y) 0 v1 v2

(** {1 Matrix Operations} *)

(** [mat_vec_mult a v] computes A * v where A is a matrix and v is a vector. *)
let mat_vec_mult a v = List.map (inner_prod v) a

(** [transpose mat] transposes a matrix. *)
let rec transpose = function
  | [] -> []
  | [] :: _ -> []
  | rows -> List.map List.hd rows :: transpose (List.map List.tl rows)

(** [mat_transpose_vec_mult a v] computes A^T * v efficiently. *)
let mat_transpose_vec_mult a v = mat_vec_mult (transpose a) v

(** {1 Vector Manipulation} *)

(** [vec_concat v1 v2] concatenates two vectors. *)
let vec_concat v1 v2 = v1 @ v2

(** [split_vec n v] splits vector at position [n].
    Returns [(first n elements, remaining elements)]. *)
let split_vec n v =
  let rec aux i acc = function
    | [] -> (List.rev acc, [])
    | x :: xs when i > 0 -> aux (i - 1) (x :: acc) xs
    | xs -> (List.rev acc, xs)
  in
  aux n [] v
