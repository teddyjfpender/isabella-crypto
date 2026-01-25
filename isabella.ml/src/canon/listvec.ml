(** List-based vectors and matrices
    Generated from Canon/Linear/ListVec.thy *)

type int_vec = int list
type int_matrix = int list list

(** Check if vector has given dimension *)
let valid_vec n v = List.length v = n

(** Check if matrix has dimensions m x n *)
let valid_matrix m n mat =
  List.length mat = m && List.for_all (fun row -> List.length row = n) mat

(** Vector addition *)
let vec_add xs ys = List.map2 (+) xs ys

(** Vector subtraction *)
let vec_sub xs ys = List.map2 (-) xs ys

(** Scalar multiplication *)
let scalar_mult c v = List.map (( * ) c) v

(** Vector negation *)
let vec_neg v = List.map (fun x -> -x) v

(** Inner product *)
let inner_prod xs ys =
  List.fold_left2 (fun acc x y -> acc + x * y) 0 xs ys

(** Matrix-vector multiplication *)
let mat_vec_mult a v = List.map (inner_prod v) a

(** Matrix transpose *)
let rec transpose = function
  | [] -> []
  | [] :: _ -> []
  | rows -> List.map List.hd rows :: transpose (List.map List.tl rows)

(** Transposed matrix times vector *)
let mat_transpose_vec_mult a v = mat_vec_mult (transpose a) v

(** Concatenate vectors *)
let vec_concat = (@)

(** Split vector at position *)
let split_vec n v =
  let rec aux i acc = function
    | [] -> (List.rev acc, [])
    | x :: xs when i > 0 -> aux (i - 1) (x :: acc) xs
    | xs -> (List.rev acc, xs)
  in aux n [] v
