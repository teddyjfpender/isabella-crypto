(** Modular arithmetic for Z_q

    This module provides operations for working with integers modulo q,
    with a focus on centered representation used in lattice cryptography.

    Generated from [Canon/Algebra/Zq.thy] *)

(** {1 Centered Modular Reduction} *)

(** [mod_centered x q] computes centered modular reduction, mapping x to (-q/2, q/2].

    This is the standard representation for LWE error terms, as it
    minimizes the absolute value of the representative.

    {b Properties (proven in Isabelle):}
    - [mod_centered x q mod q = x mod q]
    - [|mod_centered x q| <= q / 2]
    - [mod_centered 0 q = 0] (for q > 0) *)
let mod_centered x q =
  let r = x mod q in
  let r = if r < 0 then r + q else r in  (* ensure positive representative *)
  if r > q / 2 then r - q else r

(** {1 Vector Modular Operations} *)

(** [vec_mod v q] applies standard modular reduction to each element. *)
let vec_mod v q =
  List.map (fun x ->
    let r = x mod q in
    if r < 0 then r + q else r
  ) v

(** [vec_mod_centered v q] applies centered modular reduction to each element. *)
let vec_mod_centered v q = List.map (fun x -> mod_centered x q) v

(** {1 Distance from Zero} *)

(** [dist0 q x] computes the distance from zero in Z_q.

    This is the absolute value of the centered representative, used to
    determine how "close" a value is to zero in the ring Z_q.

    {b Properties (proven in Isabelle):}
    - [dist0 q x >= 0]
    - [dist0 q x <= q / 2]
    - [dist0 q 0 = 0] (for q > 0)
    - [dist0 q (x mod q) = dist0 q x] *)
let dist0 q x = abs (mod_centered x q)

(** {1 Bit Encoding/Decoding for LWE} *)

(** [encode_bit q b] encodes a boolean as an element of Z_q.

    - [false] encodes to 0
    - [true] encodes to q/2 *)
let encode_bit q b = if b then q / 2 else 0

(** [decode_bit q x] decodes an element of Z_q to a boolean.

    Returns [true] if the distance from zero exceeds q/4.

    {b Properties (proven in Isabelle):}
    - [decode_bit q (encode_bit q b) = b] (for q > 2)
    - If [|x| < q / 4] then [decode_bit q x = false]
    - If [q mod 4 = 0] and [|x| < q / 4] then [decode_bit q (x + q / 2) = true] *)
let decode_bit q x = dist0 q x > q / 4

(** {1 Matrix Operations} *)

(** [inner_prod xs ys] computes the inner product of two vectors. *)
let inner_prod xs ys =
  List.fold_left2 (fun acc x y -> acc + x * y) 0 xs ys

(** [mat_vec_mult a v] computes matrix-vector multiplication A * v. *)
let mat_vec_mult a v = List.map (inner_prod v) a

(** [mat_vec_mult_mod a v q] computes matrix-vector multiplication modulo q. *)
let mat_vec_mult_mod a v q = vec_mod (mat_vec_mult a v) q
