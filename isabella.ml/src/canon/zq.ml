(** Modular arithmetic for Z_q
    Generated from Canon/Algebra/Zq.thy *)

(** Centered modular reduction: maps to (-q/2, q/2] *)
let mod_centered x q =
  let r = x mod q in
  if r > q / 2 then r - q else r

(** Apply mod to each element of a vector *)
let vec_mod v q = List.map (fun x -> x mod q) v

(** Apply centered mod to each element *)
let vec_mod_centered v q = List.map (fun x -> mod_centered x q) v

(** Distance from zero in Z_q *)
let dist0 q x = abs (mod_centered x q)

(** Encode a bit as 0 or q/2 *)
let encode_bit q b = if b then q / 2 else 0

(** Decode based on distance from zero *)
let decode_bit q x = dist0 q x > q / 4

(** Inner product helper *)
let inner_prod xs ys =
  List.fold_left2 (fun acc x y -> acc + x * y) 0 xs ys

(** Matrix-vector multiplication *)
let mat_vec_mult a v = List.map (inner_prod v) a

(** Matrix-vector multiplication mod q *)
let mat_vec_mult_mod a v q = vec_mod (mat_vec_mult a v) q
