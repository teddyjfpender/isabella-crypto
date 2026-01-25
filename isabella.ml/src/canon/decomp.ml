(** Gadget decomposition for lattice cryptography
    Generated from Canon/Gadgets/Decomp.thy *)

(** Extract i-th digit in base B representation *)
let digit b i x =
  let rec pow base exp = if exp = 0 then 1 else base * pow base (exp - 1) in
  (x / pow b i) mod b

(** Decompose x into k digits in base B *)
let rec decomp_base b k x =
  if k = 0 then []
  else (x mod b) :: decomp_base b (k - 1) (x / b)

(** Recompose digits back to integer *)
let rec recompose b = function
  | [] -> 0
  | d :: ds -> d + b * recompose b ds

(** Gadget vector: [1, B, B^2, ..., B^{k-1}] *)
let gadget_vec b k =
  let rec pow base exp = if exp = 0 then 1 else base * pow base (exp - 1) in
  List.init k (fun i -> pow b i)

(** Signed digit: centered in (-B/2, B/2] *)
let digit_signed b i x =
  let d = digit b i x in
  if 2 * d > b then d - b else d

(** Signed decomposition: digits in (-B/2, B/2] *)
let decomp_signed b k x =
  List.init k (fun i -> digit_signed b i x)
