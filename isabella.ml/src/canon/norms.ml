(** Vector norms and bounds
    Generated from Canon/Analysis/Norms.thy *)

(** L-infinity norm: maximum absolute value of elements *)
let linf_norm v =
  if v = [] then 0
  else List.fold_left max 0 (List.map abs v)

(** Check if all elements are bounded by B in absolute value *)
let all_bounded v b = List.for_all (fun x -> abs x <= b) v
