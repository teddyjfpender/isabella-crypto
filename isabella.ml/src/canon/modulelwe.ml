(** Module-LWE and Module-SIS definitions
    Generated from Canon/Rings/ModuleLWE.thy *)

type mod_elem = Polymod.poly list
type mod_matrix = Polymod.poly list list

let valid_mod_elem k n v =
  List.length v = k && List.for_all (fun p -> List.length p = n) v

let valid_mod_matrix k kp n m =
  List.length m = k &&
  List.for_all (fun row ->
    List.length row = kp && List.for_all (fun p -> List.length p = n) row) m

let mod_inner_prod u v n q =
  let products = List.map2 (fun a b -> Polymod.ring_mult a b n q) u v in
  let zero = List.init n (fun _ -> 0) in
  List.fold_left (fun acc p -> Polymod.ring_add acc p n q) zero products

let mod_mat_vec_mult m v n q =
  List.map (fun row -> mod_inner_prod row v n q) m

let mod_add u v n q = List.map2 (fun a b -> Polymod.ring_add a b n q) u v
let mod_sub u v n q = List.map2 (fun a b -> Polymod.ring_sub a b n q) u v

(** M-LWE parameters *)
type mlwe_params = {
  mlwe_n : int;
  mlwe_k : int;
  mlwe_kp : int;
  mlwe_q : int;
  mlwe_eta : int;
}

let make_mlwe_params n k kp q eta = { mlwe_n = n; mlwe_k = k; mlwe_kp = kp; mlwe_q = q; mlwe_eta = eta }

let valid_mlwe_params p =
  p.mlwe_n > 0 && p.mlwe_k > 0 && p.mlwe_kp > 0 && p.mlwe_q > 1 && p.mlwe_eta >= 0

type mlwe_instance = { mlwe_A : mod_matrix; mlwe_b : mod_elem }

let valid_mlwe_instance p inst =
  valid_mod_matrix p.mlwe_kp p.mlwe_k p.mlwe_n inst.mlwe_A &&
  valid_mod_elem p.mlwe_kp p.mlwe_n inst.mlwe_b

let mlwe_sample a s e n q = mod_add (mod_mat_vec_mult a s n q) e n q

let poly_coeffs_bounded p eta = Norms.all_bounded p eta
let mod_elem_small v eta = List.for_all (fun p -> poly_coeffs_bounded p eta) v

let valid_mlwe_secret p s = valid_mod_elem p.mlwe_k p.mlwe_n s && mod_elem_small s p.mlwe_eta
let valid_mlwe_error p e = valid_mod_elem p.mlwe_kp p.mlwe_n e && mod_elem_small e p.mlwe_eta

let mlwe_witness_valid p inst s e =
  valid_mlwe_secret p s && valid_mlwe_error p e &&
  inst.mlwe_b = mlwe_sample inst.mlwe_A s e p.mlwe_n p.mlwe_q

(** M-SIS parameters *)
type msis_params = {
  msis_n : int;
  msis_k : int;
  msis_m : int;
  msis_q : int;
  msis_beta : int;
}

let make_msis_params n k m q beta = { msis_n = n; msis_k = k; msis_m = m; msis_q = q; msis_beta = beta }

let valid_msis_params p =
  p.msis_n > 0 && p.msis_k > 0 && p.msis_m > 0 && p.msis_q > 1 && p.msis_beta > 0

type msis_instance = { msis_A : mod_matrix }

let valid_msis_instance p inst = valid_mod_matrix p.msis_k p.msis_m p.msis_n inst.msis_A

let is_zero_mod_elem v = List.for_all (List.for_all ((=) 0)) v

let is_msis_solution p inst z =
  valid_mod_elem p.msis_m p.msis_n z &&
  not (is_zero_mod_elem z) &&
  mod_elem_small z p.msis_beta &&
  is_zero_mod_elem (mod_mat_vec_mult inst.msis_A z p.msis_n p.msis_q)
