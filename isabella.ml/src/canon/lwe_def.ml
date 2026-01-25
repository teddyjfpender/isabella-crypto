(** Learning With Errors (LWE) problem definition
    Generated from Canon/Hardness/LWE_Def.thy *)

(** LWE parameters *)
type lwe_params = {
  lwe_n : int;   (** Dimension of secret *)
  lwe_m : int;   (** Number of samples *)
  lwe_q : int;   (** Modulus *)
  lwe_Bs : int;  (** Bound on secret *)
  lwe_Be : int;  (** Bound on error *)
}

let make_lwe_params n m q bs be = { lwe_n = n; lwe_m = m; lwe_q = q; lwe_Bs = bs; lwe_Be = be }

let valid_lwe_params p =
  p.lwe_n > 0 && p.lwe_m > 0 && p.lwe_q > 1 && p.lwe_Bs >= 0 && p.lwe_Be >= 0

(** LWE instance *)
type lwe_instance = {
  lwe_A : int list list;
  lwe_b : int list;
}

let valid_lwe_instance p inst =
  Listvec.valid_matrix p.lwe_m p.lwe_n inst.lwe_A &&
  Listvec.valid_vec p.lwe_m inst.lwe_b

(** Generate LWE sample: b = A*s + e mod q *)
let lwe_sample a s e q =
  Zq.vec_mod (Listvec.vec_add (Listvec.mat_vec_mult a s) e) q

let make_lwe_instance a s e q =
  { lwe_A = a; lwe_b = lwe_sample a s e q }

let valid_secret p s =
  Listvec.valid_vec p.lwe_n s && Norms.all_bounded s p.lwe_Bs

let valid_error p e =
  Listvec.valid_vec p.lwe_m e && Norms.all_bounded e p.lwe_Be

let lwe_residual inst s q =
  Zq.vec_mod (Listvec.vec_sub inst.lwe_b (Listvec.mat_vec_mult inst.lwe_A s)) q

let lwe_witness_valid p inst s e =
  valid_secret p s && valid_error p e &&
  inst.lwe_b = lwe_sample inst.lwe_A s e p.lwe_q
