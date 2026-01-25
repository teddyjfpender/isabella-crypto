(** Short Integer Solution (SIS) problem definition
    Generated from Canon/Hardness/SIS_Def.thy *)

(** SIS parameters *)
type sis_params = {
  sis_n : int;
  sis_m : int;
  sis_q : int;
  sis_beta : int;
}

let make_sis_params n m q beta = { sis_n = n; sis_m = m; sis_q = q; sis_beta = beta }

let valid_sis_params p =
  p.sis_n > 0 && p.sis_m > 0 && p.sis_q > 1 && p.sis_beta > 0

(** SIS instance *)
type sis_instance = {
  sis_A : int list list;
}

let valid_sis_instance p inst = Listvec.valid_matrix p.sis_m p.sis_n inst.sis_A

let is_zero_vec v = List.for_all ((=) 0) v

let is_sis_solution p inst z =
  Listvec.valid_vec p.sis_n z &&
  not (is_zero_vec z) &&
  Norms.all_bounded z p.sis_beta &&
  is_zero_vec (Zq.vec_mod (Listvec.mat_vec_mult inst.sis_A z) p.sis_q)

let in_kernel_mod a z q = is_zero_vec (Zq.vec_mod (Listvec.mat_vec_mult a z) q)

(** ISIS instance *)
type isis_instance = {
  isis_sis : sis_instance;
  isis_t : int list;
}

let valid_isis_instance p inst =
  valid_sis_instance p inst.isis_sis &&
  Listvec.valid_vec p.sis_m inst.isis_t

let is_isis_solution p inst z =
  Listvec.valid_vec p.sis_n z &&
  Norms.all_bounded z p.sis_beta &&
  Zq.vec_mod (Listvec.mat_vec_mult inst.isis_sis.sis_A z) p.sis_q =
  Zq.vec_mod inst.isis_t p.sis_q
