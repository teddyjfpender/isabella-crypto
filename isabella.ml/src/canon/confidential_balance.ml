(** Confidential balance proof helpers
    Derived from the verified Canon/ZK/Confidential_Balance theory.

    This module keeps the SDK surface native and deterministic while remaining
    a thin composition layer over Isabelle-exported Canon modules. *)

type scalar_commit_params = Commit_sis.commit_params
type commit_opening = Commit_sis.commit_opening

type balance_proof = {
  balance_as : int list list;
  balance_zs : int list list;
}

let make_balance_proof balance_as balance_zs = { balance_as; balance_zs }

let balance_fs_rounds = Repeated_fs.fixed_fs_rounds

let make_scalar_commit_params m n2 q beta =
  Commit_sis.make_commit_params 1 n2 m q beta

let valid_scalar_commit_params p =
  Commit_sis.valid_commit_params p && p.Commit_sis.cp_n1 = 1

let valid_confidential_commit_key p ck =
  Commit_sis.separating_commit_key p ck

let rand_commit_key p ck =
  List.map (fun row -> snd (Listvec.split_vec p.Commit_sis.cp_n1 row)) ck

let rand_commit p ck r =
  Zq.vec_mod (Listvec.mat_vec_mult (rand_commit_key p ck) r) p.Commit_sis.cp_q

let amount_of_opening op =
  match op.Commit_sis.open_msg with
  | x :: _ -> x
  | [] -> 0

let opening_add op1 op2 =
  Commit_sis.make_opening
    (Listvec.vec_add op1.Commit_sis.open_msg op2.Commit_sis.open_msg)
    (Listvec.vec_add op1.Commit_sis.open_rand op2.Commit_sis.open_rand)

let opening_sub op1 op2 =
  Commit_sis.make_opening
    (Listvec.vec_sub op1.Commit_sis.open_msg op2.Commit_sis.open_msg)
    (Listvec.vec_sub op1.Commit_sis.open_rand op2.Commit_sis.open_rand)

let aggregate_opening op_in1 op_in2 op_out1 op_out2 =
  opening_sub (opening_add op_in1 op_in2) (opening_add op_out1 op_out2)

let aggregate_randomness op_in1 op_in2 op_out1 op_out2 =
  (aggregate_opening op_in1 op_in2 op_out1 op_out2).Commit_sis.open_rand

let balance_commitment c_in1 c_in2 c_out1 c_out2 q =
  Zq.vec_mod
    (Listvec.vec_sub (Listvec.vec_add c_in1 c_in2) (Listvec.vec_add c_out1 c_out2))
    q

let valid_balance_witness p r =
  Listvec.valid_vec p.Commit_sis.cp_n2 r &&
  Norms.all_bounded r (4 * p.Commit_sis.cp_beta)

let valid_balance_mask p gamma y =
  Listvec.valid_vec p.Commit_sis.cp_n2 y && Norms.all_bounded y gamma

let balance_response_bound p gamma challenge =
  gamma + (abs challenge * (4 * p.Commit_sis.cp_beta))

let valid_balance_challenge p challenge =
  valid_scalar_commit_params p &&
  (challenge = 0 || challenge = 1)

let valid_balance_response p gamma challenge z =
  Listvec.valid_vec p.Commit_sis.cp_n2 z &&
  Norms.all_bounded z (balance_response_bound p gamma challenge)

let balance_relation p ck c r =
  valid_scalar_commit_params p &&
  valid_confidential_commit_key p ck &&
  valid_balance_witness p r &&
  rand_commit p ck r = c

let balance_sigma_commit = rand_commit

let balance_sigma_respond r y challenge =
  Listvec.vec_add y (Listvec.scalar_mult challenge r)

let sum_list = List.fold_left ( + ) 0

let canonical_balance_challenge _p ck c a =
  (sum_list (List.concat ck) + sum_list c + sum_list a) mod 2

let balance_sigma_verify p gamma ck c a challenge z =
  valid_scalar_commit_params p &&
  valid_confidential_commit_key p ck &&
  Listvec.valid_vec p.Commit_sis.cp_m a &&
  valid_balance_challenge p challenge &&
  valid_balance_response p gamma challenge z &&
  rand_commit p ck z =
    Zq.vec_mod (Listvec.vec_add a (Listvec.scalar_mult challenge c)) p.Commit_sis.cp_q

let balance_fs_challenges _p ck c as_ =
  Repeated_fs.bool_fs_challenges
    (sum_list (List.concat ck) + sum_list c + sum_list (List.concat as_))

let balance_sigma_responds r ys es =
  Repeated_fs.sigma_response_rounds balance_sigma_respond r ys es

let balance_fs_prove p gamma ck c r ys =
  let as_ = List.map (balance_sigma_commit p ck) ys in
  let es = balance_fs_challenges p ck c as_ in
  let zs = balance_sigma_responds r ys es in
  if balance_relation p ck c r &&
     List.length ys = balance_fs_rounds &&
     List.for_all (valid_balance_mask p gamma) ys &&
     List.for_all2 (fun e z -> valid_balance_response p gamma e z) es zs
  then Some { balance_as = as_; balance_zs = zs }
  else None

let balance_fs_verify p gamma ck c proof =
  let as_ = proof.balance_as in
  let es = balance_fs_challenges p ck c as_ in
  let zs = proof.balance_zs in
  List.length as_ = balance_fs_rounds &&
  List.length zs = balance_fs_rounds &&
  List.for_all2
    (fun a (e, z) -> balance_sigma_verify p gamma ck c a e z)
    as_
    (List.combine es zs)
