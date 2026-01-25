(** SIS-based commitment scheme
    Generated from Canon/Crypto/Commit_SIS.thy *)

type commit_params = {
  cp_n1 : int;
  cp_n2 : int;
  cp_m : int;
  cp_q : int;
  cp_beta : int;
}

let make_commit_params n1 n2 m q beta = { cp_n1 = n1; cp_n2 = n2; cp_m = m; cp_q = q; cp_beta = beta }

let valid_commit_params p =
  p.cp_n1 > 0 && p.cp_n2 > 0 && p.cp_m > 0 && p.cp_q > 1 && p.cp_beta > 0

let commit_total_dim p = p.cp_n1 + p.cp_n2

let valid_commit_key p a = Listvec.valid_matrix p.cp_m (commit_total_dim p) a

type commit_opening = { open_msg : int list; open_rand : int list }

let make_opening msg rand = { open_msg = msg; open_rand = rand }

let opening_vec op = op.open_msg @ op.open_rand

let valid_opening p op =
  Listvec.valid_vec p.cp_n1 op.open_msg &&
  Listvec.valid_vec p.cp_n2 op.open_rand &&
  Norms.all_bounded (opening_vec op) p.cp_beta

let commit a op q = Zq.vec_mod (Listvec.mat_vec_mult a (opening_vec op)) q

let verify_opening a op c q = commit a op q = c

let is_binding_break a op1 op2 c q =
  verify_opening a op1 c q &&
  verify_opening a op2 c q &&
  opening_vec op1 <> opening_vec op2

let binding_to_sis_witness op1 op2 = Listvec.vec_sub (opening_vec op1) (opening_vec op2)
