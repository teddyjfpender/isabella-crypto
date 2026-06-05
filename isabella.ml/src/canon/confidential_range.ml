(** Confidential range proof helpers
    Derived from the verified Canon/ZK/Confidential_Range theory.

    This module keeps the SDK surface native and deterministic while remaining
    a thin composition layer over Isabelle-exported Canon modules. *)

type scalar_commit_params = Commit_sis.commit_params
type commit_opening = Commit_sis.commit_opening

type range_proof = {
  range_bits : int list list;
  range_comps : int list list;
  range_amount_as : int list list;
  range_amount_zs : int list list;
  range_pair_ass : int list list list;
  range_pair_zss : int list list list;
}

let make_range_proof range_bits range_comps range_amount_as range_amount_zs range_pair_ass range_pair_zss =
  { range_bits; range_comps; range_amount_as; range_amount_zs; range_pair_ass; range_pair_zss }

let one_opening p =
  Commit_sis.make_opening [1] (List.init p.Commit_sis.cp_n2 (fun _ -> 0))

let opening_scale k op =
  Commit_sis.make_opening
    (Listvec.scalar_mult k op.Commit_sis.open_msg)
    (Listvec.scalar_mult k op.Commit_sis.open_rand)

let valid_bit_opening p op =
  Confidential_balance.valid_scalar_commit_params p &&
  Commit_sis.valid_opening p op &&
  Norms.all_bounded op.Commit_sis.open_msg 1

let bit_pair_relation p op_bit op_comp =
  valid_bit_opening p op_bit &&
  valid_bit_opening p op_comp &&
  Confidential_balance.amount_of_opening op_bit +
  Confidential_balance.amount_of_opening op_comp = 1

let rec all_bit_pairs p ops_bits ops_comps =
  match ops_bits, ops_comps with
  | [], [] -> true
  | op_bit :: rest_bits, op_comp :: rest_comps ->
      bit_pair_relation p op_bit op_comp && all_bit_pairs p rest_bits rest_comps
  | _ -> false

let rec weighted_opening p b = function
  | [] -> Commit_sis.make_opening [0] (List.init p.Commit_sis.cp_n2 (fun _ -> 0))
  | op :: ops ->
      let rest = weighted_opening p b ops in
      Commit_sis.make_opening
        (Listvec.vec_add op.Commit_sis.open_msg (Listvec.scalar_mult b rest.Commit_sis.open_msg))
        (Listvec.vec_add op.Commit_sis.open_rand (Listvec.scalar_mult b rest.Commit_sis.open_rand))

let rec weighted_commitment p ck b = function
  | [] -> Confidential_balance.rand_commit p ck (List.init p.Commit_sis.cp_n2 (fun _ -> 0))
  | c :: cs ->
      Zq.vec_mod
        (Listvec.vec_add c (Listvec.scalar_mult b (weighted_commitment p ck b cs)))
        p.Commit_sis.cp_q

let range_amount_opening p op_amount ops_bits =
  let weighted = weighted_opening p 2 ops_bits in
  Commit_sis.make_opening
    (Listvec.vec_sub op_amount.Commit_sis.open_msg weighted.Commit_sis.open_msg)
    (Listvec.vec_sub op_amount.Commit_sis.open_rand weighted.Commit_sis.open_rand)

let range_amount_randomness p op_amount ops_bits =
  (range_amount_opening p op_amount ops_bits).Commit_sis.open_rand

let range_pair_opening p op_bit op_comp =
  let one = one_opening p in
  Commit_sis.make_opening
    (Listvec.vec_sub
       (Listvec.vec_add op_bit.Commit_sis.open_msg op_comp.Commit_sis.open_msg)
       one.Commit_sis.open_msg)
    (Listvec.vec_sub
       (Listvec.vec_add op_bit.Commit_sis.open_rand op_comp.Commit_sis.open_rand)
       one.Commit_sis.open_rand)

let range_pair_randomness p op_bit op_comp =
  (range_pair_opening p op_bit op_comp).Commit_sis.open_rand

let rec range_pair_randomnesses p ops_bits ops_comps =
  match ops_bits, ops_comps with
  | [], [] -> []
  | op_bit :: rest_bits, op_comp :: rest_comps ->
      range_pair_randomness p op_bit op_comp :: range_pair_randomnesses p rest_bits rest_comps
  | _ -> []

let one_commitment p ck =
  Commit_sis.commit ck (one_opening p) p.Commit_sis.cp_q

let range_amount_commitment p ck c_amount c_bits =
  Zq.vec_mod
    (Listvec.vec_sub c_amount (weighted_commitment p ck 2 c_bits))
    p.Commit_sis.cp_q

let range_pair_commitment p ck c_bit c_comp =
  Zq.vec_mod
    (Listvec.vec_sub (Listvec.vec_add c_bit c_comp) (one_commitment p ck))
    p.Commit_sis.cp_q

let rec range_pair_commitments p ck c_bits c_comps =
  match c_bits, c_comps with
  | [], [] -> []
  | c_bit :: rest_bits, c_comp :: rest_comps ->
      range_pair_commitment p ck c_bit c_comp :: range_pair_commitments p ck rest_bits rest_comps
  | _ -> []

let range_relation p ck c_amount op_amount ops_bits ops_comps =
  Confidential_balance.valid_scalar_commit_params p &&
  Confidential_balance.valid_confidential_commit_key p ck &&
  Commit_sis.valid_opening p op_amount &&
  Commit_sis.verify_opening ck op_amount c_amount p.Commit_sis.cp_q &&
  all_bit_pairs p ops_bits ops_comps &&
  Confidential_balance.amount_of_opening op_amount =
    Decomp.recompose 2 (List.map Confidential_balance.amount_of_opening ops_bits)

let rec pow_int base exp =
  if exp <= 0 then 1 else base * pow_int base (exp - 1)

let range_amount_witness_bound p k =
  pow_int 2 k * p.Commit_sis.cp_beta

let range_pair_witness_bound p =
  2 * p.Commit_sis.cp_beta

let valid_range_amount_witness p k r =
  Listvec.valid_vec p.Commit_sis.cp_n2 r &&
  Norms.all_bounded r (range_amount_witness_bound p k)

let valid_range_pair_witness p r =
  Listvec.valid_vec p.Commit_sis.cp_n2 r &&
  Norms.all_bounded r (range_pair_witness_bound p)

let valid_range_mask p gamma y =
  Listvec.valid_vec p.Commit_sis.cp_n2 y &&
  Norms.all_bounded y gamma

let range_amount_response_bound p gamma k challenge =
  gamma + (abs challenge * range_amount_witness_bound p k)

let range_pair_response_bound p gamma challenge =
  gamma + (abs challenge * range_pair_witness_bound p)

let valid_range_challenge = Confidential_balance.valid_balance_challenge

let valid_range_amount_response p gamma k challenge z =
  Listvec.valid_vec p.Commit_sis.cp_n2 z &&
  Norms.all_bounded z (range_amount_response_bound p gamma k challenge)

let valid_range_pair_response p gamma challenge z =
  Listvec.valid_vec p.Commit_sis.cp_n2 z &&
  Norms.all_bounded z (range_pair_response_bound p gamma challenge)

let valid_range_masks p gamma ys =
  List.for_all (valid_range_mask p gamma) ys

let valid_range_pair_responses p gamma challenge zs =
  List.for_all (valid_range_pair_response p gamma challenge) zs

let range_fs_rounds = Confidential_balance.balance_fs_rounds

let range_fs_challenges _p ck c_amount c_bits c_comps a_amounts a_pairss =
  let sum_list = List.fold_left ( + ) 0 in
  let base =
    sum_list (List.concat ck) +
    sum_list c_amount +
    sum_list (List.concat c_bits) +
    sum_list (List.concat c_comps) +
    sum_list (List.concat a_amounts) +
    sum_list (List.concat (List.concat a_pairss))
  in
  Repeated_fs.bool_fs_challenges base

let range_amount_sigma_announcements p ck y_amounts =
  List.map (Confidential_balance.rand_commit p ck) y_amounts

let range_amount_sigma_responses r_amount y_amounts challenges =
  Repeated_fs.sigma_response_rounds Confidential_balance.balance_sigma_respond r_amount y_amounts challenges

let range_sigma_announcements p ck ys =
  List.map (Confidential_balance.rand_commit p ck) ys

let rec range_sigma_responses rs ys challenge =
  match rs, ys with
  | [], [] -> []
  | r :: rest_rs, y :: rest_ys ->
      Confidential_balance.balance_sigma_respond r y challenge ::
      range_sigma_responses rest_rs rest_ys challenge
  | _ -> []

let range_pair_sigma_announcement_rounds p ck y_pairss =
  List.map (range_sigma_announcements p ck) y_pairss

let range_pair_sigma_response_rounds rs y_pairss challenges =
  Repeated_fs.sigma_response_rounds range_sigma_responses rs y_pairss challenges

let canonical_range_challenge _p ck c_amount c_bits c_comps a_amounts a_pairss =
  let sum_list = List.fold_left ( + ) 0 in
  (sum_list (List.concat ck) +
   sum_list c_amount +
   sum_list (List.concat c_bits) +
   sum_list (List.concat c_comps) +
   sum_list (List.concat a_amounts) +
   sum_list (List.concat (List.concat a_pairss))) mod 2

let range_amount_sigma_verify p gamma k ck c a challenge z =
  Confidential_balance.valid_scalar_commit_params p &&
  Confidential_balance.valid_confidential_commit_key p ck &&
  Listvec.valid_vec p.Commit_sis.cp_m a &&
  valid_range_challenge p challenge &&
  valid_range_amount_response p gamma k challenge z &&
  Confidential_balance.rand_commit p ck z =
    Zq.vec_mod (Listvec.vec_add a (Listvec.scalar_mult challenge c)) p.Commit_sis.cp_q

let range_pair_sigma_verify p gamma ck c a challenge z =
  Confidential_balance.valid_scalar_commit_params p &&
  Confidential_balance.valid_confidential_commit_key p ck &&
  Listvec.valid_vec p.Commit_sis.cp_m a &&
  valid_range_challenge p challenge &&
  valid_range_pair_response p gamma challenge z &&
  Confidential_balance.rand_commit p ck z =
    Zq.vec_mod (Listvec.vec_add a (Listvec.scalar_mult challenge c)) p.Commit_sis.cp_q

let rec range_sigma_verify_pairs p gamma ck cs as_ challenge zs =
  match cs, as_, zs with
  | [], [], [] -> true
  | c :: rest_cs, a :: rest_as, z :: rest_zs ->
      range_pair_sigma_verify p gamma ck c a challenge z &&
      range_sigma_verify_pairs p gamma ck rest_cs rest_as challenge rest_zs
  | _ -> false

let range_fs_prove p gamma k ck c_amount op_amount ops_bits ops_comps y_amounts y_pairss =
  let c_bits = List.map (fun op -> Commit_sis.commit ck op p.Commit_sis.cp_q) ops_bits in
  let c_comps = List.map (fun op -> Commit_sis.commit ck op p.Commit_sis.cp_q) ops_comps in
  let r_amount = range_amount_randomness p op_amount ops_bits in
  let r_pairs = range_pair_randomnesses p ops_bits ops_comps in
  let a_amounts = range_amount_sigma_announcements p ck y_amounts in
  let a_pairss = range_pair_sigma_announcement_rounds p ck y_pairss in
  let challenges = range_fs_challenges p ck c_amount c_bits c_comps a_amounts a_pairss in
  let z_amounts = range_amount_sigma_responses r_amount y_amounts challenges in
  let z_pairss = range_pair_sigma_response_rounds r_pairs y_pairss challenges in
  if range_relation p ck c_amount op_amount ops_bits ops_comps &&
     List.length ops_bits = k &&
     List.length ops_comps = k &&
     List.length y_amounts = range_fs_rounds &&
     List.length y_pairss = range_fs_rounds &&
     List.for_all (valid_range_mask p gamma) y_amounts &&
     List.for_all
       (fun ys -> List.length ys = k && valid_range_masks p gamma ys)
       y_pairss &&
     List.for_all2
       (valid_range_amount_response p gamma k)
       challenges
       z_amounts &&
     List.for_all2
       (fun challenge zs ->
         List.length zs = k &&
         valid_range_pair_responses p gamma challenge zs)
       challenges
       z_pairss
  then Some (make_range_proof c_bits c_comps a_amounts z_amounts a_pairss z_pairss)
  else None

let range_fs_verify p gamma k ck c_amount proof =
  let c_bits = proof.range_bits in
  let c_comps = proof.range_comps in
  let a_amounts = proof.range_amount_as in
  let a_pairss = proof.range_pair_ass in
  let z_amounts = proof.range_amount_zs in
  let z_pairss = proof.range_pair_zss in
  let challenges = range_fs_challenges p ck c_amount c_bits c_comps a_amounts a_pairss in
  let c_amount_res = range_amount_commitment p ck c_amount c_bits in
  let c_pair_res = range_pair_commitments p ck c_bits c_comps in
  Listvec.valid_vec p.Commit_sis.cp_m c_amount &&
  List.length c_bits = k &&
  List.length c_comps = k &&
  List.length a_amounts = range_fs_rounds &&
  List.length a_pairss = range_fs_rounds &&
  List.length z_amounts = range_fs_rounds &&
  List.length z_pairss = range_fs_rounds &&
  List.for_all2
    (fun ((a_amount, a_pairs), challenge) (z_amount, z_pairs) ->
      List.length a_pairs = k &&
      List.length z_pairs = k &&
      range_amount_sigma_verify p gamma k ck c_amount_res a_amount challenge z_amount &&
      range_sigma_verify_pairs p gamma ck c_pair_res a_pairs challenge z_pairs)
    (List.combine (List.combine a_amounts a_pairss) challenges)
    (List.combine z_amounts z_pairss)
