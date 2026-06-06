(** JavaScript bindings for Isabella Canon library

    This module exposes the verified Canon functions to JavaScript
    via js_of_ocaml. All functions maintain the same semantics as
    their OCaml counterparts.

    Provenance: Wrapper over Isabelle-exported Canon modules only. *)

open Js_of_ocaml
open Canon

(** Convert OCaml int to JS number payload *)
let js_int x = Js.Unsafe.inject (Js.number_of_float (float_of_int x))

(** Convert JS array to OCaml int list *)
let js_array_to_list arr =
  let len = arr##.length in
  let rec aux i acc =
    if i < 0 then acc
    else aux (i - 1) ((Js.to_float (Js.Unsafe.get arr i) |> int_of_float) :: acc)
  in
  aux (len - 1) []

(** Convert OCaml int list to JS array *)
let list_to_js_array lst =
  let arr = new%js Js.array_empty in
  List.iter (fun x -> ignore (arr##push (Js.number_of_float (float_of_int x)))) lst;
  arr

(** Convert JS 2D array to OCaml int list list *)
let js_matrix_to_list mat =
  let len = mat##.length in
  let rec aux i acc =
    if i < 0 then acc
    else
      let row = Js.Unsafe.get mat i in
      aux (i - 1) (js_array_to_list row :: acc)
  in
  aux (len - 1) []

(** Convert OCaml int list list to JS 2D array *)
let list_to_js_matrix mat =
  let arr = new%js Js.array_empty in
  List.iter (fun row -> ignore (arr##push (list_to_js_array row))) mat;
  arr

let js_cube_to_list cube =
  let len = cube##.length in
  let rec aux i acc =
    if i < 0 then acc
    else
      let plane = Js.Unsafe.get cube i in
      aux (i - 1) (js_matrix_to_list plane :: acc)
  in
  aux (len - 1) []

let list_to_js_cube cube =
  let arr = new%js Js.array_empty in
  List.iter (fun plane -> ignore (arr##push (list_to_js_matrix plane))) cube;
  arr

let bool_list_to_js_array lst =
  let arr = new%js Js.array_empty in
  List.iter (fun x -> ignore (arr##push (Js.bool x))) lst;
  arr

let js_bool_array_to_list arr =
  let len = arr##.length in
  let rec aux i acc =
    if i < 0 then acc
    else aux (i - 1) (Js.to_bool (Js.Unsafe.get arr i) :: acc)
  in
  aux (len - 1) []

let pair_to_js left_name right_name (left, right) =
  Js.Unsafe.obj
    [|
      (left_name, js_int left);
      (right_name, js_int right);
    |]

let dilithium_params_to_js params =
  Js.Unsafe.obj
    [|
      ("n", js_int params.Dilithium.dil_n);
      ("q", js_int params.Dilithium.dil_q);
      ("k", js_int params.Dilithium.dil_k);
      ("l", js_int params.Dilithium.dil_l);
      ("eta", js_int params.Dilithium.dil_eta);
      ("tau", js_int params.Dilithium.dil_tau);
      ("beta", js_int params.Dilithium.dil_beta);
      ("gamma1", js_int params.Dilithium.dil_gamma1);
      ("gamma2", js_int params.Dilithium.dil_gamma2);
      ("d", js_int params.Dilithium.dil_d);
      ("omega", js_int params.Dilithium.dil_omega);
    |]

let js_obj_int obj field =
  Js.to_float (Js.Unsafe.get obj field) |> int_of_float

let cb_params_to_js params =
  Js.Unsafe.obj
    [|
      ("n1", js_int params.Commit_sis.cp_n1);
      ("n2", js_int params.Commit_sis.cp_n2);
      ("m", js_int params.Commit_sis.cp_m);
      ("q", js_int params.Commit_sis.cp_q);
      ("beta", js_int params.Commit_sis.cp_beta);
    |]

let cb_params_of_js params =
  Commit_sis.make_commit_params
    (js_obj_int params "n1")
    (js_obj_int params "n2")
    (js_obj_int params "m")
    (js_obj_int params "q")
    (js_obj_int params "beta")

let cb_opening_of_js opening =
  Commit_sis.make_opening
    (js_array_to_list (Js.Unsafe.get opening "msg"))
    (js_array_to_list (Js.Unsafe.get opening "rand"))

let js_openings_to_list openings =
  let len = openings##.length in
  let rec aux i acc =
    if i < 0 then acc
    else
      let opening = Js.Unsafe.get openings i in
      aux (i - 1) (cb_opening_of_js opening :: acc)
  in
  aux (len - 1) []

let cb_proof_to_js proof =
  Js.Unsafe.obj
    [|
      ("as", Js.Unsafe.inject (list_to_js_matrix proof.Confidential_balance.balance_as));
      ("zs", Js.Unsafe.inject (list_to_js_matrix proof.Confidential_balance.balance_zs));
    |]

let cb_proof_of_js proof =
  Confidential_balance.make_balance_proof
    (js_matrix_to_list (Js.Unsafe.get proof "as"))
    (js_matrix_to_list (Js.Unsafe.get proof "zs"))

let cr_proof_to_js proof =
  Js.Unsafe.obj
    [|
      ("bits", Js.Unsafe.inject (list_to_js_matrix proof.Confidential_range.range_bits));
      ("comps", Js.Unsafe.inject (list_to_js_matrix proof.Confidential_range.range_comps));
      ("amountAs", Js.Unsafe.inject (list_to_js_matrix proof.Confidential_range.range_amount_as));
      ("amountZs", Js.Unsafe.inject (list_to_js_matrix proof.Confidential_range.range_amount_zs));
      ("pairAss", Js.Unsafe.inject (list_to_js_cube proof.Confidential_range.range_pair_ass));
      ("pairZss", Js.Unsafe.inject (list_to_js_cube proof.Confidential_range.range_pair_zss));
    |]

let cr_proof_of_js proof =
  Confidential_range.make_range_proof
    (js_matrix_to_list (Js.Unsafe.get proof "bits"))
    (js_matrix_to_list (Js.Unsafe.get proof "comps"))
    (js_matrix_to_list (Js.Unsafe.get proof "amountAs"))
    (js_matrix_to_list (Js.Unsafe.get proof "amountZs"))
    (js_cube_to_list (Js.Unsafe.get proof "pairAss"))
    (js_cube_to_list (Js.Unsafe.get proof "pairZss"))

let ct_nullifier_proof_to_js proof =
  Js.Unsafe.obj
    [|
      ("aCommits", Js.Unsafe.inject (list_to_js_matrix proof.Confidential_transaction.nullifier_a_commits));
      ("aNullifiers", Js.Unsafe.inject (list_to_js_matrix proof.Confidential_transaction.nullifier_a_nullifiers));
      ("zMsgs", Js.Unsafe.inject (list_to_js_matrix proof.Confidential_transaction.nullifier_z_msgs));
      ("zRands", Js.Unsafe.inject (list_to_js_matrix proof.Confidential_transaction.nullifier_z_rands));
    |]

let ct_nullifier_proof_of_js proof =
  Confidential_transaction.make_nullifier_proof
    (js_matrix_to_list (Js.Unsafe.get proof "aCommits"))
    (js_matrix_to_list (Js.Unsafe.get proof "aNullifiers"))
    (js_matrix_to_list (Js.Unsafe.get proof "zMsgs"))
    (js_matrix_to_list (Js.Unsafe.get proof "zRands"))

let ct_membership_proof_to_js proof =
  Js.Unsafe.obj
    [|
      ("index", js_int proof.Confidential_transaction.member_index);
      ("root", Js.Unsafe.inject (list_to_js_array proof.Confidential_transaction.member_root));
      ("siblings", Js.Unsafe.inject (list_to_js_matrix proof.Confidential_transaction.member_siblings));
      ("directions", Js.Unsafe.inject (bool_list_to_js_array proof.Confidential_transaction.member_directions));
    |]

let ct_membership_proof_of_js proof =
  Confidential_transaction.make_membership_proof
    (js_obj_int proof "index")
    (js_array_to_list (Js.Unsafe.get proof "root"))
    (js_matrix_to_list (Js.Unsafe.get proof "siblings"))
    (js_bool_array_to_list (Js.Unsafe.get proof "directions"))

let ct_verified_note_to_js note =
  Js.Unsafe.obj
    [|
      ("commitment", Js.Unsafe.inject (list_to_js_array note.Confidential_transaction.note_commitment));
      ("rangeProof", Js.Unsafe.inject (cr_proof_to_js note.Confidential_transaction.note_range_proof));
    |]

let ct_verified_note_of_js note =
  Confidential_transaction.make_verified_note
    (js_array_to_list (Js.Unsafe.get note "commitment"))
    (cr_proof_of_js (Js.Unsafe.get note "rangeProof"))

let ct_notes_to_js notes =
  let arr = new%js Js.array_empty in
  List.iter (fun note -> ignore (arr##push (ct_verified_note_to_js note))) notes;
  arr

let ct_notes_of_js notes =
  let len = notes##.length in
  let rec aux i acc =
    if i < 0 then acc
    else
      let note = Js.Unsafe.get notes i in
      aux (i - 1) (ct_verified_note_of_js note :: acc)
  in
  aux (len - 1) []

let ct_transaction_proof_to_js proof =
  Js.Unsafe.obj
    [|
      ("in1Member", Js.Unsafe.inject (ct_membership_proof_to_js proof.Confidential_transaction.tx_in1_member));
      ("in2Member", Js.Unsafe.inject (ct_membership_proof_to_js proof.Confidential_transaction.tx_in2_member));
      ("in1Nullifier", Js.Unsafe.inject (ct_nullifier_proof_to_js proof.Confidential_transaction.tx_in1_nullifier));
      ("in2Nullifier", Js.Unsafe.inject (ct_nullifier_proof_to_js proof.Confidential_transaction.tx_in2_nullifier));
      ("balance", Js.Unsafe.inject (cb_proof_to_js proof.Confidential_transaction.tx_balance));
      ("out1Range", Js.Unsafe.inject (cr_proof_to_js proof.Confidential_transaction.tx_out1_range));
      ("out2Range", Js.Unsafe.inject (cr_proof_to_js proof.Confidential_transaction.tx_out2_range));
    |]

let ct_transaction_proof_of_js proof =
  Confidential_transaction.make_transaction_proof
    (ct_membership_proof_of_js (Js.Unsafe.get proof "in1Member"))
    (ct_membership_proof_of_js (Js.Unsafe.get proof "in2Member"))
    (ct_nullifier_proof_of_js (Js.Unsafe.get proof "in1Nullifier"))
    (ct_nullifier_proof_of_js (Js.Unsafe.get proof "in2Nullifier"))
    (cb_proof_of_js (Js.Unsafe.get proof "balance"))
    (cr_proof_of_js (Js.Unsafe.get proof "out1Range"))
    (cr_proof_of_js (Js.Unsafe.get proof "out2Range"))

(** Export the Isabella module to JavaScript *)
let () =
  Js.export "Isabella"
    (object%js
       (** Centered modular reduction *)
       method modCentered x q =
         Zq.mod_centered (int_of_float (Js.to_float x)) (int_of_float (Js.to_float q))
         |> float_of_int |> Js.number_of_float

       (** Vector modular reduction *)
       method vecMod v q =
         let v' = js_array_to_list v in
         let q' = int_of_float (Js.to_float q) in
         Zq.vec_mod v' q' |> list_to_js_array

       (** Centered vector modular reduction *)
       method vecModCentered v q =
         let v' = js_array_to_list v in
         let q' = int_of_float (Js.to_float q) in
         Zq.vec_mod_centered v' q' |> list_to_js_array

       (** Distance from zero in Z_q *)
       method dist0 q x =
         Zq.dist0 (int_of_float (Js.to_float q)) (int_of_float (Js.to_float x))
         |> float_of_int |> Js.number_of_float

       (** Encode a bit for LWE *)
       method encodeBit q b =
         Zq.encode_bit (int_of_float (Js.to_float q)) (Js.to_bool b)
         |> float_of_int |> Js.number_of_float

       (** Decode a bit from LWE *)
       method decodeBit q x =
         Zq.decode_bit (int_of_float (Js.to_float q)) (int_of_float (Js.to_float x))
         |> Js.bool

       (** Vector addition *)
       method vecAdd v1 v2 =
         let v1' = js_array_to_list v1 in
         let v2' = js_array_to_list v2 in
         Listvec.vec_add v1' v2' |> list_to_js_array

       (** Vector subtraction *)
       method vecSub v1 v2 =
         let v1' = js_array_to_list v1 in
         let v2' = js_array_to_list v2 in
         Listvec.vec_sub v1' v2' |> list_to_js_array

       (** Scalar multiplication *)
       method scalarMult c v =
         let c' = int_of_float (Js.to_float c) in
         let v' = js_array_to_list v in
         Listvec.scalar_mult c' v' |> list_to_js_array

       (** Vector negation *)
       method vecNeg v =
         let v' = js_array_to_list v in
         Listvec.vec_neg v' |> list_to_js_array

       (** Inner product *)
       method innerProd v1 v2 =
         let v1' = js_array_to_list v1 in
         let v2' = js_array_to_list v2 in
         Listvec.inner_prod v1' v2' |> float_of_int |> Js.number_of_float

       (** Matrix-vector multiplication *)
       method matVecMult mat vec =
         let mat' = js_matrix_to_list mat in
         let vec' = js_array_to_list vec in
         Listvec.mat_vec_mult mat' vec' |> list_to_js_array

       (** Matrix-vector multiplication mod q *)
       method matVecMultMod mat vec q =
         let mat' = js_matrix_to_list mat in
         let vec' = js_array_to_list vec in
         let q' = int_of_float (Js.to_float q) in
         Zq.mat_vec_mult_mod mat' vec' q' |> list_to_js_array

       (** Matrix transpose *)
       method transpose mat =
         let mat' = js_matrix_to_list mat in
         Listvec.transpose mat' |> list_to_js_matrix

       (** Validate vector dimension *)
       method validVec n v =
         let n' = int_of_float (Js.to_float n) in
         let v' = js_array_to_list v in
         Listvec.valid_vec n' v' |> Js.bool

       (** Validate matrix dimensions *)
       method validMatrix m n mat =
         let m' = int_of_float (Js.to_float m) in
         let n' = int_of_float (Js.to_float n) in
         let mat' = js_matrix_to_list mat in
         Listvec.valid_matrix m' n' mat' |> Js.bool

       (** Vector concatenation *)
       method vecConcat v1 v2 =
         let v1' = js_array_to_list v1 in
         let v2' = js_array_to_list v2 in
         Listvec.vec_concat v1' v2' |> list_to_js_array

       (** Split vector at position *)
       method splitVec n v =
         let n' = int_of_float (Js.to_float n) in
         let v' = js_array_to_list v in
         let (left, right) = Listvec.split_vec n' v' in
         let result = new%js Js.array_empty in
         ignore (result##push (list_to_js_array left));
         ignore (result##push (list_to_js_array right));
         result

       (** ML-DSA parameter selection *)
       method dilParams variant =
         let variant' = String.lowercase_ascii (Js.to_string variant) in
         let params =
           match variant' with
           | "44" | "mldsa44" | "ml-dsa-44" -> Dilithium.mldsa44_params
           | "65" | "mldsa65" | "ml-dsa-65" -> Dilithium.mldsa65_params
           | "87" | "mldsa87" | "ml-dsa-87" -> Dilithium.mldsa87_params
           | _ -> invalid_arg ("Unknown ML-DSA variant: " ^ variant')
         in
         dilithium_params_to_js params

       (** Dilithium centered modular reduction *)
       method dilModCentered r m =
         Dilithium.mod_centered
           (int_of_float (Js.to_float r))
           (int_of_float (Js.to_float m))
         |> float_of_int |> Js.number_of_float

       (** Power2Round on a single coefficient *)
       method dilPower2Round r d =
         Dilithium.power2round_coeff
           (int_of_float (Js.to_float r))
           (int_of_float (Js.to_float d))
         |> pair_to_js "r1" "r0"

       (** Decompose on a single coefficient *)
       method dilDecompose r alpha =
         Dilithium.decompose_coeff
           (int_of_float (Js.to_float r))
           (int_of_float (Js.to_float alpha))
         |> pair_to_js "r1" "r0"

       (** Dilithium high bits *)
       method dilHighBits r alpha =
         Dilithium.highbits_coeff
           (int_of_float (Js.to_float r))
           (int_of_float (Js.to_float alpha))
         |> float_of_int |> Js.number_of_float

       (** Dilithium low bits *)
       method dilLowBits r alpha =
         Dilithium.lowbits_coeff
           (int_of_float (Js.to_float r))
           (int_of_float (Js.to_float alpha))
         |> float_of_int |> Js.number_of_float

       (** Dilithium hint creation *)
       method dilMakeHint z r alpha =
         Dilithium.makehint_coeff
           (int_of_float (Js.to_float z))
           (int_of_float (Js.to_float r))
           (int_of_float (Js.to_float alpha))
         |> float_of_int |> Js.number_of_float

       (** Dilithium hint application *)
       method dilUseHint h r alpha =
         Dilithium.usehint_coeff
           (int_of_float (Js.to_float h))
           (int_of_float (Js.to_float r))
           (int_of_float (Js.to_float alpha))
         |> float_of_int |> Js.number_of_float

       (** Dilithium coefficient bound check *)
       method dilCheckBound value bound =
         Dilithium.coeff_in_range
           (int_of_float (Js.to_float value))
           (int_of_float (Js.to_float bound))
         |> Js.bool

       (** Total number of 1s in a hint matrix *)
       method dilHintWeight hints =
         let hints' = js_matrix_to_list hints in
         Dilithium.hint_weight hints' |> float_of_int |> Js.number_of_float

       (** Confidential-balance scalar commitment params *)
       method cbMakeParams m n2 q beta =
         Confidential_balance.make_scalar_commit_params
           (int_of_float (Js.to_float m))
           (int_of_float (Js.to_float n2))
           (int_of_float (Js.to_float q))
           (int_of_float (Js.to_float beta))
         |> cb_params_to_js

       (** Confidential-balance parameter validation *)
       method cbValidScalarParams params =
         Confidential_balance.valid_scalar_commit_params (cb_params_of_js params)
         |> Js.bool

       (** Drop the message columns from a commitment key *)
       method cbRandCommitKey params ck =
         let params' = cb_params_of_js params in
         let ck' = js_matrix_to_list ck in
         Confidential_balance.rand_commit_key params' ck' |> list_to_js_matrix

       (** Commit to aggregate randomness using the randomness-only key *)
       method cbRandCommit params ck r =
         let params' = cb_params_of_js params in
         let ck' = js_matrix_to_list ck in
         let r' = js_array_to_list r in
         Confidential_balance.rand_commit params' ck' r' |> list_to_js_array

       (** Extract the scalar message amount from an opening *)
       method cbAmountOfOpening opening =
         Confidential_balance.amount_of_opening (cb_opening_of_js opening)
         |> float_of_int |> Js.number_of_float

       (** Aggregate randomness from balanced inputs and outputs *)
       method cbAggregateRandomness opIn1 opIn2 opOut1 opOut2 =
         Confidential_balance.aggregate_randomness
           (cb_opening_of_js opIn1)
           (cb_opening_of_js opIn2)
           (cb_opening_of_js opOut1)
           (cb_opening_of_js opOut2)
         |> list_to_js_array

       (** Aggregate commitment difference for zero-balance checking *)
       method cbBalanceCommitment cIn1 cIn2 cOut1 cOut2 q =
         Confidential_balance.balance_commitment
           (js_array_to_list cIn1)
           (js_array_to_list cIn2)
           (js_array_to_list cOut1)
           (js_array_to_list cOut2)
           (int_of_float (Js.to_float q))
         |> list_to_js_array

       (** Witness bound check *)
       method cbValidWitness params r =
         Confidential_balance.valid_balance_witness
           (cb_params_of_js params)
           (js_array_to_list r)
         |> Js.bool

       (** Mask bound check *)
       method cbValidMask params gamma y =
         Confidential_balance.valid_balance_mask
           (cb_params_of_js params)
           (int_of_float (Js.to_float gamma))
           (js_array_to_list y)
         |> Js.bool

       (** Response bound check *)
       method cbValidResponse params gamma challenge z =
         Confidential_balance.valid_balance_response
           (cb_params_of_js params)
           (int_of_float (Js.to_float gamma))
           (int_of_float (Js.to_float challenge))
           (js_array_to_list z)
         |> Js.bool

       (** Confidential-balance relation check *)
       method cbRelation params ck c r =
         Confidential_balance.balance_relation
           (cb_params_of_js params)
           (js_matrix_to_list ck)
           (js_array_to_list c)
           (js_array_to_list r)
         |> Js.bool

       (** Sigma announcement *)
       method cbSigmaCommit params ck y =
         Confidential_balance.balance_sigma_commit
           (cb_params_of_js params)
           (js_matrix_to_list ck)
           (js_array_to_list y)
         |> list_to_js_array

       (** Sigma response *)
       method cbSigmaRespond r y challenge =
         Confidential_balance.balance_sigma_respond
           (js_array_to_list r)
           (js_array_to_list y)
           (int_of_float (Js.to_float challenge))
         |> list_to_js_array

       (** Deterministic Fiat-Shamir challenge *)
       method cbCanonicalChallenge params ck c a =
         Confidential_balance.canonical_balance_challenge
           (cb_params_of_js params)
           (js_matrix_to_list ck)
           (js_array_to_list c)
           (js_array_to_list a)
         |> float_of_int |> Js.number_of_float

       (** Fixed number of Fiat-Shamir rounds *)
       method cbFsRounds =
         Confidential_balance.balance_fs_rounds
         |> float_of_int |> Js.number_of_float

       (** Deterministic Fiat-Shamir challenge list *)
       method cbFsChallenges params ck c as_ =
         Confidential_balance.balance_fs_challenges
           (cb_params_of_js params)
           (js_matrix_to_list ck)
           (js_array_to_list c)
           (js_matrix_to_list as_)
         |> list_to_js_array

       (** Sigma verification *)
       method cbSigmaVerify params gamma ck c a challenge z =
         Confidential_balance.balance_sigma_verify
           (cb_params_of_js params)
           (int_of_float (Js.to_float gamma))
           (js_matrix_to_list ck)
           (js_array_to_list c)
           (js_array_to_list a)
           (int_of_float (Js.to_float challenge))
           (js_array_to_list z)
         |> Js.bool

       (** Deterministic Fiat-Shamir proof construction *)
       method cbFsProve params gamma ck c r ys =
         let result =
           match Confidential_balance.balance_fs_prove
                   (cb_params_of_js params)
                   (int_of_float (Js.to_float gamma))
                   (js_matrix_to_list ck)
                   (js_array_to_list c)
                   (js_array_to_list r)
                   (js_matrix_to_list ys) with
           | Some proof -> Js.Unsafe.inject (cb_proof_to_js proof)
           | None -> Js.Unsafe.inject Js.null
         in
         result

       (** Deterministic Fiat-Shamir proof verification *)
       method cbFsVerify params gamma ck c proof =
         Confidential_balance.balance_fs_verify
           (cb_params_of_js params)
           (int_of_float (Js.to_float gamma))
           (js_matrix_to_list ck)
           (js_array_to_list c)
           (cb_proof_of_js proof)
         |> Js.bool

       (** Confidential-range opening to one *)
       method crOneOpening params =
         Confidential_range.one_opening (cb_params_of_js params)
         |> fun op ->
         Js.Unsafe.obj
           [|
             ("msg", Js.Unsafe.inject (list_to_js_array op.Commit_sis.open_msg));
             ("rand", Js.Unsafe.inject (list_to_js_array op.Commit_sis.open_rand));
           |]

       (** Confidential-range bit-opening validation *)
       method crValidBitOpening params opening =
         Confidential_range.valid_bit_opening
           (cb_params_of_js params)
           (cb_opening_of_js opening)
         |> Js.bool

       (** Confidential-range bit-pair relation *)
       method crBitPairRelation params bitOpening compOpening =
         Confidential_range.bit_pair_relation
           (cb_params_of_js params)
           (cb_opening_of_js bitOpening)
           (cb_opening_of_js compOpening)
         |> Js.bool

       (** Confidential-range weighted commitment *)
       method crWeightedCommitment params ck bits =
         Confidential_range.weighted_commitment
           (cb_params_of_js params)
           (js_matrix_to_list ck)
           2
           (js_matrix_to_list bits)
         |> list_to_js_array

       (** Confidential-range amount residual commitment *)
       method crAmountCommitment params ck cAmount cBits =
         Confidential_range.range_amount_commitment
           (cb_params_of_js params)
           (js_matrix_to_list ck)
           (js_array_to_list cAmount)
           (js_matrix_to_list cBits)
         |> list_to_js_array

       (** Confidential-range pair residual commitment *)
       method crPairCommitment params ck cBit cComp =
         Confidential_range.range_pair_commitment
           (cb_params_of_js params)
           (js_matrix_to_list ck)
           (js_array_to_list cBit)
           (js_array_to_list cComp)
         |> list_to_js_array

       (** Confidential-range relation check *)
       method crRelation params ck cAmount amountOpening bitOpenings compOpenings =
         let mk_openings payload =
           List.map2 Commit_sis.make_opening
             (js_matrix_to_list (Js.Unsafe.get payload "msgs"))
             (js_matrix_to_list (Js.Unsafe.get payload "rands"))
         in
         let bit_ops = mk_openings bitOpenings in
         let comp_ops = mk_openings compOpenings
         in
         Confidential_range.range_relation
           (cb_params_of_js params)
           (js_matrix_to_list ck)
           (js_array_to_list cAmount)
           (cb_opening_of_js amountOpening)
           bit_ops
           comp_ops
         |> Js.bool

       (** Confidential-range witness bounds *)
       method crAmountWitnessBound params k =
         Confidential_range.range_amount_witness_bound
           (cb_params_of_js params)
           (int_of_float (Js.to_float k))
         |> float_of_int |> Js.number_of_float

       method crPairWitnessBound params =
         Confidential_range.range_pair_witness_bound
           (cb_params_of_js params)
         |> float_of_int |> Js.number_of_float

       method crValidAmountWitness params k r =
         Confidential_range.valid_range_amount_witness
           (cb_params_of_js params)
           (int_of_float (Js.to_float k))
           (js_array_to_list r)
         |> Js.bool

       method crValidPairWitness params r =
         Confidential_range.valid_range_pair_witness
           (cb_params_of_js params)
           (js_array_to_list r)
         |> Js.bool

       method crValidMask params gamma y =
         Confidential_range.valid_range_mask
           (cb_params_of_js params)
           (int_of_float (Js.to_float gamma))
           (js_array_to_list y)
         |> Js.bool

       method crValidAmountResponse params gamma k challenge z =
         Confidential_range.valid_range_amount_response
           (cb_params_of_js params)
           (int_of_float (Js.to_float gamma))
           (int_of_float (Js.to_float k))
           (int_of_float (Js.to_float challenge))
           (js_array_to_list z)
         |> Js.bool

       method crValidPairResponse params gamma challenge z =
         Confidential_range.valid_range_pair_response
           (cb_params_of_js params)
           (int_of_float (Js.to_float gamma))
           (int_of_float (Js.to_float challenge))
           (js_array_to_list z)
         |> Js.bool

       (** Deterministic Fiat-Shamir challenge for confidential range *)
       method crCanonicalChallenge params ck cAmount cBits cComps aAmounts aPairss =
         Confidential_range.canonical_range_challenge
           (cb_params_of_js params)
           (js_matrix_to_list ck)
           (js_array_to_list cAmount)
           (js_matrix_to_list cBits)
           (js_matrix_to_list cComps)
           (js_matrix_to_list aAmounts)
           (js_cube_to_list aPairss)
         |> float_of_int |> Js.number_of_float

       (** Deterministic Fiat-Shamir proof construction for confidential range *)
       method crFsProve params gamma k ck cAmount amountOpening bitMsgs bitRands compMsgs compRands yAmounts yPairss =
         let mk_openings msgs rands =
           List.map2 Commit_sis.make_opening (js_matrix_to_list msgs) (js_matrix_to_list rands)
         in
         let result =
           match Confidential_range.range_fs_prove
                   (cb_params_of_js params)
                   (int_of_float (Js.to_float gamma))
                   (int_of_float (Js.to_float k))
                   (js_matrix_to_list ck)
                   (js_array_to_list cAmount)
                   (cb_opening_of_js amountOpening)
                   (mk_openings bitMsgs bitRands)
                   (mk_openings compMsgs compRands)
                   (js_matrix_to_list yAmounts)
                   (js_cube_to_list yPairss) with
           | Some proof -> Js.Unsafe.inject (cr_proof_to_js proof)
           | None -> Js.Unsafe.inject Js.null
         in
         result

       (** Deterministic Fiat-Shamir proof verification for confidential range *)
       method crFsVerify params gamma k ck cAmount proof =
         Confidential_range.range_fs_verify
           (cb_params_of_js params)
           (int_of_float (Js.to_float gamma))
           (int_of_float (Js.to_float k))
           (js_matrix_to_list ck)
           (js_array_to_list cAmount)
           (cr_proof_of_js proof)
         |> Js.bool

       (** Deterministic note nullifier *)
       method ctNullifier params nk opening =
         Confidential_transaction.nullifier
           (cb_params_of_js params)
           (js_matrix_to_list nk)
           (cb_opening_of_js opening)
         |> list_to_js_array

       (** Deterministic Fiat-Shamir challenge for nullifier proofs *)
       method ctNullifierCanonicalChallenge params ck nk c nf aCommit aNullifier =
         Confidential_transaction.canonical_nullifier_challenge
           (cb_params_of_js params)
           (js_matrix_to_list ck)
           (js_matrix_to_list nk)
           (js_array_to_list c)
           (js_array_to_list nf)
           (js_array_to_list aCommit)
           (js_array_to_list aNullifier)
         |> float_of_int |> Js.number_of_float

       (** Deterministic Fiat-Shamir nullifier proof construction *)
       method ctNullifierFsProve params gamma ck nk c nf opening ys =
         let result =
           match Confidential_transaction.nullifier_fs_prove
                   (cb_params_of_js params)
                   (int_of_float (Js.to_float gamma))
                   (js_matrix_to_list ck)
                   (js_matrix_to_list nk)
                   (js_array_to_list c)
                   (js_array_to_list nf)
                   (cb_opening_of_js opening)
                   (js_openings_to_list ys) with
           | Some proof -> Js.Unsafe.inject (ct_nullifier_proof_to_js proof)
           | None -> Js.Unsafe.inject Js.null
         in
         result

       (** Deterministic Fiat-Shamir nullifier proof verification *)
       method ctNullifierFsVerify params gamma ck nk c nf proof =
         Confidential_transaction.nullifier_fs_verify
           (cb_params_of_js params)
           (int_of_float (Js.to_float gamma))
           (js_matrix_to_list ck)
           (js_matrix_to_list nk)
           (js_array_to_list c)
           (js_array_to_list nf)
           (ct_nullifier_proof_of_js proof)
         |> Js.bool

       method ctLedgerRoot params ledger =
         Confidential_transaction.ledger_root
           (cb_params_of_js params)
           (js_matrix_to_list ledger)
         |> list_to_js_array

       (** Deterministic ledger membership proof construction *)
       method ctMembershipProve params ledger c =
         let result =
           match Confidential_transaction.membership_prove
                   (cb_params_of_js params)
                   (js_matrix_to_list ledger)
                   (js_array_to_list c) with
           | Some proof -> Js.Unsafe.inject (ct_membership_proof_to_js proof)
           | None -> Js.Unsafe.inject Js.null
         in
         result

       (** Deterministic ledger membership proof verification *)
       method ctMembershipVerify params c proof =
         Confidential_transaction.membership_verify
           (cb_params_of_js params)
           (js_array_to_list c)
           (ct_membership_proof_of_js proof)
         |> Js.bool

       (** Extract the commitment view of a verified-note ledger *)
       method ctCommitmentLedger notes =
         Confidential_transaction.commitment_ledger
           (ct_notes_of_js notes)
         |> list_to_js_matrix

       (** Ledger validity for range-verified notes and spent nullifiers *)
       method ctLedgerValid params gamma k ck root notes spent =
         Confidential_transaction.ledger_valid
           (cb_params_of_js params)
           (int_of_float (Js.to_float gamma))
           (int_of_float (Js.to_float k))
           (js_matrix_to_list ck)
           (js_array_to_list root)
           (ct_notes_of_js notes)
           (js_matrix_to_list spent)
         |> Js.bool

       (** Scaffold ledger-step validity from a concrete pre-state *)
       method ctLedgerStepValidScaffold params gamma k ck nk notes spent cIn1 cIn2 cOut1 cOut2 nf1 nf2 proof =
         Confidential_transaction.ledger_step_valid_scaffold
           (cb_params_of_js params)
           (int_of_float (Js.to_float gamma))
           (int_of_float (Js.to_float k))
           (js_matrix_to_list ck)
           (js_matrix_to_list nk)
           (ct_notes_of_js notes)
           (js_matrix_to_list spent)
           (js_array_to_list cIn1)
           (js_array_to_list cIn2)
           (js_array_to_list cOut1)
           (js_array_to_list cOut2)
           (js_array_to_list nf1)
           (js_array_to_list nf2)
           (ct_transaction_proof_of_js proof)
         |> Js.bool

       (** Deterministic Fiat-Shamir confidential-transaction proof construction *)
       method ctFsProve params gamma k ck nk ledger spent cIn1 cIn2 cOut1 cOut2 nf1 nf2 opIn1 opIn2 opOut1 opOut2 out1Bits out1Comps out2Bits out2Comps yIn1 yIn2 yBalance yOut1 yOut1Pairs yOut2 yOut2Pairs =
         let result =
           match Confidential_transaction.transaction_fs_prove
                   (cb_params_of_js params)
                   (int_of_float (Js.to_float gamma))
                   (int_of_float (Js.to_float k))
                   (js_matrix_to_list ck)
                   (js_matrix_to_list nk)
                   (js_matrix_to_list ledger)
                   (js_matrix_to_list spent)
                   (js_array_to_list cIn1)
                   (js_array_to_list cIn2)
                   (js_array_to_list cOut1)
                   (js_array_to_list cOut2)
                   (js_array_to_list nf1)
                   (js_array_to_list nf2)
                   (cb_opening_of_js opIn1)
                   (cb_opening_of_js opIn2)
                   (cb_opening_of_js opOut1)
                   (cb_opening_of_js opOut2)
                   (js_openings_to_list out1Bits)
                   (js_openings_to_list out1Comps)
                   (js_openings_to_list out2Bits)
                   (js_openings_to_list out2Comps)
                   (js_openings_to_list yIn1)
                   (js_openings_to_list yIn2)
                   (js_matrix_to_list yBalance)
                   (js_matrix_to_list yOut1)
                   (js_cube_to_list yOut1Pairs)
                   (js_matrix_to_list yOut2)
                   (js_cube_to_list yOut2Pairs) with
           | Some proof -> Js.Unsafe.inject (ct_transaction_proof_to_js proof)
           | None -> Js.Unsafe.inject Js.null
         in
         result

       (** Deterministic Fiat-Shamir confidential-transaction proof verification *)
       method ctFsVerify params gamma k ck nk root spent cIn1 cIn2 cOut1 cOut2 nf1 nf2 proof =
         Confidential_transaction.transaction_fs_verify
           (cb_params_of_js params)
           (int_of_float (Js.to_float gamma))
           (int_of_float (Js.to_float k))
           (js_matrix_to_list ck)
           (js_matrix_to_list nk)
           (js_array_to_list root)
           (js_matrix_to_list spent)
           (js_array_to_list cIn1)
           (js_array_to_list cIn2)
           (js_array_to_list cOut1)
           (js_array_to_list cOut2)
           (js_array_to_list nf1)
           (js_array_to_list nf2)
           (ct_transaction_proof_of_js proof)
         |> Js.bool

       (** Apply the transaction outputs to a verified-note ledger *)
       method ctLedgerApplyNotes notes proof cOut1 cOut2 =
         Confidential_transaction.ledger_apply_notes
           (ct_notes_of_js notes)
           (ct_transaction_proof_of_js proof)
           (js_array_to_list cOut1)
           (js_array_to_list cOut2)
         |> ct_notes_to_js

       (** Append new nullifiers to the spent set *)
       method ctLedgerApplySpent spent nf1 nf2 =
         Confidential_transaction.ledger_apply_spent
           (js_matrix_to_list spent)
           (js_array_to_list nf1)
           (js_array_to_list nf2)
         |> list_to_js_matrix
     end)
