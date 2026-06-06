(** Confidential transaction proof helpers
    Derived from the verified Canon/ZK/Confidential_Transaction theory.

    This module keeps the SDK surface native and deterministic while remaining
    a thin composition layer over Isabelle-exported Canon modules. *)

type scalar_commit_params = Commit_sis.commit_params
type commit_opening = Commit_sis.commit_opening
type range_proof = Confidential_range.range_proof
type balance_proof = Confidential_balance.balance_proof

type nullifier_proof = {
  nullifier_a_commits : int list list;
  nullifier_a_nullifiers : int list list;
  nullifier_z_msgs : int list list;
  nullifier_z_rands : int list list;
}

let make_nullifier_proof nullifier_a_commits nullifier_a_nullifiers nullifier_z_msgs nullifier_z_rands =
  { nullifier_a_commits; nullifier_a_nullifiers; nullifier_z_msgs; nullifier_z_rands }

type membership_proof = {
  member_index : int;
  member_root : int list;
  member_siblings : int list list;
  member_directions : bool list;
}

let make_membership_proof member_index member_root member_siblings member_directions =
  { member_index; member_root; member_siblings; member_directions }

type merkle_membership_proof = Confidential_merkle.membership_proof

let make_merkle_membership_proof merkle_index merkle_root merkle_siblings merkle_directions =
  { Confidential_merkle.merkle_index; merkle_root; merkle_siblings; merkle_directions }

type verified_note = {
  note_commitment : int list;
  note_range_proof : range_proof;
}

let make_verified_note note_commitment note_range_proof =
  { note_commitment; note_range_proof }

type transaction_proof = {
  tx_in1_member : membership_proof;
  tx_in2_member : membership_proof;
  tx_in1_nullifier : nullifier_proof;
  tx_in2_nullifier : nullifier_proof;
  tx_balance : balance_proof;
  tx_out1_range : range_proof;
  tx_out2_range : range_proof;
}

let make_transaction_proof
    tx_in1_member
    tx_in2_member
    tx_in1_nullifier
    tx_in2_nullifier
    tx_balance
    tx_out1_range
    tx_out2_range =
  {
    tx_in1_member;
    tx_in2_member;
    tx_in1_nullifier;
    tx_in2_nullifier;
    tx_balance;
    tx_out1_range;
      tx_out2_range;
  }

type merkle_transaction_proof = {
  tx_merkle_in1_member : merkle_membership_proof;
  tx_merkle_in2_member : merkle_membership_proof;
  tx_merkle_in1_nullifier : nullifier_proof;
  tx_merkle_in2_nullifier : nullifier_proof;
  tx_merkle_balance : balance_proof;
  tx_merkle_out1_range : range_proof;
  tx_merkle_out2_range : range_proof;
}

let make_merkle_transaction_proof
    tx_merkle_in1_member
    tx_merkle_in2_member
    tx_merkle_in1_nullifier
    tx_merkle_in2_nullifier
    tx_merkle_balance
    tx_merkle_out1_range
    tx_merkle_out2_range =
  {
    tx_merkle_in1_member;
    tx_merkle_in2_member;
    tx_merkle_in1_nullifier;
    tx_merkle_in2_nullifier;
    tx_merkle_balance;
    tx_merkle_out1_range;
    tx_merkle_out2_range;
  }

let transaction_dst = "ISABELLA-CT-TX-v1"
let transaction_protocol_id = "ISABELLA-CT-SIS-NOTE"
let transaction_context_tag = 0
let transaction_merkle_proof_tag = 1
let transaction_envelope_tag = 2
let transaction_wallet_proof_request_tag = 3

let require_nonnegative label value =
  if value < 0 then invalid_arg (label ^ " must be non-negative")

let encode_ascii label value =
  let bytes = Repeated_fs.string_bytes value in
  List.iteri
    (fun index byte ->
       if byte < 0x20 || byte > 0x7e then
         invalid_arg (Printf.sprintf "%s[%d] must be printable ASCII" label index))
    bytes;
  Repeated_fs.int64_le_bytes (Int64.of_int (List.length bytes)) @ bytes

let encode_transaction_int label value =
  require_nonnegative label value;
  Repeated_fs.int64_le_bytes (Int64.of_int value)

let encode_transaction_vec values =
  Repeated_fs.int64_le_bytes (Int64.of_int (List.length values))
  @ List.concat (List.map (fun value -> Repeated_fs.int64_le_bytes (Int64.of_int value)) values)

let encode_transaction_bool_vec values =
  Repeated_fs.int64_le_bytes (Int64.of_int (List.length values))
  @ List.concat
      (List.map
         (fun value -> Repeated_fs.int64_le_bytes (Int64.of_int (if value then 1 else 0)))
         values)

let encode_transaction_mat rows =
  Repeated_fs.int64_le_bytes (Int64.of_int (List.length rows))
  @ List.concat (List.map encode_transaction_vec rows)

let encode_transaction_cube mats =
  Repeated_fs.int64_le_bytes (Int64.of_int (List.length mats))
  @ List.concat (List.map encode_transaction_mat mats)

let encode_transaction_digest label digest =
  match Confidential_merkle.hex_to_bytes digest with
  | Some bytes ->
      Repeated_fs.int64_le_bytes (Int64.of_int (List.length bytes)) @ bytes
  | None -> invalid_arg (label ^ " must be a canonical lowercase SHA3-256 digest")

let encode_transaction_digest_vec label digests =
  Repeated_fs.int64_le_bytes (Int64.of_int (List.length digests))
  @ List.concat
      (List.mapi
         (fun index digest -> encode_transaction_digest (Printf.sprintf "%s[%d]" label index) digest)
         digests)

let rec compare_int_lists left right =
  match left, right with
  | [], [] -> 0
  | [], _ -> -1
  | _, [] -> 1
  | l :: ls, r :: rs ->
    if l < r then -1
    else if l > r then 1
    else compare_int_lists ls rs

let require_sorted_unique compare label values =
  let rec loop previous = function
    | [] -> ()
    | value :: rest ->
      (match previous with
       | Some p when compare p value >= 0 ->
         invalid_arg (label ^ " must be sorted with no duplicates")
       | _ -> loop (Some value) rest)
  in
  loop None values

let require_canonical_digest_set label digests =
  if digests = [] then invalid_arg (label ^ " must not be empty");
  List.iteri
    (fun index digest ->
       ignore (encode_transaction_digest (Printf.sprintf "%s[%d]" label index) digest))
    digests;
  require_sorted_unique String.compare label digests

let require_canonical_int_matrix_set label rows =
  require_sorted_unique compare_int_lists label rows

let transaction_context_preimage
    protocol_version
    network_id
    asset_id
    ledger_epoch
    root
    public_fee
    c_in1
    c_in2
    c_out1
    c_out2
    nf1
    nf2 =
  Repeated_fs.string_bytes transaction_dst
  @ Repeated_fs.int64_le_bytes (Int64.of_int transaction_context_tag)
  @ encode_ascii "protocolId" transaction_protocol_id
  @ encode_transaction_int "protocolVersion" protocol_version
  @ encode_ascii "networkId" network_id
  @ encode_transaction_int "assetId" asset_id
  @ encode_transaction_int "ledgerEpoch" ledger_epoch
  @ encode_transaction_digest "root" root
  @ encode_transaction_int "publicFee" public_fee
  @ encode_transaction_vec c_in1
  @ encode_transaction_vec c_in2
  @ encode_transaction_vec c_out1
  @ encode_transaction_vec c_out2
  @ encode_transaction_vec nf1
  @ encode_transaction_vec nf2

let transaction_tagged_preimage tag body =
  Repeated_fs.string_bytes transaction_dst
  @ Repeated_fs.int64_le_bytes (Int64.of_int tag)
  @ encode_ascii "protocolId" transaction_protocol_id
  @ body

let transaction_merkle_membership_preimage proof =
  if List.length proof.Confidential_merkle.merkle_siblings <>
     List.length proof.Confidential_merkle.merkle_directions
  then invalid_arg "Merkle proof siblings and directions must have the same length";
  encode_transaction_int "member.index" proof.Confidential_merkle.merkle_index
  @ encode_transaction_digest "member.root" proof.Confidential_merkle.merkle_root
  @ encode_transaction_digest_vec "member.siblings" proof.Confidential_merkle.merkle_siblings
  @ encode_transaction_bool_vec proof.Confidential_merkle.merkle_directions

let transaction_nullifier_proof_preimage proof =
  encode_transaction_mat proof.nullifier_a_commits
  @ encode_transaction_mat proof.nullifier_a_nullifiers
  @ encode_transaction_mat proof.nullifier_z_msgs
  @ encode_transaction_mat proof.nullifier_z_rands

let transaction_balance_proof_preimage proof =
  encode_transaction_mat proof.Confidential_balance.balance_as
  @ encode_transaction_mat proof.Confidential_balance.balance_zs

let transaction_range_proof_preimage proof =
  encode_transaction_mat proof.Confidential_range.range_bits
  @ encode_transaction_mat proof.Confidential_range.range_comps
  @ encode_transaction_mat proof.Confidential_range.range_amount_as
  @ encode_transaction_mat proof.Confidential_range.range_amount_zs
  @ encode_transaction_cube proof.Confidential_range.range_pair_ass
  @ encode_transaction_cube proof.Confidential_range.range_pair_zss

let transaction_merkle_proof_preimage proof =
  transaction_tagged_preimage
    transaction_merkle_proof_tag
    (transaction_merkle_membership_preimage proof.tx_merkle_in1_member
     @ transaction_merkle_membership_preimage proof.tx_merkle_in2_member
     @ transaction_nullifier_proof_preimage proof.tx_merkle_in1_nullifier
     @ transaction_nullifier_proof_preimage proof.tx_merkle_in2_nullifier
     @ transaction_balance_proof_preimage proof.tx_merkle_balance
     @ transaction_range_proof_preimage proof.tx_merkle_out1_range
     @ transaction_range_proof_preimage proof.tx_merkle_out2_range)

let transaction_merkle_proof_preimage_hex proof =
  transaction_merkle_proof_preimage proof |> Confidential_merkle.digest_hex

let transaction_merkle_proof_digest proof =
  transaction_merkle_proof_preimage proof |> Confidential_merkle.digest

let transaction_envelope_preimage
    context_digest
    protocol_version
    network_id
    asset_id
    ledger_epoch
    root
    public_fee
    c_in1
    c_in2
    c_out1
    c_out2
    nf1
    nf2
    proof =
  let computed_digest =
    transaction_context_preimage
      protocol_version network_id asset_id ledger_epoch root public_fee
      c_in1 c_in2 c_out1 c_out2 nf1 nf2
    |> Confidential_merkle.digest
  in
  if context_digest <> computed_digest then
    invalid_arg "contextDigest does not match canonical transaction context";
  transaction_tagged_preimage
    transaction_envelope_tag
    (encode_transaction_digest "contextDigest" computed_digest
     @ encode_transaction_digest "proofDigest" (transaction_merkle_proof_digest proof))

let transaction_envelope_preimage_hex
    context_digest protocol_version network_id asset_id ledger_epoch root public_fee
    c_in1 c_in2 c_out1 c_out2 nf1 nf2 proof =
  transaction_envelope_preimage
    context_digest protocol_version network_id asset_id ledger_epoch root public_fee
    c_in1 c_in2 c_out1 c_out2 nf1 nf2 proof
  |> Confidential_merkle.digest_hex

let transaction_envelope_digest
    context_digest protocol_version network_id asset_id ledger_epoch root public_fee
    c_in1 c_in2 c_out1 c_out2 nf1 nf2 proof =
  transaction_envelope_preimage
    context_digest protocol_version network_id asset_id ledger_epoch root public_fee
    c_in1 c_in2 c_out1 c_out2 nf1 nf2 proof
  |> Confidential_merkle.digest

let transaction_wallet_proof_request_preimage
    protocol_version
    network_id
    asset_id
    ledger_epoch
    root
    public_fee
    c_in1
    c_in2
    c_out1
    c_out2
    nf1
    nf2
    accepted_roots
    spent_nullifiers =
  require_canonical_digest_set "acceptedRoots" accepted_roots;
  require_canonical_int_matrix_set "spentNullifiers" spent_nullifiers;
  let context_digest =
    transaction_context_preimage
      protocol_version network_id asset_id ledger_epoch root public_fee
      c_in1 c_in2 c_out1 c_out2 nf1 nf2
    |> Confidential_merkle.digest
  in
  if not (List.mem root accepted_roots) then
    invalid_arg "context.root must be inside acceptedRoots";
  if nf1 = nf2 then
    invalid_arg "context nullifiers must be distinct";
  if List.mem nf1 spent_nullifiers || List.mem nf2 spent_nullifiers then
    invalid_arg "context nullifiers must be absent from spentNullifiers";
  transaction_tagged_preimage
    transaction_wallet_proof_request_tag
    (encode_transaction_digest "contextDigest" context_digest
     @ encode_transaction_digest_vec "acceptedRoots" accepted_roots
     @ encode_transaction_mat spent_nullifiers)

let transaction_wallet_proof_request_preimage_hex
    protocol_version network_id asset_id ledger_epoch root public_fee
    c_in1 c_in2 c_out1 c_out2 nf1 nf2 accepted_roots spent_nullifiers =
  transaction_wallet_proof_request_preimage
    protocol_version network_id asset_id ledger_epoch root public_fee
    c_in1 c_in2 c_out1 c_out2 nf1 nf2 accepted_roots spent_nullifiers
  |> Confidential_merkle.digest_hex

let transaction_wallet_proof_request_digest
    protocol_version network_id asset_id ledger_epoch root public_fee
    c_in1 c_in2 c_out1 c_out2 nf1 nf2 accepted_roots spent_nullifiers =
  transaction_wallet_proof_request_preimage
    protocol_version network_id asset_id ledger_epoch root public_fee
    c_in1 c_in2 c_out1 c_out2 nf1 nf2 accepted_roots spent_nullifiers
  |> Confidential_merkle.digest

let transaction_context_preimage_hex
    protocol_version network_id asset_id ledger_epoch root public_fee
    c_in1 c_in2 c_out1 c_out2 nf1 nf2 =
  transaction_context_preimage
    protocol_version network_id asset_id ledger_epoch root public_fee
    c_in1 c_in2 c_out1 c_out2 nf1 nf2
  |> Confidential_merkle.digest_hex

let transaction_context_digest
    protocol_version network_id asset_id ledger_epoch root public_fee
    c_in1 c_in2 c_out1 c_out2 nf1 nf2 =
  transaction_context_preimage
    protocol_version network_id asset_id ledger_epoch root public_fee
    c_in1 c_in2 c_out1 c_out2 nf1 nf2
  |> Confidential_merkle.digest

let valid_commitment p c =
  Listvec.valid_vec p.Commit_sis.cp_m c

let opening_add op1 op2 =
  Commit_sis.make_opening
    (Listvec.vec_add op1.Commit_sis.open_msg op2.Commit_sis.open_msg)
    (Listvec.vec_add op1.Commit_sis.open_rand op2.Commit_sis.open_rand)

let nullifier_fs_rounds = Confidential_balance.balance_fs_rounds

let nullifier_sigma_respond op y challenge =
  opening_add y (Confidential_range.opening_scale challenge op)

let nullifier_fs_domain = 3001

let nullifier_fs_fields ck nk c nf a_commits a_nullifiers =
  let sum_list = List.fold_left ( + ) 0 in
  [ sum_list (List.concat ck);
    sum_list (List.concat nk);
    sum_list c;
    sum_list nf;
    sum_list (List.concat a_commits);
    sum_list (List.concat a_nullifiers) ]

let nullifier_fs_challenges _p ck nk c nf a_commits a_nullifiers =
  Repeated_fs.binary_fs_challenges
    nullifier_fs_domain
    (nullifier_fs_fields ck nk c nf a_commits a_nullifiers)

let nullifier_z_openings proof =
  List.map2 Commit_sis.make_opening proof.nullifier_z_msgs proof.nullifier_z_rands

let nullifier p nk op =
  Commit_sis.commit nk op p.Commit_sis.cp_q

let valid_nullifier_mask p gamma y =
  Listvec.valid_vec p.Commit_sis.cp_n1 y.Commit_sis.open_msg &&
  Listvec.valid_vec p.Commit_sis.cp_n2 y.Commit_sis.open_rand &&
  Norms.all_bounded y.Commit_sis.open_msg gamma &&
  Norms.all_bounded y.Commit_sis.open_rand gamma

let sample_nullifier_mask p gamma =
  Confidential_sampling.opening p.Commit_sis.cp_n1 p.Commit_sis.cp_n2 gamma

let sample_nullifier_masks p gamma rounds =
  Confidential_sampling.openings rounds p.Commit_sis.cp_n1 p.Commit_sis.cp_n2 gamma

let nullifier_response_bound p gamma challenge =
  gamma + (abs challenge * p.Commit_sis.cp_beta)

let valid_nullifier_challenge = Confidential_balance.valid_balance_challenge

let valid_nullifier_response p gamma challenge z =
  Listvec.valid_vec p.Commit_sis.cp_n1 z.Commit_sis.open_msg &&
  Listvec.valid_vec p.Commit_sis.cp_n2 z.Commit_sis.open_rand &&
  Norms.all_bounded z.Commit_sis.open_msg (nullifier_response_bound p gamma challenge) &&
  Norms.all_bounded z.Commit_sis.open_rand (nullifier_response_bound p gamma challenge)

let nullifier_relation p ck nk c nf op =
  Confidential_balance.valid_scalar_commit_params p &&
  Confidential_balance.valid_confidential_commit_key p ck &&
  Confidential_balance.valid_confidential_commit_key p nk &&
  Commit_sis.valid_opening p op &&
  Commit_sis.verify_opening ck op c p.Commit_sis.cp_q &&
  nullifier p nk op = nf

let nullifier_relation_wellformed p ck nk c nf op =
  Confidential_balance.valid_scalar_commit_params p &&
  Commit_sis.valid_commit_key p ck &&
  Commit_sis.valid_commit_key p nk &&
  Commit_sis.valid_opening p op &&
  Commit_sis.verify_opening ck op c p.Commit_sis.cp_q &&
  nullifier p nk op = nf

let canonical_nullifier_challenge _p ck nk c nf a_commit a_nullifier =
  Repeated_fs.binary_fs_challenge
    nullifier_fs_domain
    (nullifier_fs_fields ck nk c nf [a_commit] [a_nullifier])
    0

let nullifier_sigma_verify p gamma ck nk c nf a_commit a_nullifier challenge z =
  Confidential_balance.valid_scalar_commit_params p &&
  Commit_sis.valid_commit_key p ck &&
  Commit_sis.valid_commit_key p nk &&
  valid_commitment p c &&
  valid_commitment p nf &&
  valid_commitment p a_commit &&
  valid_commitment p a_nullifier &&
  valid_nullifier_challenge p challenge &&
  valid_nullifier_response p gamma challenge z &&
  Commit_sis.commit ck z p.Commit_sis.cp_q =
    Zq.vec_mod (Listvec.vec_add a_commit (Listvec.scalar_mult challenge c)) p.Commit_sis.cp_q &&
  nullifier p nk z =
    Zq.vec_mod (Listvec.vec_add a_nullifier (Listvec.scalar_mult challenge nf)) p.Commit_sis.cp_q

let nullifier_fs_prove p gamma ck nk c nf op ys =
  let a_commits = List.map (fun y -> Commit_sis.commit ck y p.Commit_sis.cp_q) ys in
  let a_nullifiers = List.map (nullifier p nk) ys in
  let challenges = nullifier_fs_challenges p ck nk c nf a_commits a_nullifiers in
  let zs = Repeated_fs.sigma_response_rounds nullifier_sigma_respond op ys challenges in
  if nullifier_relation_wellformed p ck nk c nf op &&
     List.length ys = nullifier_fs_rounds &&
     List.for_all (valid_nullifier_mask p gamma) ys &&
     List.for_all2 (valid_nullifier_response p gamma) challenges zs
  then Some (make_nullifier_proof a_commits a_nullifiers (List.map (fun z -> z.Commit_sis.open_msg) zs) (List.map (fun z -> z.Commit_sis.open_rand) zs))
  else None

let nullifier_fs_verify p gamma ck nk c nf proof =
  let challenges =
    nullifier_fs_challenges
      p
      ck
      nk
      c
      nf
      proof.nullifier_a_commits
      proof.nullifier_a_nullifiers
  in
  let zs = nullifier_z_openings proof in
  List.length proof.nullifier_a_commits = nullifier_fs_rounds &&
  List.length proof.nullifier_a_nullifiers = nullifier_fs_rounds &&
  List.length proof.nullifier_z_msgs = nullifier_fs_rounds &&
  List.length proof.nullifier_z_rands = nullifier_fs_rounds &&
  List.for_all2
    (fun ((a_commit, a_nullifier), challenge) z ->
       nullifier_sigma_verify
         p
         gamma
         ck
         nk
         c
         nf
         a_commit
         a_nullifier
         challenge
         z)
    (List.combine (List.combine proof.nullifier_a_commits proof.nullifier_a_nullifiers) challenges)
    zs

let empty_commitment p =
  List.init p.Commit_sis.cp_m (fun _ -> 0)

let ledger_hash p left right =
  Zq.vec_mod (Listvec.vec_add left (Listvec.scalar_mult 2 right)) p.Commit_sis.cp_q

let rec compress_pairs p = function
  | [] -> []
  | [x] -> [ledger_hash p x (empty_commitment p)]
  | x :: y :: xs -> ledger_hash p x y :: compress_pairs p xs

let rec ledger_root p = function
  | [] -> empty_commitment p
  | [x] -> x
  | xs -> ledger_root p (compress_pairs p xs)

let rec index_directions depth idx =
  if depth <= 0 then [] else (idx mod 2 = 1) :: index_directions (depth - 1) (idx / 2)

let rec auth_path_root p node siblings directions =
  match siblings, directions with
  | [], [] -> node
  | sibling :: rest_siblings, false :: rest_directions ->
      auth_path_root p (ledger_hash p node sibling) rest_siblings rest_directions
  | sibling :: rest_siblings, true :: rest_directions ->
      auth_path_root p (ledger_hash p sibling node) rest_siblings rest_directions
  | _ -> empty_commitment p

let rec membership_index_of ledger c =
  match ledger with
  | [] -> None
  | x :: xs ->
      if x = c then Some 0
      else Option.map (( + ) 1) (membership_index_of xs c)

let rec membership_siblings p ledger idx =
  match ledger with
  | [] -> None
  | [_] -> if idx = 0 then Some [] else None
  | _ ->
      if idx < 0 || idx >= List.length ledger then None
      else
        let sibling =
          if idx mod 2 = 1 then List.nth ledger (idx - 1)
          else if idx + 1 < List.length ledger then List.nth ledger (idx + 1)
          else empty_commitment p
        in
        Option.map
          (fun tail -> sibling :: tail)
          (membership_siblings p (compress_pairs p ledger) (idx / 2))

let membership_prove p ledger c =
  match membership_index_of ledger c with
  | None -> None
  | Some i ->
      Option.map
        (fun siblings ->
           make_membership_proof
             i
             (ledger_root p ledger)
             siblings
             (index_directions (List.length siblings) i))
        (membership_siblings p ledger i)

let membership_verify p c proof =
  List.length proof.member_siblings = List.length proof.member_directions &&
  proof.member_directions =
    index_directions (List.length proof.member_siblings) proof.member_index &&
  auth_path_root p c proof.member_siblings proof.member_directions = proof.member_root

let merkle_ledger_root ledger =
  Confidential_merkle.root ledger

let merkle_membership_prove ledger c =
  Confidential_merkle.membership_prove ledger c

let merkle_membership_verify c proof =
  Confidential_merkle.membership_verify c proof

let merkle_member_root proof =
  proof.Confidential_merkle.merkle_root

let merkle_member_index proof =
  proof.Confidential_merkle.merkle_index

let commitment_ledger notes =
  List.map (fun note -> note.note_commitment) notes

let rec distinct = function
  | [] -> true
  | x :: xs -> not (List.mem x xs) && distinct xs

let ledger_valid p gamma k ck root notes spent =
  Confidential_balance.valid_scalar_commit_params p &&
  Commit_sis.valid_commit_key p ck &&
  root = ledger_root p (commitment_ledger notes) &&
  distinct spent &&
  List.for_all
    (fun note ->
       Confidential_range.range_fs_verify
         p
         gamma
         k
         ck
         note.note_commitment
         note.note_range_proof)
    notes

let ledger_valid_merkle p gamma k ck root notes spent =
  Confidential_balance.valid_scalar_commit_params p &&
  Commit_sis.valid_commit_key p ck &&
  root = merkle_ledger_root (commitment_ledger notes) &&
  distinct spent &&
  List.for_all
    (fun note ->
       Confidential_range.range_fs_verify
         p
         gamma
         k
         ck
         note.note_commitment
         note.note_range_proof)
    notes

let transaction_relation p ck nk ledger spent c_in1 c_in2 c_out1 c_out2 nf1 nf2
    op_in1 op_in2 op_out1 op_out2 out1_bits out1_comps out2_bits out2_comps =
  nullifier_relation p ck nk c_in1 nf1 op_in1 &&
  nullifier_relation p ck nk c_in2 nf2 op_in2 &&
  List.mem c_in1 ledger &&
  List.mem c_in2 ledger &&
  not (List.mem nf1 spent) &&
  not (List.mem nf2 spent) &&
  nf1 <> nf2 &&
  Confidential_range.range_relation p ck c_out1 op_out1 out1_bits out1_comps &&
  Confidential_range.range_relation p ck c_out2 op_out2 out2_bits out2_comps &&
  Confidential_balance.amount_of_opening op_in1 +
  Confidential_balance.amount_of_opening op_in2 =
    Confidential_balance.amount_of_opening op_out1 +
    Confidential_balance.amount_of_opening op_out2

let transaction_relation_wellformed p ck nk ledger spent c_in1 c_in2 c_out1 c_out2 nf1 nf2
    op_in1 op_in2 op_out1 op_out2 out1_bits out1_comps out2_bits out2_comps =
  nullifier_relation_wellformed p ck nk c_in1 nf1 op_in1 &&
  nullifier_relation_wellformed p ck nk c_in2 nf2 op_in2 &&
  List.mem c_in1 ledger &&
  List.mem c_in2 ledger &&
  not (List.mem nf1 spent) &&
  not (List.mem nf2 spent) &&
  nf1 <> nf2 &&
  Confidential_range.range_relation p ck c_out1 op_out1 out1_bits out1_comps &&
  Confidential_range.range_relation p ck c_out2 op_out2 out2_bits out2_comps &&
  Confidential_balance.amount_of_opening op_in1 +
  Confidential_balance.amount_of_opening op_in2 =
    Confidential_balance.amount_of_opening op_out1 +
    Confidential_balance.amount_of_opening op_out2

let transaction_fs_verify p gamma k ck nk root spent c_in1 c_in2 c_out1 c_out2 nf1 nf2 proof =
  Commit_sis.valid_commit_key p ck &&
  Commit_sis.valid_commit_key p nk &&
  membership_verify p c_in1 proof.tx_in1_member &&
  membership_verify p c_in2 proof.tx_in2_member &&
  proof.tx_in1_member.member_root = root &&
  proof.tx_in2_member.member_root = root &&
  proof.tx_in1_member.member_index <> proof.tx_in2_member.member_index &&
  not (List.mem nf1 spent) &&
  not (List.mem nf2 spent) &&
  nf1 <> nf2 &&
  nullifier_fs_verify p gamma ck nk c_in1 nf1 proof.tx_in1_nullifier &&
  nullifier_fs_verify p gamma ck nk c_in2 nf2 proof.tx_in2_nullifier &&
  Confidential_balance.balance_fs_verify
    p
    gamma
    ck
    (Confidential_balance.balance_commitment c_in1 c_in2 c_out1 c_out2 p.Commit_sis.cp_q)
    proof.tx_balance &&
  Confidential_range.range_fs_verify p gamma k ck c_out1 proof.tx_out1_range &&
  Confidential_range.range_fs_verify p gamma k ck c_out2 proof.tx_out2_range

let transaction_fs_verify_merkle p gamma k ck nk root spent c_in1 c_in2 c_out1 c_out2 nf1 nf2 proof =
  Commit_sis.valid_commit_key p ck &&
  Commit_sis.valid_commit_key p nk &&
  merkle_membership_verify c_in1 proof.tx_merkle_in1_member &&
  merkle_membership_verify c_in2 proof.tx_merkle_in2_member &&
  merkle_member_root proof.tx_merkle_in1_member = root &&
  merkle_member_root proof.tx_merkle_in2_member = root &&
  merkle_member_index proof.tx_merkle_in1_member <> merkle_member_index proof.tx_merkle_in2_member &&
  not (List.mem nf1 spent) &&
  not (List.mem nf2 spent) &&
  nf1 <> nf2 &&
  nullifier_fs_verify p gamma ck nk c_in1 nf1 proof.tx_merkle_in1_nullifier &&
  nullifier_fs_verify p gamma ck nk c_in2 nf2 proof.tx_merkle_in2_nullifier &&
  Confidential_balance.balance_fs_verify
    p
    gamma
    ck
    (Confidential_balance.balance_commitment c_in1 c_in2 c_out1 c_out2 p.Commit_sis.cp_q)
    proof.tx_merkle_balance &&
  Confidential_range.range_fs_verify p gamma k ck c_out1 proof.tx_merkle_out1_range &&
  Confidential_range.range_fs_verify p gamma k ck c_out2 proof.tx_merkle_out2_range

let transaction_fs_prove p gamma k ck nk ledger spent c_in1 c_in2 c_out1 c_out2 nf1 nf2
    op_in1 op_in2 op_out1 op_out2 out1_bits out1_comps out2_bits out2_comps
    y_in1 y_in2 y_balance y_out1 y_out1_pairs y_out2 y_out2_pairs =
  match
    membership_prove p ledger c_in1,
    membership_prove p ledger c_in2,
    nullifier_fs_prove p gamma ck nk c_in1 nf1 op_in1 y_in1,
    nullifier_fs_prove p gamma ck nk c_in2 nf2 op_in2 y_in2,
    Confidential_balance.balance_fs_prove
      p
      gamma
      ck
      (Confidential_balance.balance_commitment c_in1 c_in2 c_out1 c_out2 p.Commit_sis.cp_q)
      (Confidential_balance.aggregate_randomness op_in1 op_in2 op_out1 op_out2)
      y_balance,
    Confidential_range.range_fs_prove p gamma k ck c_out1 op_out1 out1_bits out1_comps y_out1 y_out1_pairs,
    Confidential_range.range_fs_prove p gamma k ck c_out2 op_out2 out2_bits out2_comps y_out2 y_out2_pairs
  with
  | Some member1, Some member2, Some nf_proof1, Some nf_proof2, Some bal_proof, Some range1, Some range2 ->
      if transaction_relation_wellformed p ck nk ledger spent c_in1 c_in2 c_out1 c_out2 nf1 nf2
           op_in1 op_in2 op_out1 op_out2 out1_bits out1_comps out2_bits out2_comps &&
         member1.member_index <> member2.member_index
      then
        Some
          (make_transaction_proof
             member1
             member2
             nf_proof1
             nf_proof2
             bal_proof
             range1
             range2)
      else None
  | _ -> None

let transaction_fs_prove_merkle p gamma k ck nk ledger spent c_in1 c_in2 c_out1 c_out2 nf1 nf2
    op_in1 op_in2 op_out1 op_out2 out1_bits out1_comps out2_bits out2_comps
    y_in1 y_in2 y_balance y_out1 y_out1_pairs y_out2 y_out2_pairs =
  match
    merkle_membership_prove ledger c_in1,
    merkle_membership_prove ledger c_in2,
    nullifier_fs_prove p gamma ck nk c_in1 nf1 op_in1 y_in1,
    nullifier_fs_prove p gamma ck nk c_in2 nf2 op_in2 y_in2,
    Confidential_balance.balance_fs_prove
      p
      gamma
      ck
      (Confidential_balance.balance_commitment c_in1 c_in2 c_out1 c_out2 p.Commit_sis.cp_q)
      (Confidential_balance.aggregate_randomness op_in1 op_in2 op_out1 op_out2)
      y_balance,
    Confidential_range.range_fs_prove p gamma k ck c_out1 op_out1 out1_bits out1_comps y_out1 y_out1_pairs,
    Confidential_range.range_fs_prove p gamma k ck c_out2 op_out2 out2_bits out2_comps y_out2 y_out2_pairs
  with
  | Some member1, Some member2, Some nf_proof1, Some nf_proof2, Some bal_proof, Some range1, Some range2 ->
      if transaction_relation_wellformed p ck nk ledger spent c_in1 c_in2 c_out1 c_out2 nf1 nf2
           op_in1 op_in2 op_out1 op_out2 out1_bits out1_comps out2_bits out2_comps &&
         merkle_member_index member1 <> merkle_member_index member2
      then
        Some
          (make_merkle_transaction_proof
             member1
             member2
             nf_proof1
             nf_proof2
             bal_proof
             range1
             range2)
      else None
  | _ -> None

let ledger_note_at notes proof =
  List.nth notes proof.member_index

let rec remove1 x = function
  | [] -> []
  | y :: ys -> if x = y then ys else y :: remove1 x ys

let ledger_apply_notes notes proof c_out1 c_out2 =
  let note1 = ledger_note_at notes proof.tx_in1_member in
  let note2 = ledger_note_at notes proof.tx_in2_member in
  let remaining = remove1 note2 (remove1 note1 notes) in
  let out1 = make_verified_note c_out1 proof.tx_out1_range in
  let out2 = make_verified_note c_out2 proof.tx_out2_range in
  out1 :: out2 :: remaining

let ledger_note_at_merkle notes proof =
  List.nth notes (merkle_member_index proof)

let ledger_apply_notes_merkle notes proof c_out1 c_out2 =
  let note1 = ledger_note_at_merkle notes proof.tx_merkle_in1_member in
  let note2 = ledger_note_at_merkle notes proof.tx_merkle_in2_member in
  let remaining = remove1 note2 (remove1 note1 notes) in
  let out1 = make_verified_note c_out1 proof.tx_merkle_out1_range in
  let out2 = make_verified_note c_out2 proof.tx_merkle_out2_range in
  out1 :: out2 :: remaining

let ledger_apply_spent spent nf1 nf2 =
  nf1 :: nf2 :: spent

let ledger_step_valid_scaffold p gamma k ck nk notes spent c_in1 c_in2 c_out1 c_out2 nf1 nf2 proof =
  let pre_root = ledger_root p (commitment_ledger notes) in
  let updated_notes = ledger_apply_notes notes proof c_out1 c_out2 in
  let updated_spent = ledger_apply_spent spent nf1 nf2 in
  let post_root = ledger_root p (commitment_ledger updated_notes) in
  ledger_valid p gamma k ck pre_root notes spent &&
  transaction_fs_verify p gamma k ck nk pre_root spent c_in1 c_in2 c_out1 c_out2 nf1 nf2 proof &&
  ledger_valid p gamma k ck post_root updated_notes updated_spent

let semantic_step_valid_scaffold = ledger_step_valid_scaffold

let ledger_step_valid_merkle p gamma k ck nk notes spent c_in1 c_in2 c_out1 c_out2 nf1 nf2 proof =
  let pre_root = merkle_ledger_root (commitment_ledger notes) in
  let updated_notes = ledger_apply_notes_merkle notes proof c_out1 c_out2 in
  let updated_spent = ledger_apply_spent spent nf1 nf2 in
  let post_root = merkle_ledger_root (commitment_ledger updated_notes) in
  ledger_valid_merkle p gamma k ck pre_root notes spent &&
  transaction_fs_verify_merkle p gamma k ck nk pre_root spent c_in1 c_in2 c_out1 c_out2 nf1 nf2 proof &&
  ledger_valid_merkle p gamma k ck post_root updated_notes updated_spent

let ledger_step_valid = ledger_step_valid_merkle
let semantic_step_valid_merkle = ledger_step_valid_merkle
let semantic_step_valid = ledger_step_valid_merkle
