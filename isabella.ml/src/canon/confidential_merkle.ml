(** Cryptographic Merkle helpers for confidential note commitments.

    This module is the OCaml runtime companion to Canon/ZK/Authenticated_Merkle.
    It intentionally stays separate from Confidential_transaction while that
    transaction verifier still uses the algebraic ledger scaffold. *)

type digest = string

type membership_proof = {
  merkle_index : int;
  merkle_root : digest;
  merkle_siblings : digest list;
  merkle_directions : bool list;
}

let merkle_dst = "ISABELLA-CT-MERKLE-v1"

let merkle_leaf_tag = 0
let merkle_node_tag = 1
let merkle_empty_tag = 2

let digest_hex bytes =
  String.concat "" (List.map (Printf.sprintf "%02x") bytes)

let digest preimage =
  digest_hex (Repeated_fs.sha3_256 preimage)

let encode_i64 value =
  Repeated_fs.int64_le_bytes (Int64.of_int value)

let encode_int_vec values =
  encode_i64 (List.length values) @ List.concat (List.map encode_i64 values)

let preimage tag body =
  Repeated_fs.string_bytes merkle_dst @ encode_i64 tag @ body

let encode_leaf commitment =
  digest_hex (preimage merkle_leaf_tag (encode_int_vec commitment))

let encode_empty width =
  if width < 0 then invalid_arg "empty width must be non-negative";
  digest_hex (preimage merkle_empty_tag (encode_i64 width))

let hex_value c =
  match c with
  | '0' .. '9' -> Some (Char.code c - Char.code '0')
  | 'a' .. 'f' -> Some (10 + Char.code c - Char.code 'a')
  | _ -> None

let hex_to_bytes hex =
  if String.length hex <> 64 then None
  else
    let rec loop i acc =
      if i = String.length hex then Some (List.rev acc)
      else
        match hex_value hex.[i], hex_value hex.[i + 1] with
        | Some hi, Some lo -> loop (i + 2) (((hi lsl 4) lor lo) :: acc)
        | _ -> None
    in
    loop 0 []

let encode_node left right =
  match hex_to_bytes left, hex_to_bytes right with
  | Some left_bytes, Some right_bytes ->
      digest_hex
        (preimage
           merkle_node_tag
           (encode_int_vec left_bytes @ encode_int_vec right_bytes))
  | _ -> invalid_arg "Merkle node inputs must be canonical lowercase SHA3-256 hex digests"

let leaf commitment =
  digest (preimage merkle_leaf_tag (encode_int_vec commitment))

let empty width =
  if width < 0 then invalid_arg "empty width must be non-negative";
  digest (preimage merkle_empty_tag (encode_i64 width))

let node left right =
  match hex_to_bytes left, hex_to_bytes right with
  | Some left_bytes, Some right_bytes ->
      digest
        (preimage
           merkle_node_tag
           (encode_int_vec left_bytes @ encode_int_vec right_bytes))
  | _ -> invalid_arg "Merkle node inputs must be canonical lowercase SHA3-256 hex digests"

let all_same_width commitments width =
  List.for_all (fun c -> List.length c = width) commitments

let compress_level width level =
  let rec loop acc = function
    | [] -> List.rev acc
    | [left] -> List.rev (node left (empty width) :: acc)
    | left :: right :: rest -> loop (node left right :: acc) rest
  in
  match level with
  | [] -> []
  | [x] -> [x]
  | xs -> loop [] xs

let root commitments =
  let width =
    match commitments with
    | [] -> 0
    | first :: _ -> List.length first
  in
  if not (all_same_width commitments width) then
    invalid_arg "Merkle commitments must all have the same width";
  match commitments with
  | [] -> empty 0
  | _ ->
      let rec loop level =
        match level with
        | [] -> empty width
        | [x] -> x
        | xs -> loop (compress_level width xs)
      in
      loop (List.map leaf commitments)

let rec index_directions depth index =
  if depth <= 0 then []
  else (index mod 2 = 1) :: index_directions (depth - 1) (index / 2)

let path_root commitment siblings directions =
  let rec loop acc siblings directions =
    match siblings, directions with
    | [], [] -> Some acc
    | sibling :: rest_siblings, false :: rest_directions ->
        (try loop (node acc sibling) rest_siblings rest_directions with Invalid_argument _ -> None)
    | sibling :: rest_siblings, true :: rest_directions ->
        (try loop (node sibling acc) rest_siblings rest_directions with Invalid_argument _ -> None)
    | _ -> None
  in
  loop (leaf commitment) siblings directions

let membership_index ledger commitment =
  let rec loop index = function
    | [] -> None
    | x :: xs -> if x = commitment then Some index else loop (index + 1) xs
  in
  loop 0 ledger

let membership_prove ledger commitment =
  match membership_index ledger commitment with
  | None -> None
  | Some index ->
      let width =
        match ledger with
        | [] -> List.length commitment
        | first :: _ -> List.length first
      in
      if not (all_same_width ledger width) then
        invalid_arg "Merkle commitments must all have the same width";
      let rec loop current level siblings directions =
        match level with
        | [] -> None
        | [rt] ->
            Some
              {
                merkle_index = index;
                merkle_root = rt;
                merkle_siblings = List.rev siblings;
                merkle_directions = List.rev directions;
              }
        | _ ->
            let is_right = current mod 2 = 1 in
            let sibling =
              if is_right then List.nth level (current - 1)
              else if current + 1 < List.length level then List.nth level (current + 1)
              else empty width
            in
            loop
              (current / 2)
              (compress_level width level)
              (sibling :: siblings)
              (is_right :: directions)
      in
      loop index (List.map leaf ledger) [] []

let membership_verify commitment proof =
  proof.merkle_directions = index_directions (List.length proof.merkle_siblings) proof.merkle_index &&
  match hex_to_bytes proof.merkle_root, path_root commitment proof.merkle_siblings proof.merkle_directions with
  | Some _, Some rt -> rt = proof.merkle_root
  | _ -> false
