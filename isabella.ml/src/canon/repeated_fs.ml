(** Shared domain-separated Fiat-Shamir helpers for the confidential proof
    slices. The arithmetic mixer mirrors the Isabelle reference model; release
    backends should instantiate this interface with a cryptographic transcript
    hash/XOF. *)

let fixed_fs_rounds = 128

let euclidean_mod x q =
  let r = x mod q in
  if r < 0 then r + q else r

let fs_challenge_cardinality = 2

let transcript_mix fields =
  List.fold_left
    (fun acc x ->
      euclidean_mod
        (acc * 257 + euclidean_mod x 2097143 + 65537)
        2097143)
    104729
    fields

let binary_fs_challenge domain fields round =
  euclidean_mod
    (transcript_mix (domain :: round :: fields))
    fs_challenge_cardinality

let binary_fs_challenges domain fields =
  List.init fixed_fs_rounds (fun i -> binary_fs_challenge domain fields i)

let bool_fs_challenges base =
  binary_fs_challenges 1 [base]

let sigma_response_rounds respond witness masks challenges =
  List.map2 (fun mask challenge -> respond witness mask challenge) masks challenges
