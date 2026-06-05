(** Shared fixed-round deterministic Fiat-Shamir helpers for the
    confidential proof slices. *)

let fixed_fs_rounds = 8

let bool_fs_challenges base =
  List.init fixed_fs_rounds (fun i -> (base + i) mod 2)

let sigma_response_rounds respond witness masks challenges =
  List.map2 (fun mask challenge -> respond witness mask challenge) masks challenges
