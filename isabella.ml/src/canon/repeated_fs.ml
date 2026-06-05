(** Shared domain-separated Fiat-Shamir helpers for the confidential proof
    slices.

    Runtime backends use a canonical byte transcript and SHA3-256 counter-mode
    expansion:

    ["ISABELLA-CT-FS-v1" || domain_i64_le || round_i64_le ||
     field_count_i64_le || fields_i64_le...]

    The proof slices currently require binary challenges, so the low bit of the
    SHA3-256 digest is used for each round. *)

let fixed_fs_rounds = 128

let transcript_dst = "ISABELLA-CT-FS-v1"

let rotl64 x n =
  if n = 0 then x
  else Int64.logor (Int64.shift_left x n) (Int64.shift_right_logical x (64 - n))

let keccak_round_constants =
  [|
    0x0000000000000001L; 0x0000000000008082L; 0x800000000000808aL;
    0x8000000080008000L; 0x000000000000808bL; 0x0000000080000001L;
    0x8000000080008081L; 0x8000000000008009L; 0x000000000000008aL;
    0x0000000000000088L; 0x0000000080008009L; 0x000000008000000aL;
    0x000000008000808bL; 0x800000000000008bL; 0x8000000000008089L;
    0x8000000000008003L; 0x8000000000008002L; 0x8000000000000080L;
    0x000000000000800aL; 0x800000008000000aL; 0x8000000080008081L;
    0x8000000000008080L; 0x0000000080000001L; 0x8000000080008008L;
  |]

let keccak_rotation_offsets =
  [|
    0; 1; 62; 28; 27;
    36; 44; 6; 55; 20;
    3; 10; 43; 25; 39;
    41; 45; 15; 21; 8;
    18; 2; 61; 56; 14;
  |]

let keccak_f1600 state =
  let c = Array.make 5 0L in
  let d = Array.make 5 0L in
  let b = Array.make 25 0L in
  Array.iter
    (fun rc ->
      for x = 0 to 4 do
        c.(x) <-
          Int64.logxor state.(x)
            (Int64.logxor state.(x + 5)
               (Int64.logxor state.(x + 10)
                  (Int64.logxor state.(x + 15) state.(x + 20))))
      done;
      for x = 0 to 4 do
        d.(x) <-
          Int64.logxor c.((x + 4) mod 5) (rotl64 c.((x + 1) mod 5) 1)
      done;
      for y = 0 to 4 do
        for x = 0 to 4 do
          let idx = x + (5 * y) in
          state.(idx) <- Int64.logxor state.(idx) d.(x)
        done
      done;
      for y = 0 to 4 do
        for x = 0 to 4 do
          let idx = x + (5 * y) in
          let dst = y + (5 * ((2 * x + 3 * y) mod 5)) in
          b.(dst) <- rotl64 state.(idx) keccak_rotation_offsets.(idx)
        done
      done;
      for y = 0 to 4 do
        for x = 0 to 4 do
          let idx = x + (5 * y) in
          state.(idx) <-
            Int64.logxor b.(idx)
              (Int64.logand
                 (Int64.lognot b.(((x + 1) mod 5) + (5 * y)))
                 b.(((x + 2) mod 5) + (5 * y)))
        done
      done;
      state.(0) <- Int64.logxor state.(0) rc)
    keccak_round_constants

let byte_of_int64_le value offset =
  Int64.to_int
    (Int64.logand (Int64.shift_right_logical value (8 * offset)) 0xffL)

let int64_le_bytes value =
  List.init 8 (byte_of_int64_le value)

let string_bytes s =
  List.init (String.length s) (fun i -> Char.code s.[i])

let transcript_bytes domain round fields =
  string_bytes transcript_dst
  @ int64_le_bytes (Int64.of_int domain)
  @ int64_le_bytes (Int64.of_int round)
  @ int64_le_bytes (Int64.of_int (List.length fields))
  @ List.concat (List.map (fun x -> int64_le_bytes (Int64.of_int x)) fields)

let absorb_block state block rate =
  List.iteri
    (fun i byte ->
      let lane = i / 8 in
      let shift = 8 * (i mod 8) in
      let word = Int64.shift_left (Int64.of_int byte) shift in
      state.(lane) <- Int64.logxor state.(lane) word)
    block;
  ignore rate;
  keccak_f1600 state

let sha3_256 bytes =
  let rate = 136 in
  let state = Array.make 25 0L in
  let rec absorb_full_blocks remaining =
    if List.length remaining >= rate then
      let block = List.filteri (fun i _ -> i < rate) remaining in
      let rest = List.filteri (fun i _ -> i >= rate) remaining in
      absorb_block state block rate;
      absorb_full_blocks rest
    else remaining
  in
  let tail = absorb_full_blocks bytes in
  let padded = Array.make rate 0 in
  List.iteri (fun i byte -> padded.(i) <- byte land 0xff) tail;
  padded.(List.length tail) <- padded.(List.length tail) lxor 0x06;
  padded.(rate - 1) <- padded.(rate - 1) lxor 0x80;
  absorb_block state (Array.to_list padded) rate;
  List.init 32 (fun i ->
      byte_of_int64_le state.(i / 8) (i mod 8))

let binary_fs_challenge domain fields round =
  match sha3_256 (transcript_bytes domain round fields) with
  | first :: _ -> first land 1
  | [] -> failwith "sha3_256 produced no output"

let binary_fs_challenges domain fields =
  List.init fixed_fs_rounds (fun i -> binary_fs_challenge domain fields i)

let bool_fs_challenges base =
  binary_fs_challenges 1 [base]

let sigma_response_rounds respond witness masks challenges =
  List.map2 (fun mask challenge -> respond witness mask challenge) masks challenges
