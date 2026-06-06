(** CSPRNG-backed helpers for confidential-transfer masks.

    These helpers are native runtime glue, not Isabelle-extracted proof
    artifacts. They use rejection sampling over bytes from the host OS CSPRNG
    and return centered integers in [-bound, bound]. *)

let max_array_length = 1_000_000

let max_sampling_bound = (1 lsl 52) - 1

let random_source = "/dev/urandom"

let validate_length length =
  if length < 0 || length > max_array_length then
    invalid_arg "confidential sampler length out of range"

let validate_bound bound =
  if bound < 0 || bound > max_sampling_bound then
    invalid_arg "confidential sampler bound out of range"

let validate_allocation count width =
  validate_length count;
  validate_length width;
  if count > 0 && width > max_array_length / count then
    invalid_arg "confidential sampler allocation out of range"

let with_random_channel f =
  let channel = open_in_bin random_source in
  Fun.protect
    ~finally:(fun () -> close_in_noerr channel)
    (fun () -> f channel)

let read_random_bytes channel len =
  really_input_string channel len

let random53 channel =
  let bytes = read_random_bytes channel 7 in
  let byte i = Int64.of_int (Char.code bytes.[i]) in
  let raw =
    List.fold_left
      Int64.logor
      0L
      [ byte 0;
        Int64.shift_left (byte 1) 8;
        Int64.shift_left (byte 2) 16;
        Int64.shift_left (byte 3) 24;
        Int64.shift_left (byte 4) 32;
        Int64.shift_left (byte 5) 40;
        Int64.shift_left (byte 6) 48 ]
  in
  Int64.logand raw (Int64.sub (Int64.shift_left 1L 53) 1L)

let bounded_int_from channel bound =
  validate_bound bound;
  let bound64 = Int64.of_int bound in
  let range = Int64.add (Int64.mul 2L bound64) 1L in
  let sample_space = Int64.shift_left 1L 53 in
  let limit = Int64.sub sample_space (Int64.rem sample_space range) in
  let rec draw () =
    let sample = random53 channel in
    if sample >= limit then draw ()
    else Int64.to_int (Int64.sub (Int64.rem sample range) bound64)
  in
  draw ()

let bounded_int bound =
  with_random_channel (fun channel -> bounded_int_from channel bound)

let int_vector_from channel length bound =
  validate_length length;
  validate_bound bound;
  List.init length (fun _ -> bounded_int_from channel bound)

let int_vector length bound =
  with_random_channel (fun channel -> int_vector_from channel length bound)

let int_vectors count length bound =
  validate_allocation count length;
  with_random_channel
    (fun channel -> List.init count (fun _ -> int_vector_from channel length bound))

let opening_from channel msg_length rand_length bound =
  validate_allocation 1 (msg_length + rand_length);
  Commit_sis.make_opening
    (int_vector_from channel msg_length bound)
    (int_vector_from channel rand_length bound)

let opening msg_length rand_length bound =
  with_random_channel (fun channel -> opening_from channel msg_length rand_length bound)

let openings count msg_length rand_length bound =
  validate_allocation count (msg_length + rand_length);
  with_random_channel
    (fun channel -> List.init count (fun _ -> opening_from channel msg_length rand_length bound))
