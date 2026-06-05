(** Isabella CLI - Command-line interface for the Isabella library *)

open Canon

(** {1 Output format} *)

type output_format = Human | Json

let output_format = ref Human

(** {1 Helpers} *)

let parse_int s =
  try Some (int_of_string s)
  with Failure _ -> None

let parse_bool s =
  match String.lowercase_ascii s with
  | "0" | "false" -> Some false
  | "1" | "true" -> Some true
  | _ -> None

let strip_outer_brackets s =
  let s = String.trim s in
  if String.length s >= 2 && s.[0] = '[' && s.[String.length s - 1] = ']'
  then String.sub s 1 (String.length s - 2)
  else s

let split_top_level s =
  let len = String.length s in
  let rec loop i depth start acc =
    if i = len then
      let part = String.trim (String.sub s start (len - start)) in
      List.rev (if part = "" then acc else part :: acc)
    else
      match s.[i] with
      | '[' -> loop (i + 1) (depth + 1) start acc
      | ']' -> loop (i + 1) (depth - 1) start acc
      | ',' when depth = 0 ->
          let part = String.trim (String.sub s start (i - start)) in
          loop (i + 1) depth (i + 1) (if part = "" then acc else part :: acc)
      | _ -> loop (i + 1) depth start acc
  in
  if String.trim s = "" then [] else loop 0 0 0 []

let parse_vec s =
  (* Parse "[1,2,3]" or "[1;2;3]" or "1,2,3" *)
  let s = String.trim s in
  let s = if String.length s > 0 && s.[0] = '[' then
    String.sub s 1 (String.length s - 2)
  else s in
  let parts = String.split_on_char ',' s in
  let parts = List.concat_map (String.split_on_char ';') parts in
  try Some (List.map (fun p -> int_of_string (String.trim p)) parts)
  with Failure _ -> None

let string_of_vec v =
  "[" ^ String.concat ", " (List.map string_of_int v) ^ "]"

let json_of_vec v =
  "[" ^ String.concat "," (List.map string_of_int v) ^ "]"

let json_of_string s =
  Printf.sprintf "%S" s

let json_of_string_list values =
  "[" ^ String.concat "," (List.map json_of_string values) ^ "]"

let[@warning "-32"] parse_mat s =
  (* Parse "[[1,2],[3,4]]" *)
  let trim_brackets s =
    let s = String.trim s in
    let s =
      if String.length s > 0 && s.[0] = '[' then
        String.sub s 1 (String.length s - 1)
      else s
    in
    if String.length s > 0 && s.[String.length s - 1] = ']' then
      String.sub s 0 (String.length s - 1)
    else s
  in
  let s = String.trim s in
  if String.length s < 2 then None
  else
    let s = String.sub s 1 (String.length s - 2) in  (* remove outer [] *)
    (* Split by "],["  *)
    let rows = Str.split (Str.regexp {|\],\[|}) s in
    try Some (List.map (fun row ->
      let row = trim_brackets row in
      List.map (fun p -> int_of_string (String.trim p))
        (String.split_on_char ',' row)
    ) rows)
    with Failure _ -> None

let parse_cube s =
  let inner = strip_outer_brackets s in
  if String.trim inner = "" then Some []
  else
    try Some (List.map (fun plane ->
      match parse_mat plane with
      | Some mat -> mat
      | None -> raise Exit
    ) (split_top_level inner))
    with Exit -> None

let parse_4d s =
  let inner = strip_outer_brackets s in
  if String.trim inner = "" then Some []
  else
    try Some (List.map (fun block ->
      match parse_cube block with
      | Some cube -> cube
      | None -> raise Exit
    ) (split_top_level inner))
    with Exit -> None

let[@warning "-32"] string_of_mat m =
  "[" ^ String.concat ", " (List.map string_of_vec m) ^ "]"

let[@warning "-32"] json_of_mat m =
  "[" ^ String.concat "," (List.map json_of_vec m) ^ "]"

let json_of_cube c =
  "[" ^ String.concat "," (List.map json_of_mat c) ^ "]"

let json_of_cb_params params =
  Printf.sprintf
    "{\"n1\":%d,\"n2\":%d,\"m\":%d,\"q\":%d,\"beta\":%d}"
    params.Commit_sis.cp_n1
    params.Commit_sis.cp_n2
    params.Commit_sis.cp_m
    params.Commit_sis.cp_q
    params.Commit_sis.cp_beta

let json_of_cb_proof proof =
  Printf.sprintf
    "{\"as\":%s,\"zs\":%s}"
    (json_of_mat proof.Confidential_balance.balance_as)
    (json_of_mat proof.Confidential_balance.balance_zs)

let json_of_cr_proof proof =
  Printf.sprintf
    "{\"bits\":%s,\"comps\":%s,\"amountAs\":%s,\"amountZs\":%s,\"pairAss\":%s,\"pairZss\":%s}"
    (json_of_mat proof.Confidential_range.range_bits)
    (json_of_mat proof.Confidential_range.range_comps)
    (json_of_mat proof.Confidential_range.range_amount_as)
    (json_of_mat proof.Confidential_range.range_amount_zs)
    (json_of_cube proof.Confidential_range.range_pair_ass)
    (json_of_cube proof.Confidential_range.range_pair_zss)

let json_of_ct_nullifier_proof proof =
  Printf.sprintf
    "{\"aCommits\":%s,\"aNullifiers\":%s,\"zMsgs\":%s,\"zRands\":%s}"
    (json_of_mat proof.Confidential_transaction.nullifier_a_commits)
    (json_of_mat proof.Confidential_transaction.nullifier_a_nullifiers)
    (json_of_mat proof.Confidential_transaction.nullifier_z_msgs)
    (json_of_mat proof.Confidential_transaction.nullifier_z_rands)

let json_of_ct_membership_proof proof =
  Printf.sprintf
    "{\"index\":%d,\"root\":%s,\"siblings\":%s,\"directions\":%s}"
    proof.Confidential_transaction.member_index
    (json_of_vec proof.Confidential_transaction.member_root)
    (json_of_mat proof.Confidential_transaction.member_siblings)
    (Printf.sprintf
       "[%s]"
       (String.concat ","
          (List.map (fun b -> if b then "true" else "false")
             proof.Confidential_transaction.member_directions)))

let json_of_ct_transaction_proof proof =
  Printf.sprintf
    "{\"in1Member\":%s,\"in2Member\":%s,\"in1Nullifier\":%s,\"in2Nullifier\":%s,\"balance\":%s,\"out1Range\":%s,\"out2Range\":%s}"
    (json_of_ct_membership_proof proof.Confidential_transaction.tx_in1_member)
    (json_of_ct_membership_proof proof.Confidential_transaction.tx_in2_member)
    (json_of_ct_nullifier_proof proof.Confidential_transaction.tx_in1_nullifier)
    (json_of_ct_nullifier_proof proof.Confidential_transaction.tx_in2_nullifier)
    (json_of_cb_proof proof.Confidential_transaction.tx_balance)
    (json_of_cr_proof proof.Confidential_transaction.tx_out1_range)
    (json_of_cr_proof proof.Confidential_transaction.tx_out2_range)

let json_of_merkle_membership_proof proof =
  Printf.sprintf
    "{\"index\":%d,\"root\":%s,\"siblings\":%s,\"directions\":%s}"
    proof.Confidential_merkle.merkle_index
    (json_of_string proof.Confidential_merkle.merkle_root)
    (json_of_string_list proof.Confidential_merkle.merkle_siblings)
    (Printf.sprintf
       "[%s]"
       (String.concat ","
          (List.map (fun b -> if b then "true" else "false")
             proof.Confidential_merkle.merkle_directions)))

let json_of_ct_merkle_transaction_proof proof =
  Printf.sprintf
    "{\"in1Member\":%s,\"in2Member\":%s,\"in1Nullifier\":%s,\"in2Nullifier\":%s,\"balance\":%s,\"out1Range\":%s,\"out2Range\":%s}"
    (json_of_merkle_membership_proof proof.Confidential_transaction.tx_merkle_in1_member)
    (json_of_merkle_membership_proof proof.Confidential_transaction.tx_merkle_in2_member)
    (json_of_ct_nullifier_proof proof.Confidential_transaction.tx_merkle_in1_nullifier)
    (json_of_ct_nullifier_proof proof.Confidential_transaction.tx_merkle_in2_nullifier)
    (json_of_cb_proof proof.Confidential_transaction.tx_merkle_balance)
    (json_of_cr_proof proof.Confidential_transaction.tx_merkle_out1_range)
    (json_of_cr_proof proof.Confidential_transaction.tx_merkle_out2_range)

(** JSON output helpers *)
let[@warning "-32"] output_result key value =
  match !output_format with
  | Human -> Printf.printf "%s = %s\n" key value
  | Json -> Printf.printf "{\"result\":%s}\n" value

let output_string_result key value =
  match !output_format with
  | Human -> Printf.printf "%s = %s\n" key value
  | Json -> Printf.printf "{\"result\":%s}\n" (json_of_string value)

type bench_stats = {
  valid : bool;
  iterations : int;
  warmup : int;
  total_ns : int64;
  mean_ns : float;
  median_ns : float;
  stdev_ns : float;
  min_ns : int64;
  max_ns : int64;
}

let now_ns () =
  Int64.of_float (Unix.gettimeofday () *. 1_000_000_000.)

let mean_ns times =
  match times with
  | [] -> 0.0
  | _ ->
    Int64.to_float (List.fold_left Int64.add 0L times)
    /. float_of_int (List.length times)

let median_ns times =
  match List.sort Int64.compare times with
  | [] -> 0.0
  | sorted ->
    let len = List.length sorted in
    if len mod 2 = 1 then
      Int64.to_float (List.nth sorted (len / 2))
    else
      let upper = Int64.to_float (List.nth sorted (len / 2)) in
      let lower = Int64.to_float (List.nth sorted ((len / 2) - 1)) in
      (lower +. upper) /. 2.0

let stdev_ns times mean =
  match times with
  | [] | [_] -> 0.0
  | _ ->
    let variance =
      List.fold_left
        (fun acc sample ->
           let diff = Int64.to_float sample -. mean in
           acc +. (diff *. diff))
        0.0
        times
      /. float_of_int (List.length times - 1)
    in
    sqrt variance

let json_of_bench_stats stats =
  Printf.sprintf
    "{\"valid\":%s,\"iterations\":%d,\"warmup\":%d,\"totalNs\":%Ld,\"meanNs\":%.3f,\"medianNs\":%.3f,\"stdevNs\":%.3f,\"minNs\":%Ld,\"maxNs\":%Ld}"
    (if stats.valid then "true" else "false")
    stats.iterations
    stats.warmup
    stats.total_ns
    stats.mean_ns
    stats.median_ns
    stats.stdev_ns
    stats.min_ns
    stats.max_ns

let output_bench_stats key stats =
  match !output_format with
  | Human ->
    Printf.printf
      "%s valid=%b, iterations=%d, warmup=%d, totalNs=%Ld, meanNs=%.3f, medianNs=%.3f, stdevNs=%.3f, minNs=%Ld, maxNs=%Ld\n"
      key
      stats.valid
      stats.iterations
      stats.warmup
      stats.total_ns
      stats.mean_ns
      stats.median_ns
      stats.stdev_ns
      stats.min_ns
      stats.max_ns
  | Json -> Printf.printf "{\"result\":%s}\n" (json_of_bench_stats stats)

let output_error msg =
  match !output_format with
  | Human -> Printf.eprintf "Error: %s\n" msg
  | Json -> Printf.printf "{\"error\":\"%s\"}\n" msg

let benchmark_bool warmup iterations verify =
  let run_once () =
    let start = now_ns () in
    let valid = verify () in
    let stop = now_ns () in
    (valid, Int64.sub stop start)
  in
  for _ = 1 to warmup do
    ignore (verify ())
  done;
  let samples = List.init iterations (fun _ -> run_once ()) in
  let valids = List.map fst samples in
  let times = List.map snd samples in
  let total_ns = List.fold_left Int64.add 0L times in
  let min_ns = List.fold_left Int64.min (List.hd times) (List.tl times) in
  let max_ns = List.fold_left Int64.max (List.hd times) (List.tl times) in
  let mean_ns = mean_ns times in
  {
    valid = List.for_all Fun.id valids;
    iterations;
    warmup;
    total_ns;
    mean_ns;
    median_ns = median_ns times;
    stdev_ns = stdev_ns times mean_ns;
    min_ns;
    max_ns;
  }

(** {1 Commands} *)

let cmd_mod_centered args =
  match args with
  | [x_str; q_str] ->
    (match parse_int x_str, parse_int q_str with
     | Some x, Some q ->
       let result = Zq.mod_centered x q in
       output_result (Printf.sprintf "mod_centered %d %d" x q) (string_of_int result)
     | _ -> output_error "Expected two integers (X Q)")
  | _ -> output_error "Usage: mod-centered X Q"

let cmd_dist0 args =
  match args with
  | [q_str; x_str] ->
    (match parse_int q_str, parse_int x_str with
     | Some q, Some x ->
       let result = Zq.dist0 q x in
       output_result (Printf.sprintf "dist0 %d %d" q x) (string_of_int result)
     | _ -> output_error "Expected two integers (Q X)")
  | _ -> output_error "Usage: dist0 Q X"

let cmd_encode_bit args =
  match args with
  | [q_str; b_str] ->
    (match parse_int q_str, parse_bool b_str with
     | Some q, Some b ->
       let result = Zq.encode_bit q b in
       output_result (Printf.sprintf "encode_bit %d %b" q b) (string_of_int result)
     | _ -> output_error "Expected integer Q and boolean B")
  | _ -> output_error "Usage: encode-bit Q B"

let cmd_decode_bit args =
  match args with
  | [q_str; x_str] ->
    (match parse_int q_str, parse_int x_str with
     | Some q, Some x ->
       let result = Zq.decode_bit q x in
       output_result (Printf.sprintf "decode_bit %d %d" q x) (if result then "true" else "false")
     | _ -> output_error "Expected two integers (Q X)")
  | _ -> output_error "Usage: decode-bit Q X"

let cmd_inner_prod args =
  match args with
  | [v1_str; v2_str] ->
    (match parse_vec v1_str, parse_vec v2_str with
     | Some v1, Some v2 ->
       let result = Listvec.inner_prod v1 v2 in
       output_result (Printf.sprintf "inner_prod %s %s" (string_of_vec v1) (string_of_vec v2)) (string_of_int result)
     | _ -> output_error "Expected two vectors")
  | _ -> output_error "Usage: inner-prod \"[v1]\" \"[v2]\""

let cmd_vec_add args =
  match args with
  | [v1_str; v2_str] ->
    (match parse_vec v1_str, parse_vec v2_str with
     | Some v1, Some v2 ->
       let result = Listvec.vec_add v1 v2 in
       (match !output_format with
        | Human -> Printf.printf "vec_add %s %s = %s\n" (string_of_vec v1) (string_of_vec v2) (string_of_vec result)
        | Json -> Printf.printf "{\"result\":%s}\n" (json_of_vec result))
     | _ -> output_error "Expected two vectors")
  | _ -> output_error "Usage: vec-add \"[v1]\" \"[v2]\""

let cmd_transpose args =
  match args with
  | [m_str] ->
    (match parse_mat m_str with
     | Some m ->
       let result = Listvec.transpose m in
       (match !output_format with
        | Human -> Printf.printf "transpose %s = %s\n" (string_of_mat m) (string_of_mat result)
        | Json -> Printf.printf "{\"result\":%s}\n" (json_of_mat result))
     | _ -> output_error "Expected a matrix")
  | _ -> output_error "Usage: transpose \"[[row1],[row2]]\""

let cmd_mat_vec_mult args =
  match args with
  | [m_str; v_str; q_str] ->
    (match parse_mat m_str, parse_vec v_str, parse_int q_str with
     | Some m, Some v, Some q ->
       let result = Zq.mat_vec_mult_mod m v q in
       (match !output_format with
        | Human ->
          Printf.printf "mat_vec_mult_mod\n  A = %s\n  v = %s\n  q = %d\n  result = %s\n"
            (string_of_mat m) (string_of_vec v) q (string_of_vec result)
        | Json ->
          Printf.printf "{\"result\":%s}\n" (json_of_vec result))
     | _ -> output_error "Expected matrix M, vector V, and modulus Q")
  | _ -> output_error "Usage: mat-vec-mult \"[[row1],[row2]]\" \"[v]\" Q"

(** {1 NTT Commands} *)

let cmd_ntt_fast args =
  match args with
  | [vec_str; omega_str; q_str; n_str] ->
    (match parse_vec vec_str, parse_int omega_str, parse_int q_str, parse_int n_str with
     | Some vec, Some omega, Some q, Some n ->
       let result = Ntt.ntt_fast vec omega q n in
       (match !output_format with
        | Human -> Printf.printf "ntt_fast (n=%d, q=%d, ω=%d)\n  input:  %s\n  output: %s\n" n q omega (string_of_vec vec) (string_of_vec result)
        | Json -> Printf.printf "{\"input\":%s,\"output\":%s,\"n\":%d,\"q\":%d,\"omega\":%d}\n" (json_of_vec vec) (json_of_vec result) n q omega)
     | _ -> output_error "Expected: vector, omega, q, n")
  | _ -> output_error "Usage: ntt-fast \"[vec]\" OMEGA Q N"

let cmd_intt_fast args =
  match args with
  | [vec_str; omega_str; q_str; n_str] ->
    (match parse_vec vec_str, parse_int omega_str, parse_int q_str, parse_int n_str with
     | Some vec, Some omega, Some q, Some n ->
       let result = Ntt.intt_fast vec omega q n in
       (match !output_format with
        | Human -> Printf.printf "intt_fast (n=%d, q=%d, ω=%d)\n  input:  %s\n  output: %s\n" n q omega (string_of_vec vec) (string_of_vec result)
        | Json -> Printf.printf "{\"input\":%s,\"output\":%s,\"n\":%d,\"q\":%d,\"omega\":%d}\n" (json_of_vec vec) (json_of_vec result) n q omega)
     | _ -> output_error "Expected: vector, omega, q, n")
  | _ -> output_error "Usage: intt-fast \"[vec]\" OMEGA Q N"

let cmd_ntt_pointwise args =
  match args with
  | [v1_str; v2_str; q_str] ->
    (match parse_vec v1_str, parse_vec v2_str, parse_int q_str with
     | Some v1, Some v2, Some q ->
       let result = Ntt.ntt_pointwise_mult v1 v2 q in
       (match !output_format with
        | Human -> Printf.printf "ntt_pointwise_mult (q=%d)\n  a: %s\n  b: %s\n  result: %s\n" q (string_of_vec v1) (string_of_vec v2) (string_of_vec result)
        | Json -> Printf.printf "{\"a\":%s,\"b\":%s,\"result\":%s,\"q\":%d}\n" (json_of_vec v1) (json_of_vec v2) (json_of_vec result) q)
     | _ -> output_error "Expected: two vectors and q")
  | _ -> output_error "Usage: ntt-pointwise \"[v1]\" \"[v2]\" Q"

let cmd_power_mod args =
  match args with
  | [a_str; k_str; m_str] ->
    (match parse_int a_str, parse_int k_str, parse_int m_str with
     | Some a, Some k, Some m ->
       let result = Ntt.power_mod a k m in
       (match !output_format with
        | Human -> Printf.printf "power_mod %d %d %d = %d\n" a k m result
        | Json -> Printf.printf "{\"result\":%d}\n" result)
     | _ -> output_error "Expected three integers")
  | _ -> output_error "Usage: power-mod A K M"

let cmd_mod_inverse args =
  match args with
  | [a_str; m_str] ->
    (match parse_int a_str, parse_int m_str with
     | Some a, Some m ->
       let result = Ntt.mod_inverse a m in
       (match !output_format with
        | Human -> Printf.printf "mod_inverse %d %d = %d\n" a m result
        | Json -> Printf.printf "{\"result\":%d}\n" result)
     | _ -> output_error "Expected two integers")
  | _ -> output_error "Usage: mod-inverse A M"

let cmd_is_primitive_root args =
  match args with
  | [omega_str; n_str; q_str] ->
    (match parse_int omega_str, parse_int n_str, parse_int q_str with
     | Some omega, Some n, Some q ->
       let result = Ntt.is_primitive_root omega n q in
       (match !output_format with
        | Human -> Printf.printf "is_primitive_root %d %d %d = %b\n" omega n q result
        | Json -> Printf.printf "{\"result\":%b}\n" result)
     | _ -> output_error "Expected three integers")
  | _ -> output_error "Usage: is-primitive-root OMEGA N Q"

(** {1 Polynomial Ring Commands} *)

let cmd_poly_mult args =
  match args with
  | [p1_str; p2_str] ->
    (match parse_vec p1_str, parse_vec p2_str with
     | Some p1, Some p2 ->
       let result = Polymod.poly_mult p1 p2 in
       (match !output_format with
        | Human -> Printf.printf "poly_mult\n  a: %s\n  b: %s\n  result: %s\n" (string_of_vec p1) (string_of_vec p2) (string_of_vec result)
        | Json -> Printf.printf "{\"a\":%s,\"b\":%s,\"result\":%s}\n" (json_of_vec p1) (json_of_vec p2) (json_of_vec result))
     | _ -> output_error "Expected two polynomials")
  | _ -> output_error "Usage: poly-mult \"[p1]\" \"[p2]\""

let cmd_ring_mult args =
  match args with
  | [p1_str; p2_str; n_str; q_str] ->
    (match parse_vec p1_str, parse_vec p2_str, parse_int n_str, parse_int q_str with
     | Some p1, Some p2, Some n, Some q ->
       let result = Polymod.ring_mult p1 p2 n q in
       (match !output_format with
        | Human -> Printf.printf "ring_mult (n=%d, q=%d) mod X^n+1\n  a: %s\n  b: %s\n  result: %s\n" n q (string_of_vec p1) (string_of_vec p2) (string_of_vec result)
        | Json -> Printf.printf "{\"a\":%s,\"b\":%s,\"result\":%s,\"n\":%d,\"q\":%d}\n" (json_of_vec p1) (json_of_vec p2) (json_of_vec result) n q)
     | _ -> output_error "Expected two polynomials, n, and q")
  | _ -> output_error "Usage: ring-mult \"[p1]\" \"[p2]\" N Q"

(** {1 Kyber Commands} *)

let cmd_kyber_ntt args =
  match args with
  | [vec_str] ->
    (match parse_vec vec_str with
     | Some vec ->
       let result = Kyber.kyber_ntt vec in
       (match !output_format with
        | Human -> Printf.printf "kyber_ntt\n  input:  %s\n  output: %s\n" (string_of_vec vec) (string_of_vec result)
        | Json -> Printf.printf "{\"input\":%s,\"output\":%s}\n" (json_of_vec vec) (json_of_vec result))
     | _ -> output_error "Expected a vector")
  | _ -> output_error "Usage: kyber-ntt \"[vec]\""

let cmd_kyber_intt args =
  match args with
  | [vec_str] ->
    (match parse_vec vec_str with
     | Some vec ->
       let result = Kyber.kyber_intt vec in
       (match !output_format with
        | Human -> Printf.printf "kyber_intt\n  input:  %s\n  output: %s\n" (string_of_vec vec) (string_of_vec result)
        | Json -> Printf.printf "{\"input\":%s,\"output\":%s}\n" (json_of_vec vec) (json_of_vec result))
     | _ -> output_error "Expected a vector")
  | _ -> output_error "Usage: kyber-intt \"[vec]\""

let cmd_kyber_poly_mult args =
  match args with
  | [p1_str; p2_str] ->
    (match parse_vec p1_str, parse_vec p2_str with
     | Some p1, Some p2 ->
       let result = Kyber.kyber_poly_mult_ntt p1 p2 in
       (match !output_format with
        | Human -> Printf.printf "kyber_poly_mult_ntt\n  a: %s\n  b: %s\n  result: %s\n" (string_of_vec p1) (string_of_vec p2) (string_of_vec result)
        | Json -> Printf.printf "{\"a\":%s,\"b\":%s,\"result\":%s}\n" (json_of_vec p1) (json_of_vec p2) (json_of_vec result))
     | _ -> output_error "Expected two polynomials")
  | _ -> output_error "Usage: kyber-poly-mult \"[p1]\" \"[p2]\""

let cmd_kyber_encode_msg args =
  match args with
  | [msg_str] ->
    (match parse_vec msg_str with
     | Some msg ->
       let result = Kyber.kyber_encode_msg msg in
       (match !output_format with
        | Human -> Printf.printf "kyber_encode_msg\n  input:  %s\n  output: %s\n" (string_of_vec msg) (string_of_vec result)
        | Json -> Printf.printf "{\"input\":%s,\"output\":%s}\n" (json_of_vec msg) (json_of_vec result))
     | _ -> output_error "Expected a message vector (0s and 1s)")
  | _ -> output_error "Usage: kyber-encode-msg \"[0,1,0,1,...]\""

let cmd_kyber_decode_msg args =
  match args with
  | [poly_str] ->
    (match parse_vec poly_str with
     | Some poly ->
       let result = Kyber.kyber_decode_msg poly in
       (match !output_format with
        | Human -> Printf.printf "kyber_decode_msg\n  input:  %s\n  output: %s\n" (string_of_vec poly) (string_of_vec result)
        | Json -> Printf.printf "{\"input\":%s,\"output\":%s}\n" (json_of_vec poly) (json_of_vec result))
     | _ -> output_error "Expected a polynomial")
  | _ -> output_error "Usage: kyber-decode-msg \"[poly]\""

(** {1 Dilithium Commands} *)

let cmd_dil_mod_centered args =
  match args with
  | [r_str; m_str] ->
    (match parse_int r_str, parse_int m_str with
     | Some r, Some m ->
       let result = Dilithium.mod_centered r m in
       (match !output_format with
        | Human -> Printf.printf "mod_centered %d %d = %d\n" r m result
        | Json -> Printf.printf "{\"r\":%d,\"m\":%d,\"result\":%d}\n" r m result)
     | _ -> output_error "Expected two integers")
  | _ -> output_error "Usage: dil-mod-centered R M"

let cmd_dil_power2round args =
  match args with
  | [r_str; d_str] ->
    (match parse_int r_str, parse_int d_str with
     | Some r, Some d ->
       let (r1, r0) = Dilithium.power2round_coeff r d in
       (match !output_format with
        | Human -> Printf.printf "power2round %d %d = (r1=%d, r0=%d)\n" r d r1 r0
        | Json -> Printf.printf "{\"r\":%d,\"d\":%d,\"r1\":%d,\"r0\":%d}\n" r d r1 r0)
     | _ -> output_error "Expected two integers")
  | _ -> output_error "Usage: dil-power2round R D"

let cmd_dil_decompose args =
  match args with
  | [r_str; alpha_str] ->
    (match parse_int r_str, parse_int alpha_str with
     | Some r, Some alpha ->
       let (r1, r0) = Dilithium.decompose_coeff r alpha in
       (match !output_format with
        | Human -> Printf.printf "decompose %d %d = (r1=%d, r0=%d)\n" r alpha r1 r0
        | Json -> Printf.printf "{\"r\":%d,\"alpha\":%d,\"r1\":%d,\"r0\":%d}\n" r alpha r1 r0)
     | _ -> output_error "Expected two integers")
  | _ -> output_error "Usage: dil-decompose R ALPHA"

let cmd_dil_highbits args =
  match args with
  | [r_str; alpha_str] ->
    (match parse_int r_str, parse_int alpha_str with
     | Some r, Some alpha ->
       let result = Dilithium.highbits_coeff r alpha in
       (match !output_format with
        | Human -> Printf.printf "highbits %d %d = %d\n" r alpha result
        | Json -> Printf.printf "{\"r\":%d,\"alpha\":%d,\"result\":%d}\n" r alpha result)
     | _ -> output_error "Expected two integers")
  | _ -> output_error "Usage: dil-highbits R ALPHA"

let cmd_dil_lowbits args =
  match args with
  | [r_str; alpha_str] ->
    (match parse_int r_str, parse_int alpha_str with
     | Some r, Some alpha ->
       let result = Dilithium.lowbits_coeff r alpha in
       (match !output_format with
        | Human -> Printf.printf "lowbits %d %d = %d\n" r alpha result
        | Json -> Printf.printf "{\"r\":%d,\"alpha\":%d,\"result\":%d}\n" r alpha result)
     | _ -> output_error "Expected two integers")
  | _ -> output_error "Usage: dil-lowbits R ALPHA"

let cmd_dil_makehint args =
  match args with
  | [z_str; r_str; alpha_str] ->
    (match parse_int z_str, parse_int r_str, parse_int alpha_str with
     | Some z, Some r, Some alpha ->
       let result = Dilithium.makehint_coeff z r alpha in
       (match !output_format with
        | Human -> Printf.printf "makehint z=%d r=%d alpha=%d = %d\n" z r alpha result
        | Json -> Printf.printf "{\"z\":%d,\"r\":%d,\"alpha\":%d,\"result\":%d}\n" z r alpha result)
     | _ -> output_error "Expected three integers")
  | _ -> output_error "Usage: dil-makehint Z R ALPHA"

let cmd_dil_usehint args =
  match args with
  | [h_str; r_str; alpha_str] ->
    (match parse_int h_str, parse_int r_str, parse_int alpha_str with
     | Some h, Some r, Some alpha ->
       let result = Dilithium.usehint_coeff h r alpha in
       (match !output_format with
        | Human -> Printf.printf "usehint h=%d r=%d alpha=%d = %d\n" h r alpha result
        | Json -> Printf.printf "{\"h\":%d,\"r\":%d,\"alpha\":%d,\"result\":%d}\n" h r alpha result)
     | _ -> output_error "Expected three integers")
  | _ -> output_error "Usage: dil-usehint H R ALPHA"

let cmd_dil_params args =
  match args with
  | [variant_str] ->
    let params = match String.lowercase_ascii variant_str with
      | "44" | "mldsa44" | "ml-dsa-44" -> Some Dilithium.mldsa44_params
      | "65" | "mldsa65" | "ml-dsa-65" -> Some Dilithium.mldsa65_params
      | "87" | "mldsa87" | "ml-dsa-87" -> Some Dilithium.mldsa87_params
      | _ -> None
    in
    (match params with
     | Some p ->
       (match !output_format with
        | Human ->
          Printf.printf "ML-DSA-%s parameters:\n" variant_str;
          Printf.printf "  n=%d, q=%d, k=%d, l=%d\n" p.dil_n p.dil_q p.dil_k p.dil_l;
          Printf.printf "  eta=%d, tau=%d, beta=%d\n" p.dil_eta p.dil_tau p.dil_beta;
          Printf.printf "  gamma1=%d, gamma2=%d, d=%d, omega=%d\n" p.dil_gamma1 p.dil_gamma2 p.dil_d p.dil_omega
        | Json ->
          Printf.printf "{\"n\":%d,\"q\":%d,\"k\":%d,\"l\":%d,\"eta\":%d,\"tau\":%d,\"beta\":%d,\"gamma1\":%d,\"gamma2\":%d,\"d\":%d,\"omega\":%d}\n"
            p.dil_n p.dil_q p.dil_k p.dil_l p.dil_eta p.dil_tau p.dil_beta p.dil_gamma1 p.dil_gamma2 p.dil_d p.dil_omega)
     | None -> output_error "Unknown variant. Use 44, 65, or 87")
  | _ -> output_error "Usage: dil-params VARIANT (44, 65, or 87)"

let cmd_dil_check_bound args =
  match args with
  | [value_str; bound_str] ->
    (match parse_int value_str, parse_int bound_str with
     | Some value, Some bnd ->
       let result = Dilithium.coeff_in_range value bnd in
       (match !output_format with
        | Human -> Printf.printf "coeff_in_range %d %d = %b (|%d| < %d)\n" value bnd result (abs value) bnd
        | Json -> Printf.printf "{\"value\":%d,\"bound\":%d,\"result\":%b}\n" value bnd result)
     | _ -> output_error "Expected two integers")
  | _ -> output_error "Usage: dil-check-bound VALUE BOUND"

let cmd_dil_hint_weight args =
  match args with
  | [hints_str] ->
    (* Parse [[1,0,1],[0,1,0]] format *)
    (try
       let hints_str = String.trim hints_str in
       let inner = String.sub hints_str 1 (String.length hints_str - 2) in
       let rows = Str.split (Str.regexp {|\],\[|}) inner in
       let parse_row row =
         let row = String.trim row in
         (* Strip leading [ if present *)
         let row = if String.length row > 0 && row.[0] = '[' then
           String.sub row 1 (String.length row - 1)
         else row in
         (* Strip trailing ] if present *)
         let row = if String.length row > 0 && row.[String.length row - 1] = ']' then
           String.sub row 0 (String.length row - 1)
         else row in
         List.map (fun p -> int_of_string (String.trim p)) (String.split_on_char ',' row)
       in
       let hints = List.map parse_row rows in
       let result = Dilithium.hint_weight hints in
       (match !output_format with
        | Human -> Printf.printf "hint_weight = %d\n" result
        | Json -> Printf.printf "{\"result\":%d}\n" result)
     with _ -> output_error "Expected hint matrix [[h1],[h2],...]")
  | _ -> output_error "Usage: dil-hint-weight \"[[h1],[h2],...]\""

(** {1 Confidential Balance Commands} *)

let make_cb_params m_str n2_str q_str beta_str =
  match parse_int m_str, parse_int n2_str, parse_int q_str, parse_int beta_str with
  | Some m, Some n2, Some q, Some beta ->
    Some (Confidential_balance.make_scalar_commit_params m n2 q beta)
  | _ -> None

let make_scalar_opening amount rand =
  Commit_sis.make_opening [amount] rand

let rec make_scalar_openings values rands =
  match values, rands with
  | [], [] -> Some []
  | value :: rest_values, rand :: rest_rands ->
      Option.map (fun rest -> make_scalar_opening value rand :: rest)
        (make_scalar_openings rest_values rest_rands)
  | _ -> None

let rec make_verified_notes commitments bits comps amount_as amount_zs pair_as pair_zs =
  match commitments, bits, comps, amount_as, amount_zs, pair_as, pair_zs with
  | [], [], [], [], [], [], [] -> Some []
  | commitment :: rest_commitments,
    bit_rows :: rest_bits,
    comp_rows :: rest_comps,
    amount_a :: rest_amount_as,
    amount_z :: rest_amount_zs,
    pair_rows :: rest_pair_as,
    pair_z_rows :: rest_pair_zs ->
      Option.map
        (fun rest ->
           Confidential_transaction.make_verified_note
             commitment
             (Confidential_range.make_range_proof bit_rows comp_rows amount_a amount_z pair_rows pair_z_rows)
           :: rest)
        (make_verified_notes
           rest_commitments
           rest_bits
           rest_comps
           rest_amount_as
           rest_amount_zs
           rest_pair_as
           rest_pair_zs)
  | _ -> None

let cmd_cb_params args =
  match args with
  | [m_str; n2_str; q_str; beta_str] ->
    (match make_cb_params m_str n2_str q_str beta_str with
     | Some params ->
       (match !output_format with
        | Human -> Printf.printf "scalar_commit_params = %s\n" (json_of_cb_params params)
        | Json -> Printf.printf "%s\n" (json_of_cb_params params))
     | None -> output_error "Expected four integers (M N2 Q BETA)")
  | _ -> output_error "Usage: cb-params M N2 Q BETA"

let cmd_cb_valid_params args =
  match args with
  | [m_str; n2_str; q_str; beta_str] ->
    (match make_cb_params m_str n2_str q_str beta_str with
     | Some params ->
       let result = Confidential_balance.valid_scalar_commit_params params in
       output_result "valid_scalar_commit_params" (if result then "true" else "false")
     | None -> output_error "Expected four integers (M N2 Q BETA)")
  | _ -> output_error "Usage: cb-valid-params M N2 Q BETA"

let cmd_cb_rand_commit_key args =
  match args with
  | [m_str; n2_str; q_str; beta_str; ck_str] ->
    (match make_cb_params m_str n2_str q_str beta_str, parse_mat ck_str with
     | Some params, Some ck ->
       let result = Confidential_balance.rand_commit_key params ck in
       (match !output_format with
        | Human -> Printf.printf "rand_commit_key = %s\n" (string_of_mat result)
        | Json -> Printf.printf "{\"result\":%s}\n" (json_of_mat result))
     | _ -> output_error "Expected params (M N2 Q BETA) and a commitment-key matrix")
  | _ -> output_error "Usage: cb-rand-commit-key M N2 Q BETA \"[[row1],[row2]]\""

let cmd_cb_rand_commit args =
  match args with
  | [m_str; n2_str; q_str; beta_str; ck_str; r_str] ->
    (match make_cb_params m_str n2_str q_str beta_str, parse_mat ck_str, parse_vec r_str with
     | Some params, Some ck, Some r ->
       let result = Confidential_balance.rand_commit params ck r in
       (match !output_format with
        | Human -> Printf.printf "rand_commit = %s\n" (string_of_vec result)
        | Json -> Printf.printf "{\"result\":%s}\n" (json_of_vec result))
     | _ -> output_error "Expected params (M N2 Q BETA), a commitment-key matrix, and a witness vector")
  | _ -> output_error "Usage: cb-rand-commit M N2 Q BETA \"[[row1],[row2]]\" \"[r]\""

let cmd_cb_valid_witness args =
  match args with
  | [m_str; n2_str; q_str; beta_str; r_str] ->
    (match make_cb_params m_str n2_str q_str beta_str, parse_vec r_str with
     | Some params, Some r ->
       let result = Confidential_balance.valid_balance_witness params r in
       output_result "valid_balance_witness" (if result then "true" else "false")
     | _ -> output_error "Expected params (M N2 Q BETA) and a witness vector")
  | _ -> output_error "Usage: cb-valid-witness M N2 Q BETA \"[r]\""

let cmd_cb_valid_mask args =
  match args with
  | [m_str; n2_str; q_str; beta_str; gamma_str; y_str] ->
    (match make_cb_params m_str n2_str q_str beta_str, parse_int gamma_str, parse_vec y_str with
     | Some params, Some gamma, Some y ->
       let result = Confidential_balance.valid_balance_mask params gamma y in
       output_result "valid_balance_mask" (if result then "true" else "false")
     | _ -> output_error "Expected params (M N2 Q BETA), gamma, and a mask vector")
  | _ -> output_error "Usage: cb-valid-mask M N2 Q BETA GAMMA \"[y]\""

let cmd_cb_valid_response args =
  match args with
  | [m_str; n2_str; q_str; beta_str; gamma_str; challenge_str; z_str] ->
    (match make_cb_params m_str n2_str q_str beta_str, parse_int gamma_str, parse_int challenge_str, parse_vec z_str with
     | Some params, Some gamma, Some challenge, Some z ->
       let result = Confidential_balance.valid_balance_response params gamma challenge z in
       output_result "valid_balance_response" (if result then "true" else "false")
     | _ -> output_error "Expected params (M N2 Q BETA), gamma, challenge, and a response vector")
  | _ -> output_error "Usage: cb-valid-response M N2 Q BETA GAMMA CHALLENGE \"[z]\""

let cmd_cb_balance_commitment args =
  match args with
  | [c_in1_str; c_in2_str; c_out1_str; c_out2_str; q_str] ->
    (match parse_vec c_in1_str, parse_vec c_in2_str, parse_vec c_out1_str, parse_vec c_out2_str, parse_int q_str with
     | Some c_in1, Some c_in2, Some c_out1, Some c_out2, Some q ->
       let result = Confidential_balance.balance_commitment c_in1 c_in2 c_out1 c_out2 q in
       (match !output_format with
        | Human -> Printf.printf "balance_commitment = %s\n" (string_of_vec result)
        | Json -> Printf.printf "{\"result\":%s}\n" (json_of_vec result))
     | _ -> output_error "Expected four commitment vectors and modulus Q")
  | _ -> output_error "Usage: cb-balance-commitment \"[c1]\" \"[c2]\" \"[c3]\" \"[c4]\" Q"

let cmd_cb_canonical_challenge args =
  match args with
  | [m_str; n2_str; q_str; beta_str; ck_str; c_str; a_str] ->
    (match make_cb_params m_str n2_str q_str beta_str, parse_mat ck_str, parse_vec c_str, parse_vec a_str with
     | Some params, Some ck, Some c, Some a ->
       let result = Confidential_balance.canonical_balance_challenge params ck c a in
       output_result "canonical_balance_challenge" (string_of_int result)
     | _ -> output_error "Expected params (M N2 Q BETA), a commitment-key matrix, a commitment vector, and an announcement vector")
  | _ -> output_error "Usage: cb-canonical-challenge M N2 Q BETA \"[[row1],[row2]]\" \"[c]\" \"[a]\""

let cmd_cb_sigma_commit args =
  match args with
  | [m_str; n2_str; q_str; beta_str; ck_str; y_str] ->
    (match make_cb_params m_str n2_str q_str beta_str, parse_mat ck_str, parse_vec y_str with
     | Some params, Some ck, Some y ->
       let result = Confidential_balance.balance_sigma_commit params ck y in
       (match !output_format with
        | Human -> Printf.printf "balance_sigma_commit = %s\n" (string_of_vec result)
        | Json -> Printf.printf "{\"result\":%s}\n" (json_of_vec result))
     | _ -> output_error "Expected params (M N2 Q BETA), a commitment-key matrix, and a mask vector")
  | _ -> output_error "Usage: cb-sigma-commit M N2 Q BETA \"[[row1],[row2]]\" \"[y]\""

let cmd_cb_sigma_respond args =
  match args with
  | [r_str; y_str; challenge_str] ->
    (match parse_vec r_str, parse_vec y_str, parse_int challenge_str with
     | Some r, Some y, Some challenge ->
       let result = Confidential_balance.balance_sigma_respond r y challenge in
       (match !output_format with
        | Human -> Printf.printf "balance_sigma_respond = %s\n" (string_of_vec result)
        | Json -> Printf.printf "{\"result\":%s}\n" (json_of_vec result))
     | _ -> output_error "Expected a witness vector, a mask vector, and an integer challenge")
  | _ -> output_error "Usage: cb-sigma-respond \"[r]\" \"[y]\" CHALLENGE"

let cmd_cb_sigma_verify args =
  match args with
  | [m_str; n2_str; q_str; beta_str; gamma_str; ck_str; c_str; a_str; challenge_str; z_str] ->
    (match make_cb_params m_str n2_str q_str beta_str, parse_int gamma_str, parse_mat ck_str, parse_vec c_str, parse_vec a_str, parse_int challenge_str, parse_vec z_str with
     | Some params, Some gamma, Some ck, Some c, Some a, Some challenge, Some z ->
       let result = Confidential_balance.balance_sigma_verify params gamma ck c a challenge z in
       output_result "balance_sigma_verify" (if result then "true" else "false")
     | _ -> output_error "Expected params, gamma, a commitment-key matrix, a commitment vector, an announcement vector, an integer challenge, and a response vector")
  | _ -> output_error "Usage: cb-sigma-verify M N2 Q BETA GAMMA \"[[row1],[row2]]\" \"[c]\" \"[a]\" CHALLENGE \"[z]\""

let cmd_cb_prove args =
  match args with
  | [m_str; n2_str; q_str; beta_str; gamma_str; ck_str; c_str; r_str; ys_str] ->
    (match make_cb_params m_str n2_str q_str beta_str, parse_int gamma_str, parse_mat ck_str, parse_vec c_str, parse_vec r_str, parse_mat ys_str with
     | Some params, Some gamma, Some ck, Some c, Some r, Some ys ->
       (match Confidential_balance.balance_fs_prove params gamma ck c r ys with
        | Some proof ->
          (match !output_format with
           | Human -> Printf.printf "balance_fs_proof = %s\n" (json_of_cb_proof proof)
           | Json -> Printf.printf "%s\n" (json_of_cb_proof proof))
        | None ->
          (match !output_format with
           | Human -> print_endline "balance_fs_proof = null"
           | Json -> print_endline "null"))
     | _ -> output_error "Expected params, gamma, a commitment-key matrix, a commitment vector, a witness vector, and a matrix of mask vectors")
  | _ -> output_error "Usage: cb-prove M N2 Q BETA GAMMA \"[[row1],[row2]]\" \"[c]\" \"[r]\" \"[[y1],[y2],...]\""

let cmd_cb_verify args =
  match args with
  | [m_str; n2_str; q_str; beta_str; gamma_str; ck_str; c_str; as_str; zs_str] ->
    (match make_cb_params m_str n2_str q_str beta_str, parse_int gamma_str, parse_mat ck_str, parse_vec c_str, parse_mat as_str, parse_mat zs_str with
     | Some params, Some gamma, Some ck, Some c, Some as_, Some zs ->
       let proof = Confidential_balance.make_balance_proof as_ zs in
       let result = Confidential_balance.balance_fs_verify params gamma ck c proof in
       output_result "balance_fs_verify" (if result then "true" else "false")
     | _ -> output_error "Expected params, gamma, a commitment-key matrix, a commitment vector, an announcement matrix, and a response matrix")
  | _ -> output_error "Usage: cb-verify M N2 Q BETA GAMMA \"[[row1],[row2]]\" \"[c]\" \"[[a1],[a2],...]\" \"[[z1],[z2],...]\""

(** {1 Confidential Range Commands} *)

let cmd_cr_amount_commitment args =
  match args with
  | [m_str; n2_str; q_str; beta_str; ck_str; c_amount_str; c_bits_str] ->
    (match make_cb_params m_str n2_str q_str beta_str, parse_mat ck_str, parse_vec c_amount_str, parse_mat c_bits_str with
     | Some params, Some ck, Some c_amount, Some c_bits ->
       let result = Confidential_range.range_amount_commitment params ck c_amount c_bits in
       (match !output_format with
        | Human -> Printf.printf "range_amount_commitment = %s\n" (string_of_vec result)
        | Json -> Printf.printf "{\"result\":%s}\n" (json_of_vec result))
     | _ -> output_error "Expected params, commitment key, amount commitment, and bit commitments")
  | _ -> output_error "Usage: cr-amount-commitment M N2 Q BETA \"[[ck]]\" \"[cAmount]\" \"[[cBit1],[cBit2]]\""

let cmd_cr_prove args =
  match args with
  | [m_str; n2_str; q_str; beta_str; gamma_str; k_str; ck_str; c_amount_str; amount_str; amount_rand_str; bits_str; bit_rands_str; comps_str; comp_rands_str; y_amounts_str; y_pairss_str] ->
    (match make_cb_params m_str n2_str q_str beta_str, parse_int gamma_str, parse_int k_str, parse_mat ck_str, parse_vec c_amount_str, parse_int amount_str, parse_vec amount_rand_str, parse_vec bits_str, parse_mat bit_rands_str, parse_vec comps_str, parse_mat comp_rands_str, parse_mat y_amounts_str, parse_cube y_pairss_str with
     | Some params, Some gamma, Some k, Some ck, Some c_amount, Some amount, Some amount_rand, Some bits, Some bit_rands, Some comps, Some comp_rands, Some y_amounts, Some y_pairss ->
       (match make_scalar_openings bits bit_rands, make_scalar_openings comps comp_rands with
        | Some bit_ops, Some comp_ops ->
          (match Confidential_range.range_fs_prove params gamma k ck c_amount (make_scalar_opening amount amount_rand) bit_ops comp_ops y_amounts y_pairss with
           | Some proof ->
             (match !output_format with
              | Human -> Printf.printf "range_fs_proof = %s\n" (json_of_cr_proof proof)
              | Json -> Printf.printf "%s\n" (json_of_cr_proof proof))
           | None ->
             (match !output_format with
              | Human -> print_endline "range_fs_proof = null"
              | Json -> print_endline "null"))
        | _ -> output_error "Bit/complement counts must match their randomness matrices")
     | _ -> output_error "Expected params, gamma, commitment key, amount commitment, scalar opening, bit openings, complement openings, and masks")
  | _ -> output_error "Usage: cr-prove M N2 Q BETA GAMMA K \"[[ck]]\" \"[cAmount]\" AMOUNT \"[amountRand]\" \"[bits]\" \"[[bitRands]]\" \"[comps]\" \"[[compRands]]\" \"[[yAmounts]]\" \"[[[yPairss]]]\""

let prepare_cr_verify args =
  match args with
  | [m_str; n2_str; q_str; beta_str; gamma_str; k_str; ck_str; c_amount_str; bits_str; comps_str; amount_as_str; amount_zs_str; pair_ass_str; pair_zss_str] ->
    (match make_cb_params m_str n2_str q_str beta_str, parse_int gamma_str, parse_int k_str, parse_mat ck_str, parse_vec c_amount_str, parse_mat bits_str, parse_mat comps_str, parse_mat amount_as_str, parse_mat amount_zs_str, parse_cube pair_ass_str, parse_cube pair_zss_str with
     | Some params, Some gamma, Some k, Some ck, Some c_amount, Some bits, Some comps, Some amount_as, Some amount_zs, Some pair_ass, Some pair_zss ->
       let proof = Confidential_range.make_range_proof bits comps amount_as amount_zs pair_ass pair_zss in
       Ok (fun () -> Confidential_range.range_fs_verify params gamma k ck c_amount proof)
     | _ -> Error "Expected params, gamma, commitment key, amount commitment, and proof fields")
  | _ -> Error "Usage: cr-verify M N2 Q BETA GAMMA K \"[[ck]]\" \"[cAmount]\" \"[[bits]]\" \"[[comps]]\" \"[[amountAs]]\" \"[[amountZs]]\" \"[[[pairAss]]]\" \"[[[pairZss]]]\""

let cmd_cr_verify args =
  match prepare_cr_verify args with
  | Ok verify -> output_result "range_fs_verify" (if verify () then "true" else "false")
  | Error msg -> output_error msg

let cmd_cr_verify_bench args =
  match args with
  | iterations_str :: warmup_str :: rest ->
    (match parse_int iterations_str, parse_int warmup_str with
     | Some iterations, Some warmup when iterations > 0 && warmup >= 0 ->
       (match prepare_cr_verify rest with
        | Ok verify -> output_bench_stats "range_fs_verify_bench" (benchmark_bool warmup iterations verify)
        | Error msg -> output_error msg)
     | _ -> output_error "Expected positive ITERATIONS and non-negative WARMUP")
  | _ -> output_error "Usage: cr-verify-bench ITERATIONS WARMUP M N2 Q BETA GAMMA K \"[[ck]]\" \"[cAmount]\" \"[[bits]]\" \"[[comps]]\" \"[[amountAs]]\" \"[[amountZs]]\" \"[[[pairAss]]]\" \"[[[pairZss]]]\""

(** {1 Confidential Merkle Commands} *)

let cmd_ct_merkle_leaf args =
  match args with
  | [commitment_str] ->
    (match parse_vec commitment_str with
     | Some commitment ->
       output_string_result "ct_merkle_leaf" (Confidential_merkle.leaf commitment)
     | None -> output_error "Expected commitment vector")
  | _ -> output_error "Usage: ct-merkle-leaf \"[commitment]\""

let cmd_ct_merkle_empty args =
  match args with
  | [width_str] ->
    (match parse_int width_str with
     | Some width when width >= 0 ->
       output_string_result "ct_merkle_empty" (Confidential_merkle.empty width)
     | _ -> output_error "Expected non-negative width")
  | _ -> output_error "Usage: ct-merkle-empty WIDTH"

let cmd_ct_merkle_node args =
  match args with
  | [left; right] ->
    (try output_string_result "ct_merkle_node" (Confidential_merkle.node left right)
     with Invalid_argument msg -> output_error msg)
  | _ -> output_error "Usage: ct-merkle-node LEFT_DIGEST RIGHT_DIGEST"

let cmd_ct_merkle_root args =
  match args with
  | [ledger_str] ->
    (match parse_mat ledger_str with
     | Some ledger ->
       (try output_string_result "ct_merkle_root" (Confidential_merkle.root ledger)
        with Invalid_argument msg -> output_error msg)
     | None -> output_error "Expected ledger matrix")
  | _ -> output_error "Usage: ct-merkle-root \"[[commitment],...]\""

let cmd_ct_merkle_member_prove args =
  match args with
  | [ledger_str; commitment_str] ->
    (match parse_mat ledger_str, parse_vec commitment_str with
     | Some ledger, Some commitment ->
       (try
          match Confidential_merkle.membership_prove ledger commitment with
          | Some proof ->
            (match !output_format with
             | Human -> Printf.printf "ct_merkle_membership_proof = %s\n" (json_of_merkle_membership_proof proof)
             | Json -> Printf.printf "%s\n" (json_of_merkle_membership_proof proof))
          | None ->
            (match !output_format with
             | Human -> print_endline "ct_merkle_membership_proof = null"
             | Json -> print_endline "null")
        with Invalid_argument msg -> output_error msg)
     | _ -> output_error "Expected ledger matrix and commitment vector")
  | _ -> output_error "Usage: ct-merkle-member-prove \"[[commitment],...]\" \"[commitment]\""

let cmd_ct_merkle_member_verify args =
  match args with
  | [ledger_str; commitment_str] ->
    (match parse_mat ledger_str, parse_vec commitment_str with
     | Some ledger, Some commitment ->
       let result =
         try
           match Confidential_merkle.membership_prove ledger commitment with
           | Some proof -> Confidential_merkle.membership_verify commitment proof
           | None -> false
         with Invalid_argument _ -> false
       in
       output_result "ct_merkle_membership_verify" (if result then "true" else "false")
     | _ -> output_error "Expected ledger matrix and commitment vector")
  | _ -> output_error "Usage: ct-merkle-member-verify \"[[commitment],...]\" \"[commitment]\""

let cmd_ct_transaction_context args =
  match args with
  | [protocol_version_str; network_id; asset_id_str; ledger_epoch_str; root;
     public_fee_str; c_in1_str; c_in2_str; c_out1_str; c_out2_str; nf1_str; nf2_str] ->
    (match
       parse_int protocol_version_str,
       parse_int asset_id_str,
       parse_int ledger_epoch_str,
       parse_int public_fee_str,
       parse_vec c_in1_str,
       parse_vec c_in2_str,
       parse_vec c_out1_str,
       parse_vec c_out2_str,
       parse_vec nf1_str,
       parse_vec nf2_str
     with
     | Some protocol_version, Some asset_id, Some ledger_epoch, Some public_fee,
       Some c_in1, Some c_in2, Some c_out1, Some c_out2, Some nf1, Some nf2 ->
       (try
          output_string_result "ct_transaction_context"
            (Confidential_transaction.transaction_context_digest
               protocol_version network_id asset_id ledger_epoch root public_fee
               c_in1 c_in2 c_out1 c_out2 nf1 nf2)
        with Invalid_argument msg -> output_error msg)
     | _ -> output_error "Expected transaction context fields")
  | _ ->
    output_error "Usage: ct-transaction-context VERSION NETWORK_ID ASSET_ID LEDGER_EPOCH ROOT PUBLIC_FEE C_IN1 C_IN2 C_OUT1 C_OUT2 NF1 NF2"

(** {1 Confidential Transaction Commands} *)

let cmd_ct_nullifier args =
  match args with
  | [m_str; n2_str; q_str; beta_str; nk_str; amount_str; rand_str] ->
    (match make_cb_params m_str n2_str q_str beta_str, parse_mat nk_str, parse_int amount_str, parse_vec rand_str with
     | Some params, Some nk, Some amount, Some rand ->
       let result = Confidential_transaction.nullifier params nk (make_scalar_opening amount rand) in
       (match !output_format with
        | Human -> Printf.printf "nullifier = %s\n" (string_of_vec result)
        | Json -> Printf.printf "{\"result\":%s}\n" (json_of_vec result))
     | _ -> output_error "Expected params, nullifier key, scalar amount, and randomness vector")
  | _ -> output_error "Usage: ct-nullifier M N2 Q BETA \"[[nk]]\" AMOUNT \"[rand]\""

let cmd_ct_nullifier_canonical_challenge args =
  match args with
  | [m_str; n2_str; q_str; beta_str; ck_str; nk_str; c_str; nf_str; a_commit_str; a_nullifier_str] ->
    (match
       make_cb_params m_str n2_str q_str beta_str,
       parse_mat ck_str,
       parse_mat nk_str,
       parse_vec c_str,
       parse_vec nf_str,
       parse_vec a_commit_str,
       parse_vec a_nullifier_str
     with
     | Some params, Some ck, Some nk, Some c, Some nf, Some a_commit, Some a_nullifier ->
       let result =
         Confidential_transaction.canonical_nullifier_challenge
           params ck nk c nf a_commit a_nullifier
       in
       output_result "canonical_nullifier_challenge" (string_of_int result)
     | _ ->
       output_error "Expected params, keys, commitment, nullifier, commitment announcement, and nullifier announcement")
  | _ ->
    output_error "Usage: ct-nullifier-canonical-challenge M N2 Q BETA \"[[ck]]\" \"[[nk]]\" \"[c]\" \"[nf]\" \"[aCommit]\" \"[aNullifier]\""

let cmd_ct_nullifier_prove args =
  match args with
  | [m_str; n2_str; q_str; beta_str; gamma_str; ck_str; nk_str; c_str; nf_str; amount_str; rand_str; y_msgs_str; y_rands_str] ->
    (match make_cb_params m_str n2_str q_str beta_str, parse_int gamma_str, parse_mat ck_str, parse_mat nk_str, parse_vec c_str, parse_vec nf_str, parse_int amount_str, parse_vec rand_str, parse_vec y_msgs_str, parse_mat y_rands_str with
     | Some params, Some gamma, Some ck, Some nk, Some c, Some nf, Some amount, Some rand, Some y_msgs, Some y_rands ->
       (match make_scalar_openings y_msgs y_rands with
        | Some ys ->
          (match Confidential_transaction.nullifier_fs_prove
                   params
                   gamma
                   ck
                   nk
                   c
                   nf
                   (make_scalar_opening amount rand)
                   ys with
           | Some proof ->
             (match !output_format with
              | Human -> Printf.printf "nullifier_fs_proof = %s\n" (json_of_ct_nullifier_proof proof)
              | Json -> Printf.printf "%s\n" (json_of_ct_nullifier_proof proof))
           | None ->
             (match !output_format with
              | Human -> print_endline "nullifier_fs_proof = null"
              | Json -> print_endline "null"))
        | None -> output_error "Mask message and randomness counts must match")
     | _ -> output_error "Expected params, gamma, keys, commitments, witness opening, and mask openings")
  | _ -> output_error "Usage: ct-nullifier-prove M N2 Q BETA G \"[[ck]]\" \"[[nk]]\" \"[c]\" \"[nf]\" AMOUNT \"[rand]\" \"[yMsgs]\" \"[[yRands]]\""

let cmd_ct_nullifier_verify args =
  match args with
  | [m_str; n2_str; q_str; beta_str; gamma_str; ck_str; nk_str; c_str; nf_str; a_commits_str; a_nullifiers_str; z_msgs_str; z_rands_str] ->
    (match make_cb_params m_str n2_str q_str beta_str, parse_int gamma_str, parse_mat ck_str, parse_mat nk_str, parse_vec c_str, parse_vec nf_str, parse_mat a_commits_str, parse_mat a_nullifiers_str, parse_mat z_msgs_str, parse_mat z_rands_str with
     | Some params, Some gamma, Some ck, Some nk, Some c, Some nf, Some a_commits, Some a_nullifiers, Some z_msgs, Some z_rands ->
       let proof =
         Confidential_transaction.make_nullifier_proof a_commits a_nullifiers z_msgs z_rands
       in
       let result = Confidential_transaction.nullifier_fs_verify params gamma ck nk c nf proof in
       output_result "nullifier_fs_verify" (if result then "true" else "false")
     | _ -> output_error "Expected params, gamma, keys, commitments, and repeated nullifier-proof fields")
  | _ -> output_error "Usage: ct-nullifier-verify M N2 Q BETA G \"[[ck]]\" \"[[nk]]\" \"[c]\" \"[nf]\" \"[[aCommits]]\" \"[[aNullifiers]]\" \"[[zMsgs]]\" \"[[zRands]]\""

let cmd_ct_member_prove args =
  match args with
  | [m_str; n2_str; q_str; beta_str; ledger_str; c_str] ->
    (match make_cb_params m_str n2_str q_str beta_str, parse_mat ledger_str, parse_vec c_str with
     | Some params, Some ledger, Some c ->
       (match Confidential_transaction.membership_prove params ledger c with
        | Some proof ->
          (match !output_format with
           | Human -> Printf.printf "membership_proof = %s\n" (json_of_ct_membership_proof proof)
           | Json -> Printf.printf "%s\n" (json_of_ct_membership_proof proof))
        | None ->
          (match !output_format with
           | Human -> print_endline "membership_proof = null"
           | Json -> print_endline "null"))
     | _ -> output_error "Expected params, a ledger matrix, and commitment vector")
  | _ -> output_error "Usage: ct-member-prove M N2 Q BETA \"[[c1],[c2],...]\" \"[c]\""

let cmd_ct_member_verify args =
  match args with
  | [m_str; n2_str; q_str; beta_str; ledger_str; c_str] ->
    (match make_cb_params m_str n2_str q_str beta_str, parse_mat ledger_str, parse_vec c_str with
     | Some params, Some ledger, Some c ->
       let result =
         match Confidential_transaction.membership_prove params ledger c with
         | Some proof -> Confidential_transaction.membership_verify params c proof
         | None -> false
       in
       output_result "membership_verify" (if result then "true" else "false")
     | _ -> output_error "Expected params, a ledger matrix, and commitment vector")
  | _ -> output_error "Usage: ct-member-verify M N2 Q BETA \"[[c1],[c2],...]\" \"[c]\""

let cmd_ct_prove args =
  match args with
  | [m_str; n2_str; q_str; beta_str; gamma_str; k_str; ck_str; nk_str; ledger_str; spent_str; c_in1_str; c_in2_str; c_out1_str; c_out2_str; nf1_str; nf2_str; in1_amount_str; in1_rand_str; in2_amount_str; in2_rand_str; out1_amount_str; out1_rand_str; out2_amount_str; out2_rand_str; out1_bits_str; out1_bit_rands_str; out1_comps_str; out1_comp_rands_str; out2_bits_str; out2_bit_rands_str; out2_comps_str; out2_comp_rands_str; y_in1_msgs_str; y_in1_rands_str; y_in2_msgs_str; y_in2_rands_str; y_balance_str; y_out1_amounts_str; y_out1_pairss_str; y_out2_amounts_str; y_out2_pairss_str] ->
    (match
       make_cb_params m_str n2_str q_str beta_str,
       parse_int gamma_str,
       parse_int k_str,
       parse_mat ck_str,
       parse_mat nk_str,
       parse_mat ledger_str,
       parse_mat spent_str,
       parse_vec c_in1_str,
       parse_vec c_in2_str,
       parse_vec c_out1_str,
       parse_vec c_out2_str,
       parse_vec nf1_str,
       parse_vec nf2_str,
       parse_int in1_amount_str,
       parse_vec in1_rand_str,
       parse_int in2_amount_str,
       parse_vec in2_rand_str,
       parse_int out1_amount_str,
       parse_vec out1_rand_str,
       parse_int out2_amount_str,
       parse_vec out2_rand_str,
       parse_vec out1_bits_str,
       parse_mat out1_bit_rands_str,
       parse_vec out1_comps_str,
       parse_mat out1_comp_rands_str,
       parse_vec out2_bits_str,
       parse_mat out2_bit_rands_str,
       parse_vec out2_comps_str,
       parse_mat out2_comp_rands_str,
       parse_vec y_in1_msgs_str,
       parse_mat y_in1_rands_str,
       parse_vec y_in2_msgs_str,
       parse_mat y_in2_rands_str,
       parse_mat y_balance_str,
       parse_mat y_out1_amounts_str,
       parse_cube y_out1_pairss_str,
       parse_mat y_out2_amounts_str,
       parse_cube y_out2_pairss_str with
     | Some params, Some gamma, Some k, Some ck, Some nk, Some ledger, Some spent, Some c_in1, Some c_in2, Some c_out1, Some c_out2, Some nf1, Some nf2, Some in1_amount, Some in1_rand, Some in2_amount, Some in2_rand, Some out1_amount, Some out1_rand, Some out2_amount, Some out2_rand, Some out1_bits, Some out1_bit_rands, Some out1_comps, Some out1_comp_rands, Some out2_bits, Some out2_bit_rands, Some out2_comps, Some out2_comp_rands, Some y_in1_msgs, Some y_in1_rands, Some y_in2_msgs, Some y_in2_rands, Some y_balance, Some y_out1_amounts, Some y_out1_pairss, Some y_out2_amounts, Some y_out2_pairss ->
       (match make_scalar_openings out1_bits out1_bit_rands, make_scalar_openings out1_comps out1_comp_rands, make_scalar_openings out2_bits out2_bit_rands, make_scalar_openings out2_comps out2_comp_rands, make_scalar_openings y_in1_msgs y_in1_rands, make_scalar_openings y_in2_msgs y_in2_rands with
        | Some out1_bit_ops, Some out1_comp_ops, Some out2_bit_ops, Some out2_comp_ops, Some y_in1_ops, Some y_in2_ops ->
          (match Confidential_transaction.transaction_fs_prove
                   params
                   gamma
                   k
                   ck
                   nk
                   ledger
                   spent
                   c_in1
                   c_in2
                   c_out1
                   c_out2
                   nf1
                   nf2
                   (make_scalar_opening in1_amount in1_rand)
                   (make_scalar_opening in2_amount in2_rand)
                   (make_scalar_opening out1_amount out1_rand)
                   (make_scalar_opening out2_amount out2_rand)
                   out1_bit_ops
                   out1_comp_ops
                   out2_bit_ops
                   out2_comp_ops
                   y_in1_ops
                   y_in2_ops
                   y_balance
                   y_out1_amounts
                   y_out1_pairss
                   y_out2_amounts
                   y_out2_pairss with
           | Some proof ->
             (match !output_format with
              | Human -> Printf.printf "transaction_fs_proof = %s\n" (json_of_ct_transaction_proof proof)
              | Json -> Printf.printf "%s\n" (json_of_ct_transaction_proof proof))
           | None ->
             (match !output_format with
              | Human -> print_endline "transaction_fs_proof = null"
              | Json -> print_endline "null"))
        | _ -> output_error "Bit, complement, and nullifier-mask counts must match their randomness matrices")
     | _ -> output_error "Expected params, keys, ledger, commitments, openings, bit decompositions, and mask vectors")
  | _ -> output_error "Usage: ct-prove M N2 Q BETA G K CK NK LEDGER SPENT C1 C2 C3 C4 NF1 NF2 IN1_AMOUNT IN1_RAND IN2_AMOUNT IN2_RAND OUT1_AMOUNT OUT1_RAND OUT2_AMOUNT OUT2_RAND OUT1_BITS OUT1_BIT_RANDS OUT1_COMPS OUT1_COMP_RANDS OUT2_BITS OUT2_BIT_RANDS OUT2_COMPS OUT2_COMP_RANDS Y1_MSGS Y1_RANDS Y2_MSGS Y2_RANDS YBALS YOUT1_AMOUNTS YOUT1_PAIRSS YOUT2_AMOUNTS YOUT2_PAIRSS"

let cmd_ct_prove_merkle args =
  match args with
  | [m_str; n2_str; q_str; beta_str; gamma_str; k_str; ck_str; nk_str; ledger_str; spent_str; c_in1_str; c_in2_str; c_out1_str; c_out2_str; nf1_str; nf2_str; in1_amount_str; in1_rand_str; in2_amount_str; in2_rand_str; out1_amount_str; out1_rand_str; out2_amount_str; out2_rand_str; out1_bits_str; out1_bit_rands_str; out1_comps_str; out1_comp_rands_str; out2_bits_str; out2_bit_rands_str; out2_comps_str; out2_comp_rands_str; y_in1_msgs_str; y_in1_rands_str; y_in2_msgs_str; y_in2_rands_str; y_balance_str; y_out1_amounts_str; y_out1_pairss_str; y_out2_amounts_str; y_out2_pairss_str] ->
    (match
       make_cb_params m_str n2_str q_str beta_str,
       parse_int gamma_str,
       parse_int k_str,
       parse_mat ck_str,
       parse_mat nk_str,
       parse_mat ledger_str,
       parse_mat spent_str,
       parse_vec c_in1_str,
       parse_vec c_in2_str,
       parse_vec c_out1_str,
       parse_vec c_out2_str,
       parse_vec nf1_str,
       parse_vec nf2_str,
       parse_int in1_amount_str,
       parse_vec in1_rand_str,
       parse_int in2_amount_str,
       parse_vec in2_rand_str,
       parse_int out1_amount_str,
       parse_vec out1_rand_str,
       parse_int out2_amount_str,
       parse_vec out2_rand_str,
       parse_vec out1_bits_str,
       parse_mat out1_bit_rands_str,
       parse_vec out1_comps_str,
       parse_mat out1_comp_rands_str,
       parse_vec out2_bits_str,
       parse_mat out2_bit_rands_str,
       parse_vec out2_comps_str,
       parse_mat out2_comp_rands_str,
       parse_vec y_in1_msgs_str,
       parse_mat y_in1_rands_str,
       parse_vec y_in2_msgs_str,
       parse_mat y_in2_rands_str,
       parse_mat y_balance_str,
       parse_mat y_out1_amounts_str,
       parse_cube y_out1_pairss_str,
       parse_mat y_out2_amounts_str,
       parse_cube y_out2_pairss_str with
     | Some params, Some gamma, Some k, Some ck, Some nk, Some ledger, Some spent, Some c_in1, Some c_in2, Some c_out1, Some c_out2, Some nf1, Some nf2, Some in1_amount, Some in1_rand, Some in2_amount, Some in2_rand, Some out1_amount, Some out1_rand, Some out2_amount, Some out2_rand, Some out1_bits, Some out1_bit_rands, Some out1_comps, Some out1_comp_rands, Some out2_bits, Some out2_bit_rands, Some out2_comps, Some out2_comp_rands, Some y_in1_msgs, Some y_in1_rands, Some y_in2_msgs, Some y_in2_rands, Some y_balance, Some y_out1_amounts, Some y_out1_pairss, Some y_out2_amounts, Some y_out2_pairss ->
       (match make_scalar_openings out1_bits out1_bit_rands, make_scalar_openings out1_comps out1_comp_rands, make_scalar_openings out2_bits out2_bit_rands, make_scalar_openings out2_comps out2_comp_rands, make_scalar_openings y_in1_msgs y_in1_rands, make_scalar_openings y_in2_msgs y_in2_rands with
        | Some out1_bit_ops, Some out1_comp_ops, Some out2_bit_ops, Some out2_comp_ops, Some y_in1_ops, Some y_in2_ops ->
          (match Confidential_transaction.transaction_fs_prove_merkle
                   params
                   gamma
                   k
                   ck
                   nk
                   ledger
                   spent
                   c_in1
                   c_in2
                   c_out1
                   c_out2
                   nf1
                   nf2
                   (make_scalar_opening in1_amount in1_rand)
                   (make_scalar_opening in2_amount in2_rand)
                   (make_scalar_opening out1_amount out1_rand)
                   (make_scalar_opening out2_amount out2_rand)
                   out1_bit_ops
                   out1_comp_ops
                   out2_bit_ops
                   out2_comp_ops
                   y_in1_ops
                   y_in2_ops
                   y_balance
                   y_out1_amounts
                   y_out1_pairss
                   y_out2_amounts
                   y_out2_pairss with
           | Some proof ->
             (match !output_format with
              | Human -> Printf.printf "transaction_fs_merkle_proof = %s\n" (json_of_ct_merkle_transaction_proof proof)
              | Json -> Printf.printf "%s\n" (json_of_ct_merkle_transaction_proof proof))
           | None ->
             (match !output_format with
              | Human -> print_endline "transaction_fs_merkle_proof = null"
              | Json -> print_endline "null"))
        | _ -> output_error "Bit, complement, and nullifier-mask counts must match their randomness matrices")
     | _ -> output_error "Expected params, keys, ledger, commitments, openings, bit decompositions, and mask vectors")
  | _ -> output_error "Usage: ct-prove-merkle M N2 Q BETA G K CK NK LEDGER SPENT C1 C2 C3 C4 NF1 NF2 IN1_AMOUNT IN1_RAND IN2_AMOUNT IN2_RAND OUT1_AMOUNT OUT1_RAND OUT2_AMOUNT OUT2_RAND OUT1_BITS OUT1_BIT_RANDS OUT1_COMPS OUT1_COMP_RANDS OUT2_BITS OUT2_BIT_RANDS OUT2_COMPS OUT2_COMP_RANDS Y1_MSGS Y1_RANDS Y2_MSGS Y2_RANDS YBALS YOUT1_AMOUNTS YOUT1_PAIRSS YOUT2_AMOUNTS YOUT2_PAIRSS"

let prepare_ct_verify args =
  match args with
  | [m_str; n2_str; q_str; beta_str; gamma_str; k_str; ck_str; nk_str; ledger_str; spent_str; c_in1_str; c_in2_str; c_out1_str; c_out2_str; nf1_str; nf2_str; in1_a_commits_str; in1_a_nullifiers_str; in1_z_msgs_str; in1_z_rands_str; in2_a_commits_str; in2_a_nullifiers_str; in2_z_msgs_str; in2_z_rands_str; balance_as_str; balance_zs_str; out1_bits_str; out1_comps_str; out1_amount_a_str; out1_amount_z_str; out1_pair_as_str; out1_pair_zs_str; out2_bits_str; out2_comps_str; out2_amount_a_str; out2_amount_z_str; out2_pair_as_str; out2_pair_zs_str] ->
    (match
       make_cb_params m_str n2_str q_str beta_str,
       parse_int gamma_str,
       parse_int k_str,
       parse_mat ck_str,
       parse_mat nk_str,
       parse_mat ledger_str,
       parse_mat spent_str,
       parse_vec c_in1_str,
       parse_vec c_in2_str,
       parse_vec c_out1_str,
       parse_vec c_out2_str,
       parse_vec nf1_str,
       parse_vec nf2_str,
       parse_mat in1_a_commits_str,
       parse_mat in1_a_nullifiers_str,
       parse_mat in1_z_msgs_str,
       parse_mat in1_z_rands_str,
       parse_mat in2_a_commits_str,
       parse_mat in2_a_nullifiers_str,
       parse_mat in2_z_msgs_str,
       parse_mat in2_z_rands_str,
       parse_mat balance_as_str,
       parse_mat balance_zs_str,
       parse_mat out1_bits_str,
       parse_mat out1_comps_str,
       parse_mat out1_amount_a_str,
       parse_mat out1_amount_z_str,
       parse_cube out1_pair_as_str,
       parse_cube out1_pair_zs_str,
       parse_mat out2_bits_str,
       parse_mat out2_comps_str,
       parse_mat out2_amount_a_str,
       parse_mat out2_amount_z_str,
       parse_cube out2_pair_as_str,
       parse_cube out2_pair_zs_str with
     | Some params, Some gamma, Some k, Some ck, Some nk, Some ledger, Some spent, Some c_in1, Some c_in2, Some c_out1, Some c_out2, Some nf1, Some nf2, Some in1_a_commits, Some in1_a_nullifiers, Some in1_z_msgs, Some in1_z_rands, Some in2_a_commits, Some in2_a_nullifiers, Some in2_z_msgs, Some in2_z_rands, Some balance_as, Some balance_zs, Some out1_bits, Some out1_comps, Some out1_amount_a, Some out1_amount_z, Some out1_pair_as, Some out1_pair_zs, Some out2_bits, Some out2_comps, Some out2_amount_a, Some out2_amount_z, Some out2_pair_as, Some out2_pair_zs ->
       let root = Confidential_transaction.ledger_root params ledger in
       (match
          Confidential_transaction.membership_prove params ledger c_in1,
          Confidential_transaction.membership_prove params ledger c_in2 with
        | Some in1_member, Some in2_member ->
          let proof =
            Confidential_transaction.make_transaction_proof
              in1_member
              in2_member
              (Confidential_transaction.make_nullifier_proof in1_a_commits in1_a_nullifiers in1_z_msgs in1_z_rands)
              (Confidential_transaction.make_nullifier_proof in2_a_commits in2_a_nullifiers in2_z_msgs in2_z_rands)
              (Confidential_balance.make_balance_proof balance_as balance_zs)
              (Confidential_range.make_range_proof out1_bits out1_comps out1_amount_a out1_amount_z out1_pair_as out1_pair_zs)
              (Confidential_range.make_range_proof out2_bits out2_comps out2_amount_a out2_amount_z out2_pair_as out2_pair_zs)
          in
          Ok
            (fun () ->
              Confidential_transaction.transaction_fs_verify
                params
                gamma
                k
                ck
                nk
                root
                spent
                c_in1
                c_in2
                c_out1
                c_out2
                nf1
                nf2
                proof)
        | _ -> Error "Expected membership proofs for both input commitments in the supplied ledger")
     | _ -> Error "Expected params, keys, ledger, commitments, nullifiers, and transaction-proof fields")
  | _ -> Error "Usage: ct-verify M N2 Q BETA G K CK NK LEDGER SPENT C1 C2 C3 C4 NF1 NF2 IN1_A_COMMITS IN1_A_NULLIFIERS IN1_Z_MSGS IN1_Z_RANDS IN2_A_COMMITS IN2_A_NULLIFIERS IN2_Z_MSGS IN2_Z_RANDS BAL_AS BAL_ZS OUT1_BITS OUT1_COMPS OUT1_AMOUNT_AS OUT1_AMOUNT_ZS OUT1_PAIR_ASS OUT1_PAIR_ZSS OUT2_BITS OUT2_COMPS OUT2_AMOUNT_AS OUT2_AMOUNT_ZS OUT2_PAIR_ASS OUT2_PAIR_ZSS"

let prepare_ct_verify_merkle args =
  match args with
  | [m_str; n2_str; q_str; beta_str; gamma_str; k_str; ck_str; nk_str; ledger_str; spent_str; c_in1_str; c_in2_str; c_out1_str; c_out2_str; nf1_str; nf2_str; in1_a_commits_str; in1_a_nullifiers_str; in1_z_msgs_str; in1_z_rands_str; in2_a_commits_str; in2_a_nullifiers_str; in2_z_msgs_str; in2_z_rands_str; balance_as_str; balance_zs_str; out1_bits_str; out1_comps_str; out1_amount_a_str; out1_amount_z_str; out1_pair_as_str; out1_pair_zs_str; out2_bits_str; out2_comps_str; out2_amount_a_str; out2_amount_z_str; out2_pair_as_str; out2_pair_zs_str] ->
    (match
       make_cb_params m_str n2_str q_str beta_str,
       parse_int gamma_str,
       parse_int k_str,
       parse_mat ck_str,
       parse_mat nk_str,
       parse_mat ledger_str,
       parse_mat spent_str,
       parse_vec c_in1_str,
       parse_vec c_in2_str,
       parse_vec c_out1_str,
       parse_vec c_out2_str,
       parse_vec nf1_str,
       parse_vec nf2_str,
       parse_mat in1_a_commits_str,
       parse_mat in1_a_nullifiers_str,
       parse_mat in1_z_msgs_str,
       parse_mat in1_z_rands_str,
       parse_mat in2_a_commits_str,
       parse_mat in2_a_nullifiers_str,
       parse_mat in2_z_msgs_str,
       parse_mat in2_z_rands_str,
       parse_mat balance_as_str,
       parse_mat balance_zs_str,
       parse_mat out1_bits_str,
       parse_mat out1_comps_str,
       parse_mat out1_amount_a_str,
       parse_mat out1_amount_z_str,
       parse_cube out1_pair_as_str,
       parse_cube out1_pair_zs_str,
       parse_mat out2_bits_str,
       parse_mat out2_comps_str,
       parse_mat out2_amount_a_str,
       parse_mat out2_amount_z_str,
       parse_cube out2_pair_as_str,
       parse_cube out2_pair_zs_str with
     | Some params, Some gamma, Some k, Some ck, Some nk, Some ledger, Some spent, Some c_in1, Some c_in2, Some c_out1, Some c_out2, Some nf1, Some nf2, Some in1_a_commits, Some in1_a_nullifiers, Some in1_z_msgs, Some in1_z_rands, Some in2_a_commits, Some in2_a_nullifiers, Some in2_z_msgs, Some in2_z_rands, Some balance_as, Some balance_zs, Some out1_bits, Some out1_comps, Some out1_amount_a, Some out1_amount_z, Some out1_pair_as, Some out1_pair_zs, Some out2_bits, Some out2_comps, Some out2_amount_a, Some out2_amount_z, Some out2_pair_as, Some out2_pair_zs ->
       let root = Confidential_transaction.merkle_ledger_root ledger in
       (match
          Confidential_transaction.merkle_membership_prove ledger c_in1,
          Confidential_transaction.merkle_membership_prove ledger c_in2 with
        | Some in1_member, Some in2_member ->
          let proof =
            Confidential_transaction.make_merkle_transaction_proof
              in1_member
              in2_member
              (Confidential_transaction.make_nullifier_proof in1_a_commits in1_a_nullifiers in1_z_msgs in1_z_rands)
              (Confidential_transaction.make_nullifier_proof in2_a_commits in2_a_nullifiers in2_z_msgs in2_z_rands)
              (Confidential_balance.make_balance_proof balance_as balance_zs)
              (Confidential_range.make_range_proof out1_bits out1_comps out1_amount_a out1_amount_z out1_pair_as out1_pair_zs)
              (Confidential_range.make_range_proof out2_bits out2_comps out2_amount_a out2_amount_z out2_pair_as out2_pair_zs)
          in
          Ok
            (fun () ->
              Confidential_transaction.transaction_fs_verify_merkle
                params
                gamma
                k
                ck
                nk
                root
                spent
                c_in1
                c_in2
                c_out1
                c_out2
                nf1
                nf2
                proof)
        | _ -> Error "Expected Merkle membership proofs for both input commitments in the supplied ledger")
     | _ -> Error "Expected params, keys, ledger, commitments, nullifiers, and transaction-proof fields")
  | _ -> Error "Usage: ct-verify-merkle M N2 Q BETA G K CK NK LEDGER SPENT C1 C2 C3 C4 NF1 NF2 IN1_A_COMMITS IN1_A_NULLIFIERS IN1_Z_MSGS IN1_Z_RANDS IN2_A_COMMITS IN2_A_NULLIFIERS IN2_Z_MSGS IN2_Z_RANDS BAL_AS BAL_ZS OUT1_BITS OUT1_COMPS OUT1_AMOUNT_AS OUT1_AMOUNT_ZS OUT1_PAIR_ASS OUT1_PAIR_ZSS OUT2_BITS OUT2_COMPS OUT2_AMOUNT_AS OUT2_AMOUNT_ZS OUT2_PAIR_ASS OUT2_PAIR_ZSS"

let cmd_ct_verify args =
  match prepare_ct_verify args with
  | Ok verify -> output_result "transaction_fs_verify" (if verify () then "true" else "false")
  | Error msg -> output_error msg

let cmd_ct_verify_merkle args =
  match prepare_ct_verify_merkle args with
  | Ok verify -> output_result "transaction_fs_verify_merkle" (if verify () then "true" else "false")
  | Error msg -> output_error msg

let cmd_ct_verify_bench args =
  match args with
  | iterations_str :: warmup_str :: rest ->
    (match parse_int iterations_str, parse_int warmup_str with
     | Some iterations, Some warmup when iterations > 0 && warmup >= 0 ->
       (match prepare_ct_verify rest with
        | Ok verify -> output_bench_stats "transaction_fs_verify_bench" (benchmark_bool warmup iterations verify)
        | Error msg -> output_error msg)
     | _ -> output_error "Expected positive ITERATIONS and non-negative WARMUP")
  | _ -> output_error "Usage: ct-verify-bench ITERATIONS WARMUP M N2 Q BETA G K CK NK LEDGER SPENT C1 C2 C3 C4 NF1 NF2 IN1_A_COMMITS IN1_A_NULLIFIERS IN1_Z_MSGS IN1_Z_RANDS IN2_A_COMMITS IN2_A_NULLIFIERS IN2_Z_MSGS IN2_Z_RANDS BAL_AS BAL_ZS OUT1_BITS OUT1_COMPS OUT1_AMOUNT_AS OUT1_AMOUNT_ZS OUT1_PAIR_ASS OUT1_PAIR_ZSS OUT2_BITS OUT2_COMPS OUT2_AMOUNT_AS OUT2_AMOUNT_ZS OUT2_PAIR_ASS OUT2_PAIR_ZSS"

let cmd_ct_ledger_step_verify args =
  match args with
  | [m_str; n2_str; q_str; beta_str; gamma_str; k_str; ck_str; nk_str; note_commitments_str; note_bits_str; note_comps_str; note_amount_as_str; note_amount_zs_str; note_pair_as_str; note_pair_zs_str; spent_str; c_in1_str; c_in2_str; c_out1_str; c_out2_str; nf1_str; nf2_str; in1_a_commits_str; in1_a_nullifiers_str; in1_z_msgs_str; in1_z_rands_str; in2_a_commits_str; in2_a_nullifiers_str; in2_z_msgs_str; in2_z_rands_str; balance_as_str; balance_zs_str; out1_bits_str; out1_comps_str; out1_amount_a_str; out1_amount_z_str; out1_pair_as_str; out1_pair_zs_str; out2_bits_str; out2_comps_str; out2_amount_a_str; out2_amount_z_str; out2_pair_as_str; out2_pair_zs_str] ->
    (match
       make_cb_params m_str n2_str q_str beta_str,
       parse_int gamma_str,
       parse_int k_str,
       parse_mat ck_str,
       parse_mat nk_str,
       parse_mat note_commitments_str,
       parse_cube note_bits_str,
       parse_cube note_comps_str,
       parse_cube note_amount_as_str,
       parse_cube note_amount_zs_str,
       parse_4d note_pair_as_str,
       parse_4d note_pair_zs_str,
       parse_mat spent_str,
       parse_vec c_in1_str,
       parse_vec c_in2_str,
       parse_vec c_out1_str,
       parse_vec c_out2_str,
       parse_vec nf1_str,
       parse_vec nf2_str,
       parse_mat in1_a_commits_str,
       parse_mat in1_a_nullifiers_str,
       parse_mat in1_z_msgs_str,
       parse_mat in1_z_rands_str,
       parse_mat in2_a_commits_str,
       parse_mat in2_a_nullifiers_str,
       parse_mat in2_z_msgs_str,
       parse_mat in2_z_rands_str,
       parse_mat balance_as_str,
       parse_mat balance_zs_str,
       parse_mat out1_bits_str,
       parse_mat out1_comps_str,
       parse_mat out1_amount_a_str,
       parse_mat out1_amount_z_str,
       parse_cube out1_pair_as_str,
       parse_cube out1_pair_zs_str,
       parse_mat out2_bits_str,
       parse_mat out2_comps_str,
       parse_mat out2_amount_a_str,
       parse_mat out2_amount_z_str,
       parse_cube out2_pair_as_str,
       parse_cube out2_pair_zs_str with
     | Some params, Some gamma, Some k, Some ck, Some nk, Some note_commitments, Some note_bits, Some note_comps, Some note_amount_as, Some note_amount_zs, Some note_pair_as, Some note_pair_zs, Some spent, Some c_in1, Some c_in2, Some c_out1, Some c_out2, Some nf1, Some nf2, Some in1_a_commits, Some in1_a_nullifiers, Some in1_z_msgs, Some in1_z_rands, Some in2_a_commits, Some in2_a_nullifiers, Some in2_z_msgs, Some in2_z_rands, Some balance_as, Some balance_zs, Some out1_bits, Some out1_comps, Some out1_amount_a, Some out1_amount_z, Some out1_pair_as, Some out1_pair_zs, Some out2_bits, Some out2_comps, Some out2_amount_a, Some out2_amount_z, Some out2_pair_as, Some out2_pair_zs ->
       (match
          make_verified_notes note_commitments note_bits note_comps note_amount_as note_amount_zs note_pair_as note_pair_zs,
          Confidential_transaction.membership_prove params note_commitments c_in1,
          Confidential_transaction.membership_prove params note_commitments c_in2 with
        | Some notes, Some in1_member, Some in2_member ->
          let proof =
            Confidential_transaction.make_transaction_proof
              in1_member
              in2_member
              (Confidential_transaction.make_nullifier_proof in1_a_commits in1_a_nullifiers in1_z_msgs in1_z_rands)
              (Confidential_transaction.make_nullifier_proof in2_a_commits in2_a_nullifiers in2_z_msgs in2_z_rands)
              (Confidential_balance.make_balance_proof balance_as balance_zs)
              (Confidential_range.make_range_proof out1_bits out1_comps out1_amount_a out1_amount_z out1_pair_as out1_pair_zs)
              (Confidential_range.make_range_proof out2_bits out2_comps out2_amount_a out2_amount_z out2_pair_as out2_pair_zs)
          in
          let result =
            Confidential_transaction.ledger_step_valid
              params
              gamma
              k
              ck
              nk
              notes
              spent
              c_in1
              c_in2
              c_out1
              c_out2
              nf1
              nf2
              proof
          in
          output_result "ledger_step_valid" (if result then "true" else "false")
        | _ -> output_error "Expected consistent verified-note inputs and membership proofs for both input commitments")
     | _ -> output_error "Expected params, keys, verified-note ledger fields, nullifiers, and transaction-proof fields")
  | _ -> output_error "Usage: ct-ledger-step-verify M N2 Q BETA G K CK NK NOTE_COMMITMENTS NOTE_BITS NOTE_COMPS NOTE_AMOUNT_AS NOTE_AMOUNT_ZS NOTE_PAIR_AS NOTE_PAIR_ZS SPENT C1 C2 C3 C4 NF1 NF2 IN1_A_COMMITS IN1_A_NULLIFIERS IN1_Z_MSGS IN1_Z_RANDS IN2_A_COMMITS IN2_A_NULLIFIERS IN2_Z_MSGS IN2_Z_RANDS BAL_AS BAL_ZS OUT1_BITS OUT1_COMPS OUT1_AMOUNT_AS OUT1_AMOUNT_ZS OUT1_PAIR_ASS OUT1_PAIR_ZSS OUT2_BITS OUT2_COMPS OUT2_AMOUNT_AS OUT2_AMOUNT_ZS OUT2_PAIR_ASS OUT2_PAIR_ZSS"

(** {1 Examples} *)

let time_it f =
  let start = Unix.gettimeofday () in
  let result = f () in
  let stop = Unix.gettimeofday () in
  (result, stop -. start)

let run_examples () =
  print_endline "=====================================================";
  print_endline "  Isabella - Formally Verified Lattice Cryptography";
  print_endline "=====================================================";
  print_endline "";

  print_endline "--- Centered Modular Reduction ---";
  print_endline "";
  Printf.printf "  mod_centered 7 5 = %d\n" (Zq.mod_centered 7 5);
  Printf.printf "  mod_centered 8 5 = %d\n" (Zq.mod_centered 8 5);
  Printf.printf "  mod_centered (-3) 5 = %d\n" (Zq.mod_centered (-3) 5);
  print_endline "";

  print_endline "--- Distance from Zero ---";
  print_endline "";
  Printf.printf "  dist0 256 5 = %d\n" (Zq.dist0 256 5);
  Printf.printf "  dist0 256 130 = %d\n" (Zq.dist0 256 130);
  Printf.printf "  dist0 256 250 = %d\n" (Zq.dist0 256 250);
  print_endline "";

  print_endline "--- Bit Encoding/Decoding ---";
  print_endline "";
  let q = 256 in
  Printf.printf "  Using modulus q = %d\n\n" q;
  Printf.printf "  encode_bit 256 false = %d\n" (Zq.encode_bit q false);
  Printf.printf "  encode_bit 256 true = %d\n" (Zq.encode_bit q true);
  Printf.printf "  decode_bit 256 5 = %b\n" (Zq.decode_bit q 5);
  Printf.printf "  decode_bit 256 130 = %b\n" (Zq.decode_bit q 130);
  print_endline "";

  print_endline "--- Encoding Round-Trip (with noise) ---";
  print_endline "";
  let noise = 10 in
  Printf.printf "  Testing decode(encode(b) + noise) with noise = %d\n\n" noise;
  let encoded0 = Zq.encode_bit q false in
  let encoded1 = Zq.encode_bit q true in
  Printf.printf "  decode_bit (encode_bit false + 10) = %b\n" (Zq.decode_bit q (encoded0 + noise));
  Printf.printf "  decode_bit (encode_bit true + 10) = %b\n" (Zq.decode_bit q (encoded1 + noise));
  print_endline "";

  print_endline "--- Vector Operations ---";
  print_endline "";
  let v1 = [1; 2; 3; 4; 5] in
  let v2 = [10; 20; 30; 40; 50] in
  Printf.printf "  inner_prod [1;2;3;4;5] [10;20;30;40;50] = %d\n" (Listvec.inner_prod v1 v2);
  Printf.printf "  vec_add [1;2;3;4;5] [10;20;30;40;50]\n    = %s\n" (string_of_vec (Listvec.vec_add v1 v2));
  Printf.printf "  scalar_mult 3 [1;2;3;4;5]\n    = %s\n" (string_of_vec (Listvec.scalar_mult 3 v1));
  print_endline "";

  print_endline "--- Vector Modular Operations ---";
  print_endline "";
  let v3 = [7; 13; -2; 100; 255] in
  Printf.printf "  vec_mod [7;13;-2;100;255] 10\n    = %s\n" (string_of_vec (Zq.vec_mod v3 10));
  Printf.printf "  vec_mod_centered [7;13;-2;100;255] 10\n    = %s\n" (string_of_vec (Zq.vec_mod_centered v3 10));
  print_endline "";

  print_endline "--- Matrix-Vector Multiplication ---";
  print_endline "";
  let matrix = [[1; 2; 3]; [4; 5; 6]; [7; 8; 9]] in
  let vec = [1; 0; 1] in
  Printf.printf "  mat_vec_mult [[1;2;3];[4;5;6];[7;8;9]] [1;0;1]\n    = %s\n"
    (string_of_vec (Listvec.mat_vec_mult matrix vec));
  Printf.printf "  mat_vec_mult_mod same 10\n    = %s\n"
    (string_of_vec (Zq.mat_vec_mult_mod matrix vec 10));
  print_endline "";

  print_endline "--- Performance: Inner Product ---";
  print_endline "";
  let size = 10000 in
  let big_v1 = List.init size (fun _ -> 1) in
  let big_v2 = List.init size (fun _ -> 2) in
  Printf.printf "  Computing inner product of two %d-element vectors...\n" size;
  let (result, time) = time_it (fun () -> Listvec.inner_prod big_v1 big_v2) in
  Printf.printf "  Result: %d\n" result;
  Printf.printf "  Time: %.6fs\n" time;
  print_endline "";

  print_endline "--- Performance: Matrix-Vector Multiply ---";
  print_endline "";
  let rows = 100 in
  let cols = 100 in
  let big_mat = List.init rows (fun _ -> List.init cols (fun _ -> 1)) in
  let big_vec = List.init cols (fun _ -> 1) in
  Printf.printf "  Computing %dx%d matrix * vector...\n" rows cols;
  let (result2, time2) = time_it (fun () -> Listvec.mat_vec_mult big_mat big_vec) in
  Printf.printf "  Result sum: %d\n" (List.fold_left (+) 0 result2);
  Printf.printf "  Time: %.6fs\n" time2;
  print_endline "";

  print_endline "=====================================================";
  print_endline "  All examples completed successfully!";
  print_endline "  All operations are formally verified in Isabelle/HOL";
  print_endline "====================================================="

(** {1 Help} *)

let show_help () =
  print_endline "Isabella - Formally Verified Lattice Cryptography";
  print_endline "";
  print_endline "Usage: isabella_cli [--json] <command> [options]";
  print_endline "";
  print_endline "Global Options:";
  print_endline "  --json             Output results in JSON format";
  print_endline "  --help, -h         Show this help message";
  print_endline "";
  print_endline "Basic Commands:";
  print_endline "  examples           Run example computations";
  print_endline "  mod-centered X Q   Compute centered modular reduction";
  print_endline "  dist0 Q X          Compute distance from zero in Z_q";
  print_endline "  encode-bit Q B     Encode a bit (0 or 1) for LWE";
  print_endline "  decode-bit Q X     Decode an LWE value to a bit";
  print_endline "  inner-prod V1 V2   Compute inner product of two vectors";
  print_endline "  vec-add V1 V2      Add two vectors";
  print_endline "  transpose M        Transpose a matrix";
  print_endline "  mat-vec-mult M V Q Matrix-vector multiplication mod q";
  print_endline "";
  print_endline "NTT Commands:";
  print_endline "  ntt-fast V W Q N   Fast NTT (Cooley-Tukey)";
  print_endline "  intt-fast V W Q N  Fast inverse NTT";
  print_endline "  ntt-pointwise A B Q  Pointwise multiplication in NTT domain";
  print_endline "  power-mod A K M    Modular exponentiation a^k mod m";
  print_endline "  mod-inverse A M    Modular multiplicative inverse";
  print_endline "  is-primitive-root W N Q  Check if omega is primitive root";
  print_endline "";
  print_endline "Polynomial Commands:";
  print_endline "  poly-mult P1 P2 Q  Polynomial multiplication mod q";
  print_endline "  ring-mult P1 P2 N Q  Ring multiplication mod (X^n+1, q)";
  print_endline "";
  print_endline "Kyber Commands:";
  print_endline "  kyber-ntt V        Kyber NTT (n=256, q=3329)";
  print_endline "  kyber-intt V       Kyber inverse NTT";
  print_endline "  kyber-poly-mult A B  Kyber polynomial multiplication via NTT";
  print_endline "  kyber-encode-msg M Encode message bits";
  print_endline "  kyber-decode-msg P Decode polynomial to message bits";
  print_endline "";
  print_endline "Dilithium Commands (ML-DSA):";
  print_endline "  dil-params VARIANT    Get ML-DSA parameters (44, 65, 87)";
  print_endline "  dil-mod-centered R M  Centered modular reduction r mod+/- m";
  print_endline "  dil-power2round R D   Power2Round: split r into (r1, r0)";
  print_endline "  dil-decompose R A     Decompose: split r into high/low bits";
  print_endline "  dil-highbits R A      Extract high-order bits";
  print_endline "  dil-lowbits R A       Extract low-order bits";
  print_endline "  dil-makehint Z R A    Compute hint bit";
  print_endline "  dil-usehint H R A     Recover high bits using hint";
  print_endline "  dil-check-bound V B   Check if |value| < bound";
  print_endline "  dil-hint-weight H     Compute total hint weight";
  print_endline "";
  print_endline "Confidential Balance Commands:";
  print_endline "  cb-params M N2 Q BETA      Build scalar commitment params for the balance proof slice";
  print_endline "  cb-valid-params M N2 Q BETA  Check scalar commitment params";
  print_endline "  cb-rand-commit-key M N2 Q BETA CK  Drop the message column from a commitment key";
  print_endline "  cb-rand-commit M N2 Q BETA CK R     Commit to aggregate randomness";
  print_endline "  cb-valid-witness M N2 Q BETA R      Check witness bounds";
  print_endline "  cb-valid-mask M N2 Q BETA G Y       Check mask bounds";
  print_endline "  cb-valid-response M N2 Q BETA G Z   Check response bounds";
  print_endline "  cb-balance-commitment C1 C2 C3 C4 Q Aggregate commitments for zero-balance checking";
  print_endline "  cb-canonical-challenge M N2 Q BETA CK C A  Deterministic Fiat-Shamir challenge";
  print_endline "  cb-sigma-commit M N2 Q BETA CK Y    Compute sigma announcement";
  print_endline "  cb-sigma-respond R Y E              Compute sigma response";
  print_endline "  cb-sigma-verify M N2 Q BETA G CK C A E Z  Verify sigma step";
  print_endline "  cb-prove M N2 Q BETA G CK C R Y     Build deterministic balance proof";
  print_endline "  cb-verify M N2 Q BETA G CK C A Z    Verify deterministic balance proof";
  print_endline "";
  print_endline "Confidential Range Commands:";
  print_endline "  cr-amount-commitment M N2 Q BETA CK C BITS  Build the amount residual commitment";
  print_endline "  cr-prove M N2 Q BETA G K CK C AMOUNT RAND BITS BIT_RANDS COMPS COMP_RANDS YAMOUNTS YPAIRSS  Build deterministic range proof";
  print_endline "  cr-verify M N2 Q BETA G K CK C BITS COMPS AMOUNT_AS AMOUNT_ZS PAIR_ASS PAIR_ZSS  Verify deterministic range proof";
  print_endline "  cr-verify-bench I W ...  Benchmark deterministic range verification natively";
  print_endline "";
  print_endline "Confidential Merkle Commands:";
  print_endline "  ct-merkle-leaf C             Hash a confidential note commitment leaf";
  print_endline "  ct-merkle-empty WIDTH        Hash an empty Merkle placeholder";
  print_endline "  ct-merkle-node LEFT RIGHT    Hash an internal Merkle node";
  print_endline "  ct-merkle-root LEDGER        Compute cryptographic Merkle root";
  print_endline "  ct-merkle-member-prove LEDGER C   Build cryptographic Merkle membership proof";
  print_endline "  ct-merkle-member-verify LEDGER C  Verify cryptographic Merkle membership proof";
  print_endline "  ct-transaction-context VERSION NETWORK ASSET EPOCH ROOT FEE C1 C2 C3 C4 NF1 NF2";
  print_endline "";
  print_endline "Confidential Transaction Commands:";
  print_endline "  ct-nullifier M N2 Q BETA NK AMOUNT RAND  Compute a deterministic note nullifier";
  print_endline "  ct-nullifier-canonical-challenge M N2 Q BETA CK NK C NF ACOMMIT ANULLIFIER  Deterministic nullifier Fiat-Shamir challenge";
  print_endline "  ct-nullifier-prove M N2 Q BETA G CK NK C NF AMOUNT RAND YMSGS YRANDS  Build repeated-round deterministic nullifier proof";
  print_endline "  ct-nullifier-verify M N2 Q BETA G CK NK C NF ACOMMITS ANULLIFIERS ZMSGS ZRANDS  Verify repeated-round deterministic nullifier proof";
  print_endline "  ct-member-prove M N2 Q BETA LEDGER C   Build explicit ledger membership proof";
  print_endline "  ct-member-verify M N2 Q BETA LEDGER C  Verify explicit ledger membership proof";
  print_endline "  ct-ledger-step-verify ... Verify semantic ledger-step validity from verified input notes";
  print_endline "  ct-prove ...  Build deterministic confidential-transaction proof";
  print_endline "  ct-prove-merkle ...  Build deterministic confidential-transaction proof with Merkle membership";
  print_endline "  ct-verify ... Verify deterministic confidential-transaction proof";
  print_endline "  ct-verify-merkle ... Verify deterministic confidential-transaction proof with Merkle membership";
  print_endline "  ct-verify-bench I W ... Benchmark deterministic confidential-transaction verification natively";
  print_endline "";
  print_endline "Examples:";
  print_endline "  isabella_cli mod-centered 7 5";
  print_endline "  isabella_cli --json ntt-fast \"[1,2,3,4]\" 17 3329 4";
  print_endline "  isabella_cli kyber-ntt \"[1,0,0,...,0]\"";
  print_endline "  isabella_cli --json dil-params 65";
  print_endline "  isabella_cli --json dil-power2round 12345 13";
  print_endline "  isabella_cli --json cb-prove 2 2 17 3 5 \"[[5,1,2],[4,-1,3]]\" \"[5,5]\" \"[1,2]\" \"[0,1]\"";
  print_endline "  isabella_cli --json cr-prove 2 2 17 6 5 3 \"[[5,1,2],[4,-1,3]]\" \"[13,8]\" 5 \"[1,2]\" \"[1,0,1]\" \"[[1,0],[0,1],[1,1]]\" \"[0,1,0]\" \"[[0,1],[1,0],[0,-1]]\" \"[[0,1],[0,1],[0,1],[0,1]]\" \"[[[1,0],[0,0],[1,-1]],[[1,0],[0,0],[1,-1]],[[1,0],[0,0],[1,-1]],[[1,0],[0,0],[1,-1]]]\"";
  print_endline "  isabella_cli --json ct-nullifier 2 2 17 6 \"[[5,1,2],[4,-1,3]]\" 5 \"[1,2]\"";
  print_endline "";
  print_endline "All functions are formally verified in Isabelle/HOL."

(** {1 Main} *)

let run_command cmd args =
  match cmd with
  | "examples" | "example" -> run_examples ()
  | "mod-centered" -> cmd_mod_centered args
  | "dist0" -> cmd_dist0 args
  | "encode-bit" -> cmd_encode_bit args
  | "decode-bit" -> cmd_decode_bit args
  | "inner-prod" -> cmd_inner_prod args
  | "vec-add" -> cmd_vec_add args
  | "transpose" -> cmd_transpose args
  | "mat-vec-mult" -> cmd_mat_vec_mult args
  (* NTT commands *)
  | "ntt-fast" -> cmd_ntt_fast args
  | "intt-fast" -> cmd_intt_fast args
  | "ntt-pointwise" -> cmd_ntt_pointwise args
  | "power-mod" -> cmd_power_mod args
  | "mod-inverse" -> cmd_mod_inverse args
  | "is-primitive-root" -> cmd_is_primitive_root args
  (* Polynomial commands *)
  | "poly-mult" -> cmd_poly_mult args
  | "ring-mult" -> cmd_ring_mult args
  (* Kyber commands *)
  | "kyber-ntt" -> cmd_kyber_ntt args
  | "kyber-intt" -> cmd_kyber_intt args
  | "kyber-poly-mult" -> cmd_kyber_poly_mult args
  | "kyber-encode-msg" -> cmd_kyber_encode_msg args
  | "kyber-decode-msg" -> cmd_kyber_decode_msg args
  (* Dilithium commands *)
  | "dil-mod-centered" -> cmd_dil_mod_centered args
  | "dil-power2round" -> cmd_dil_power2round args
  | "dil-decompose" -> cmd_dil_decompose args
  | "dil-highbits" -> cmd_dil_highbits args
  | "dil-lowbits" -> cmd_dil_lowbits args
  | "dil-makehint" -> cmd_dil_makehint args
  | "dil-usehint" -> cmd_dil_usehint args
  | "dil-params" -> cmd_dil_params args
  | "dil-check-bound" -> cmd_dil_check_bound args
  | "dil-hint-weight" -> cmd_dil_hint_weight args
  | "cb-params" -> cmd_cb_params args
  | "cb-valid-params" -> cmd_cb_valid_params args
  | "cb-rand-commit-key" -> cmd_cb_rand_commit_key args
  | "cb-rand-commit" -> cmd_cb_rand_commit args
  | "cb-valid-witness" -> cmd_cb_valid_witness args
  | "cb-valid-mask" -> cmd_cb_valid_mask args
  | "cb-valid-response" -> cmd_cb_valid_response args
  | "cb-balance-commitment" -> cmd_cb_balance_commitment args
  | "cb-canonical-challenge" -> cmd_cb_canonical_challenge args
  | "cb-sigma-commit" -> cmd_cb_sigma_commit args
  | "cb-sigma-respond" -> cmd_cb_sigma_respond args
  | "cb-sigma-verify" -> cmd_cb_sigma_verify args
  | "cb-prove" -> cmd_cb_prove args
  | "cb-verify" -> cmd_cb_verify args
  | "cr-amount-commitment" -> cmd_cr_amount_commitment args
  | "cr-prove" -> cmd_cr_prove args
  | "cr-verify" -> cmd_cr_verify args
  | "cr-verify-bench" -> cmd_cr_verify_bench args
  | "ct-merkle-leaf" -> cmd_ct_merkle_leaf args
  | "ct-merkle-empty" -> cmd_ct_merkle_empty args
  | "ct-merkle-node" -> cmd_ct_merkle_node args
  | "ct-merkle-root" -> cmd_ct_merkle_root args
  | "ct-merkle-member-prove" -> cmd_ct_merkle_member_prove args
  | "ct-merkle-member-verify" -> cmd_ct_merkle_member_verify args
  | "ct-transaction-context" -> cmd_ct_transaction_context args
  | "ct-nullifier" -> cmd_ct_nullifier args
  | "ct-nullifier-canonical-challenge" -> cmd_ct_nullifier_canonical_challenge args
  | "ct-nullifier-prove" -> cmd_ct_nullifier_prove args
  | "ct-nullifier-verify" -> cmd_ct_nullifier_verify args
  | "ct-member-prove" -> cmd_ct_member_prove args
  | "ct-member-verify" -> cmd_ct_member_verify args
  | "ct-ledger-step-verify" -> cmd_ct_ledger_step_verify args
  | "ct-prove" -> cmd_ct_prove args
  | "ct-prove-merkle" -> cmd_ct_prove_merkle args
  | "ct-verify" -> cmd_ct_verify args
  | "ct-verify-merkle" -> cmd_ct_verify_merkle args
  | "ct-verify-bench" -> cmd_ct_verify_bench args
  | _ -> output_error (Printf.sprintf "Unknown command: %s. Use --help for usage." cmd)

let () =
  let args = Array.to_list Sys.argv |> List.tl in
  (* Handle --json flag *)
  let args = match args with
    | "--json" :: rest -> output_format := Json; rest
    | _ -> args
  in
  match args with
  | [] -> show_help ()
  | ["--help"] | ["-h"] | ["help"] -> show_help ()
  | cmd :: rest -> run_command cmd rest
