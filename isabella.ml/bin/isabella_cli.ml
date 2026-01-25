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

let[@warning "-32"] parse_mat s =
  (* Parse "[[1,2],[3,4]]" *)
  let s = String.trim s in
  if String.length s < 2 then None
  else
    let s = String.sub s 1 (String.length s - 2) in  (* remove outer [] *)
    (* Split by "],["  *)
    let rows = Str.split (Str.regexp {|\],\[|}) s in
    try Some (List.map (fun row ->
      let row = String.trim row in
      let row = if String.length row > 0 && row.[0] = '[' then
        String.sub row 1 (String.length row - 1)
      else if String.length row > 0 && row.[String.length row - 1] = ']' then
        String.sub row 0 (String.length row - 1)
      else row in
      List.map (fun p -> int_of_string (String.trim p))
        (String.split_on_char ',' row)
    ) rows)
    with Failure _ -> None

let[@warning "-32"] string_of_mat m =
  "[" ^ String.concat ", " (List.map string_of_vec m) ^ "]"

let[@warning "-32"] json_of_mat m =
  "[" ^ String.concat "," (List.map json_of_vec m) ^ "]"

(** JSON output helpers *)
let[@warning "-32"] output_result key value =
  match !output_format with
  | Human -> Printf.printf "%s = %s\n" key value
  | Json -> Printf.printf "{\"result\":%s}\n" value

let output_error msg =
  match !output_format with
  | Human -> Printf.eprintf "Error: %s\n" msg
  | Json -> Printf.printf "{\"error\":\"%s\"}\n" msg

(** {1 Commands} *)

let cmd_mod_centered args =
  match args with
  | [x_str; q_str] ->
    (match parse_int x_str, parse_int q_str with
     | Some x, Some q ->
       let result = Zq.mod_centered x q in
       Printf.printf "mod_centered %d %d = %d\n" x q result
     | _ -> print_endline "Error: Expected two integers (X Q)")
  | _ -> print_endline "Usage: mod-centered X Q"

let cmd_dist0 args =
  match args with
  | [q_str; x_str] ->
    (match parse_int q_str, parse_int x_str with
     | Some q, Some x ->
       let result = Zq.dist0 q x in
       Printf.printf "dist0 %d %d = %d\n" q x result
     | _ -> print_endline "Error: Expected two integers (Q X)")
  | _ -> print_endline "Usage: dist0 Q X"

let cmd_encode_bit args =
  match args with
  | [q_str; b_str] ->
    (match parse_int q_str, parse_bool b_str with
     | Some q, Some b ->
       let result = Zq.encode_bit q b in
       Printf.printf "encode_bit %d %b = %d\n" q b result
     | _ -> print_endline "Error: Expected integer Q and boolean B")
  | _ -> print_endline "Usage: encode-bit Q B"

let cmd_decode_bit args =
  match args with
  | [q_str; x_str] ->
    (match parse_int q_str, parse_int x_str with
     | Some q, Some x ->
       let result = Zq.decode_bit q x in
       Printf.printf "decode_bit %d %d = %b\n" q x result
     | _ -> print_endline "Error: Expected two integers (Q X)")
  | _ -> print_endline "Usage: decode-bit Q X"

let cmd_inner_prod args =
  match args with
  | [v1_str; v2_str] ->
    (match parse_vec v1_str, parse_vec v2_str with
     | Some v1, Some v2 ->
       let result = Listvec.inner_prod v1 v2 in
       Printf.printf "inner_prod %s %s = %d\n" (string_of_vec v1) (string_of_vec v2) result
     | _ -> print_endline "Error: Expected two vectors")
  | _ -> print_endline "Usage: inner-prod \"[v1]\" \"[v2]\""

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
  print_endline "Examples:";
  print_endline "  isabella_cli mod-centered 7 5";
  print_endline "  isabella_cli --json ntt-fast \"[1,2,3,4]\" 17 3329 4";
  print_endline "  isabella_cli kyber-ntt \"[1,0,0,...,0]\"  # 256 coefficients";
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
