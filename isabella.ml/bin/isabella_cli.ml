(** Isabella CLI - Command-line interface for the Isabella library *)

open Canon

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

(* Unused for now, but kept for future commands *)
let[@warning "-32"] _parse_mat s =
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

let[@warning "-32"] _string_of_mat m =
  "[" ^ String.concat ", " (List.map string_of_vec m) ^ "]"

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
       Printf.printf "vec_add %s %s = %s\n" (string_of_vec v1) (string_of_vec v2) (string_of_vec result)
     | _ -> print_endline "Error: Expected two vectors")
  | _ -> print_endline "Usage: vec-add \"[v1]\" \"[v2]\""

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
  print_endline "Usage: isabella_cli <command> [options]";
  print_endline "";
  print_endline "Commands:";
  print_endline "  examples           Run example computations";
  print_endline "  mod-centered X Q   Compute centered modular reduction";
  print_endline "  dist0 Q X          Compute distance from zero in Z_q";
  print_endline "  encode-bit Q B     Encode a bit (0 or 1) for LWE";
  print_endline "  decode-bit Q X     Decode an LWE value to a bit";
  print_endline "  inner-prod V1 V2   Compute inner product of two vectors";
  print_endline "  vec-add V1 V2      Add two vectors";
  print_endline "";
  print_endline "Options:";
  print_endline "  --help, -h         Show this help message";
  print_endline "";
  print_endline "Examples:";
  print_endline "  isabella_cli mod-centered 7 5";
  print_endline "  isabella_cli dist0 256 130";
  print_endline "  isabella_cli encode-bit 256 1";
  print_endline "  isabella_cli inner-prod \"1,2,3\" \"4,5,6\"";
  print_endline "";
  print_endline "All functions are formally verified in Isabelle/HOL."

(** {1 Main} *)

let () =
  let args = Array.to_list Sys.argv |> List.tl in
  match args with
  | [] -> show_help ()
  | ["--help"] | ["-h"] | ["help"] -> show_help ()
  | ["examples"] | ["example"] -> run_examples ()
  | "mod-centered" :: rest -> cmd_mod_centered rest
  | "dist0" :: rest -> cmd_dist0 rest
  | "encode-bit" :: rest -> cmd_encode_bit rest
  | "decode-bit" :: rest -> cmd_decode_bit rest
  | "inner-prod" :: rest -> cmd_inner_prod rest
  | "vec-add" :: rest -> cmd_vec_add rest
  | cmd :: _ -> Printf.printf "Unknown command: %s\nUse --help for usage.\n" cmd
