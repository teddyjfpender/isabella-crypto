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

let parse_string_list s =
  let trim_quotes s =
    let s = String.trim s in
    let len = String.length s in
    if len >= 2 && s.[0] = '"' && s.[len - 1] = '"'
    then String.sub s 1 (len - 2)
    else s
  in
  let inner = strip_outer_brackets s in
  if String.trim inner = "" then Some []
  else Some (List.map trim_quotes (split_top_level inner))

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

let max_safe_protocol_int = 9007199254740991

let safe_protocol_int value =
  value >= -max_safe_protocol_int && value <= max_safe_protocol_int

let safe_protocol_vec values =
  List.for_all safe_protocol_int values

let safe_protocol_mat rows =
  List.for_all safe_protocol_vec rows

let safe_protocol_cube mats =
  List.for_all safe_protocol_mat mats

let parse_canonical_int s =
  match parse_int s with
  | Some value when string_of_int value = s && safe_protocol_int value -> Some value
  | _ -> None

let parse_canonical_vec s =
  match parse_vec s with
  | Some value when json_of_vec value = s && safe_protocol_vec value -> Some value
  | _ -> None

let parse_canonical_mat s =
  match parse_mat s with
  | Some value when json_of_mat value = s && safe_protocol_mat value -> Some value
  | _ -> None

let parse_canonical_cube s =
  match parse_cube s with
  | Some value when json_of_cube value = s && safe_protocol_cube value -> Some value
  | _ -> None

let parse_canonical_bool_vec01 s =
  match parse_vec s with
  | Some values when json_of_vec values = s ->
    let rec loop acc = function
      | [] -> Some (List.rev acc)
      | 0 :: rest -> loop (false :: acc) rest
      | 1 :: rest -> loop (true :: acc) rest
      | _ -> None
    in
    loop [] values
  | _ -> None

let is_decimal_digit c =
  c >= '0' && c <= '9'

let canonical_bignum_parts label value =
  let len = String.length value in
  if len = 0 then invalid_arg (label ^ " must be a canonical decimal integer");
  let negative, first =
    if value.[0] = '-' then
      if len = 1 then invalid_arg (label ^ " must be a canonical decimal integer")
      else (true, 1)
    else if value.[0] = '+' then
      invalid_arg (label ^ " must be a canonical decimal integer")
    else (false, 0)
  in
  for index = first to len - 1 do
    if not (is_decimal_digit value.[index]) then
      invalid_arg (label ^ " must be a canonical decimal integer")
  done;
  if len - first > 1 && value.[first] = '0' then
    invalid_arg (label ^ " must be a canonical decimal integer");
  if negative && value.[first] = '0' then
    invalid_arg (label ^ " must be a canonical decimal integer");
  (negative, String.sub value first (len - first))

let decimal_divmod_256 digits =
  let carry = ref 0 in
  let quotient = Buffer.create (String.length digits) in
  let started = ref false in
  String.iter
    (fun c ->
       let value = (!carry * 10) + (Char.code c - Char.code '0') in
       let q = value / 256 in
       let r = value mod 256 in
       if q <> 0 || !started then begin
         Buffer.add_char quotient (Char.chr (Char.code '0' + q));
         started := true
       end;
       carry := r)
    digits;
  let q = if Buffer.length quotient = 0 then "0" else Buffer.contents quotient in
  (q, !carry)

let bignum_magnitude_le_bytes digits =
  let rec loop current acc =
    if current = "0" then List.rev acc
    else
      let quotient, remainder = decimal_divmod_256 current in
      loop quotient (remainder :: acc)
  in
  loop digits []

let bignum_length_le_bytes value =
  let rec loop remaining count acc =
    if count = 0 then List.rev acc
    else loop (remaining / 256) (count - 1) ((remaining mod 256) :: acc)
  in
  loop value 8 []

let encode_bignum_decimal label value =
  let negative, digits = canonical_bignum_parts label value in
  let magnitude = bignum_magnitude_le_bytes digits in
  let sign = if negative then 1 else 0 in
  [sign]
  @ bignum_length_le_bytes (List.length magnitude)
  @ magnitude

let encode_bignum_decimal_vec values =
  bignum_length_le_bytes (List.length values)
  @ List.concat
      (List.mapi
         (fun index value -> encode_bignum_decimal (Printf.sprintf "values[%d]" index) value)
         values)

let bigint_base = 1_000_000
let bigint_base_width = 6

type cli_bigint = {
  big_neg : bool;
  big_limbs : int list;  (* little-endian limbs in base 1_000_000 *)
}

let normalize_bigint_limbs limbs =
  let rec drop_high_zeroes = function
    | 0 :: rest -> drop_high_zeroes rest
    | rest -> rest
  in
  List.rev (drop_high_zeroes (List.rev limbs))

let make_bigint neg limbs =
  let limbs = normalize_bigint_limbs limbs in
  { big_neg = neg && limbs <> []; big_limbs = limbs }

let bigint_zero = { big_neg = false; big_limbs = [] }
let bigint_one = { big_neg = false; big_limbs = [1] }

let bigint_is_zero value =
  value.big_limbs = []

let bigint_abs value =
  { value with big_neg = false }

let bigint_negate value =
  if bigint_is_zero value then value
  else { value with big_neg = not value.big_neg }

let bigint_of_int value =
  if value = 0 then bigint_zero
  else make_bigint (value < 0) [abs value]

let compare_bigint_abs left right =
  let left_len = List.length left.big_limbs in
  let right_len = List.length right.big_limbs in
  if left_len <> right_len then compare left_len right_len
  else
    let rec compare_rev left right =
      match left, right with
      | [], [] -> 0
      | x :: xs, y :: ys ->
          let cmp = compare x y in
          if cmp <> 0 then cmp else compare_rev xs ys
      | _ -> invalid_arg "limb lists have different lengths"
    in
    compare_rev (List.rev left.big_limbs) (List.rev right.big_limbs)

let compare_bigint left right =
  match left.big_neg, right.big_neg with
  | true, false -> -1
  | false, true -> 1
  | false, false -> compare_bigint_abs left right
  | true, true -> -compare_bigint_abs left right

let add_bigint_abs_limbs left right =
  let rec loop xs ys carry acc =
    match xs, ys with
    | [], [] ->
        let acc = if carry = 0 then acc else carry :: acc in
        List.rev acc
    | x :: xt, [] | [], x :: xt ->
        let total = x + carry in
        loop xt [] (total / bigint_base) ((total mod bigint_base) :: acc)
    | x :: xt, y :: yt ->
        let total = x + y + carry in
        loop xt yt (total / bigint_base) ((total mod bigint_base) :: acc)
  in
  loop left right 0 []

let sub_bigint_abs_limbs left right =
  let rec loop xs ys borrow acc =
    match xs, ys with
    | [], [] ->
        if borrow = 0 then List.rev acc
        else invalid_arg "negative absolute subtraction"
    | x :: xt, [] ->
        let diff = x - borrow in
        if diff < 0 then loop xt [] 1 ((diff + bigint_base) :: acc)
        else loop xt [] 0 (diff :: acc)
    | x :: xt, y :: yt ->
        let diff = x - y - borrow in
        if diff < 0 then loop xt yt 1 ((diff + bigint_base) :: acc)
        else loop xt yt 0 (diff :: acc)
    | [], _ -> invalid_arg "negative absolute subtraction"
  in
  normalize_bigint_limbs (loop left right 0 [])

let bigint_add left right =
  if left.big_neg = right.big_neg then
    make_bigint left.big_neg (add_bigint_abs_limbs left.big_limbs right.big_limbs)
  else
    match compare_bigint_abs left right with
    | 0 -> bigint_zero
    | cmp when cmp > 0 ->
        make_bigint left.big_neg (sub_bigint_abs_limbs left.big_limbs right.big_limbs)
    | _ ->
        make_bigint right.big_neg (sub_bigint_abs_limbs right.big_limbs left.big_limbs)

let rec bigint_mul_small value scalar =
  if scalar = 0 || bigint_is_zero value then bigint_zero
  else if scalar < 0 then bigint_negate (bigint_mul_small value (-scalar))
  else
    let rec loop limbs carry acc =
      match limbs with
      | [] ->
          let rec emit_carry carry acc =
            if carry = 0 then List.rev acc
            else emit_carry (carry / bigint_base) ((carry mod bigint_base) :: acc)
          in
          emit_carry carry acc
      | limb :: rest ->
          let total = (limb * scalar) + carry in
          loop rest (total / bigint_base) ((total mod bigint_base) :: acc)
    in
    make_bigint value.big_neg (loop value.big_limbs 0 [])

let bigint_mul left right =
  if bigint_is_zero left || bigint_is_zero right then bigint_zero
  else
    let left_len = List.length left.big_limbs in
    let right_len = List.length right.big_limbs in
    let accum = Array.make (left_len + right_len + 1) 0 in
    List.iteri
      (fun i x ->
         List.iteri
           (fun j y ->
              accum.(i + j) <- accum.(i + j) + (x * y))
           right.big_limbs)
      left.big_limbs;
    let carry = ref 0 in
    for i = 0 to Array.length accum - 1 do
      let total = accum.(i) + !carry in
      accum.(i) <- total mod bigint_base;
      carry := total / bigint_base
    done;
    make_bigint (left.big_neg <> right.big_neg) (Array.to_list accum)

let bigint_shift_limbs value shift =
  if bigint_is_zero value then value
  else make_bigint value.big_neg (List.init shift (fun _ -> 0) @ value.big_limbs)

let bigint_best_mod_digit remainder shifted =
  let rec search low high best =
    if low > high then best
    else
      let mid = (low + high) / 2 in
      let candidate = bigint_mul_small shifted mid in
      if compare_bigint_abs candidate remainder <= 0 then
        search (mid + 1) high mid
      else
        search low (mid - 1) best
  in
  search 0 (bigint_base - 1) 0

let bigint_mod_abs value modulus =
  let value = bigint_abs value in
  let modulus = bigint_abs modulus in
  if compare_bigint_abs value modulus < 0 then value
  else
    let remainder = ref value in
    let modulus_len = List.length modulus.big_limbs in
    let max_shift = List.length value.big_limbs - modulus_len in
    for shift = max_shift downto 0 do
      let shifted = bigint_shift_limbs modulus shift in
      if compare_bigint_abs !remainder shifted >= 0 then begin
        let digit = bigint_best_mod_digit !remainder shifted in
        if digit > 0 then
          remainder :=
            make_bigint false
              (sub_bigint_abs_limbs
                 (!remainder).big_limbs
                 (bigint_mul_small shifted digit).big_limbs)
      end
    done;
    !remainder

let bigint_mod value modulus =
  if compare_bigint modulus bigint_one <= 0 then
    invalid_arg "modulus must be greater than 1";
  let reduced = bigint_mod_abs value modulus in
  if value.big_neg && not (bigint_is_zero reduced) then
    make_bigint false (sub_bigint_abs_limbs modulus.big_limbs reduced.big_limbs)
  else reduced

let bigint_abs_leq value bound =
  compare_bigint bound bigint_zero >= 0 &&
  compare_bigint_abs value bound <= 0

let bigint_to_abs_decimal value =
  match List.rev value.big_limbs with
  | [] -> "0"
  | high :: rest ->
      string_of_int high ^
      String.concat ""
        (List.map
           (fun limb -> Printf.sprintf "%0*d" bigint_base_width limb)
           rest)

let string_of_bigint value =
  let digits = bigint_to_abs_decimal value in
  if value.big_neg then "-" ^ digits else digits

let parse_canonical_bigint s =
  try
    let negative, digits = canonical_bignum_parts "integer" s in
    let value =
      String.fold_left
        (fun acc digit ->
           let digit_value = Char.code digit - Char.code '0' in
           bigint_add (bigint_mul_small acc 10) (bigint_of_int digit_value))
        bigint_zero
        digits
    in
    Some (if negative then bigint_negate value else value)
  with Invalid_argument _ -> None

let bigint_vec_text values =
  "[" ^ String.concat "," (List.map string_of_bigint values) ^ "]"

let bigint_mat_text rows =
  "[" ^ String.concat "," (List.map bigint_vec_text rows) ^ "]"

let bigint_cube_text cubes =
  "[" ^ String.concat "," (List.map bigint_mat_text cubes) ^ "]"

let json_of_bigint value =
  json_of_string (string_of_bigint value)

let json_of_bigint_vec values =
  "[" ^ String.concat "," (List.map json_of_bigint values) ^ "]"

let json_of_bigint_mat rows =
  "[" ^ String.concat "," (List.map json_of_bigint_vec rows) ^ "]"

let json_of_bigint_cube cubes =
  "[" ^ String.concat "," (List.map json_of_bigint_mat cubes) ^ "]"

let parse_canonical_bigint_vec s =
  let parse_inner inner =
    if String.trim inner = "" then Some []
    else
      let rec parse_parts acc = function
        | [] -> Some (List.rev acc)
        | part :: rest ->
            match parse_canonical_bigint part with
            | Some value -> parse_parts (value :: acc) rest
            | None -> None
      in
      parse_parts [] (split_top_level inner)
  in
  if String.length s >= 2 && s.[0] = '[' && s.[String.length s - 1] = ']' then
    let inner = String.sub s 1 (String.length s - 2) in
    match parse_inner inner with
    | Some values when bigint_vec_text values = s -> Some values
    | _ -> None
  else None

let parse_canonical_bigint_mat s =
  let parse_inner inner =
    if String.trim inner = "" then Some []
    else
      let rec parse_rows acc = function
        | [] -> Some (List.rev acc)
        | row :: rest ->
            match parse_canonical_bigint_vec row with
            | Some value -> parse_rows (value :: acc) rest
            | None -> None
      in
      parse_rows [] (split_top_level inner)
  in
  if String.length s >= 2 && s.[0] = '[' && s.[String.length s - 1] = ']' then
    let inner = String.sub s 1 (String.length s - 2) in
    match parse_inner inner with
    | Some rows when bigint_mat_text rows = s -> Some rows
    | _ -> None
  else None

let parse_canonical_bigint_cube s =
  let parse_inner inner =
    if String.trim inner = "" then Some []
    else
      let rec parse_cubes acc = function
        | [] -> Some (List.rev acc)
        | cube :: rest ->
            match parse_canonical_bigint_mat cube with
            | Some value -> parse_cubes (value :: acc) rest
            | None -> None
      in
      parse_cubes [] (split_top_level inner)
  in
  if String.length s >= 2 && s.[0] = '[' && s.[String.length s - 1] = ']' then
    let inner = String.sub s 1 (String.length s - 2) in
    match parse_inner inner with
    | Some cubes when bigint_cube_text cubes = s -> Some cubes
    | _ -> None
  else None

let encode_bigint_value value =
  let magnitude = bignum_magnitude_le_bytes (bigint_to_abs_decimal value) in
  let sign = if value.big_neg then 1 else 0 in
  [sign] @ bignum_length_le_bytes (List.length magnitude) @ magnitude

let ascii_bytes text =
  List.init (String.length text) (fun index -> Char.code text.[index])

let json_of_bigint_balance_proof as_ zs =
  Printf.sprintf "{\"as\":%s,\"zs\":%s}" (json_of_bigint_mat as_) (json_of_bigint_mat zs)

let json_of_bigint_range_proof bits comps amount_as amount_zs pair_ass pair_zss =
  Printf.sprintf
    "{\"bits\":%s,\"comps\":%s,\"amountAs\":%s,\"amountZs\":%s,\"pairAss\":%s,\"pairZss\":%s}"
    (json_of_bigint_mat bits)
    (json_of_bigint_mat comps)
    (json_of_bigint_mat amount_as)
    (json_of_bigint_mat amount_zs)
    (json_of_bigint_cube pair_ass)
    (json_of_bigint_cube pair_zss)

let json_of_bigint_nullifier_proof a_commits a_nullifiers z_msgs z_rands =
  Printf.sprintf
    "{\"aCommits\":%s,\"aNullifiers\":%s,\"zMsgs\":%s,\"zRands\":%s}"
    (json_of_bigint_mat a_commits)
    (json_of_bigint_mat a_nullifiers)
    (json_of_bigint_mat z_msgs)
    (json_of_bigint_mat z_rands)

type big_cb_params = {
  big_cb_n1 : int;
  big_cb_n2 : int;
  big_cb_m : int;
  big_cb_q : cli_bigint;
  big_cb_beta : cli_bigint;
}

type big_opening = {
  big_open_msg : cli_bigint list;
  big_open_rand : cli_bigint list;
}

let big_cb_fs_domain = 1001
let big_cr_fs_domain = 2001
let big_nf_fs_domain = 3001
let big_cb_fs_rounds = 128
let big_cb_transcript_dst = "ISABELLA-CT-FS-v1"

let make_big_cb_params m_str n2_str q_str beta_str =
  match
    parse_canonical_int m_str,
    parse_canonical_int n2_str,
    parse_canonical_bigint q_str,
    parse_canonical_bigint beta_str
  with
  | Some m, Some n2, Some q, Some beta ->
      Some { big_cb_n1 = 1; big_cb_n2 = n2; big_cb_m = m; big_cb_q = q; big_cb_beta = beta }
  | _ -> None

let valid_big_cb_params params =
  params.big_cb_n1 = 1 &&
  params.big_cb_n2 > 0 &&
  params.big_cb_m > 0 &&
  compare_bigint params.big_cb_q bigint_one > 0 &&
  compare_bigint params.big_cb_beta bigint_zero > 0

let valid_big_vec expected values =
  List.length values = expected

let valid_big_commit_key params ck =
  valid_big_cb_params params &&
  List.length ck = params.big_cb_m &&
  List.for_all (valid_big_vec (params.big_cb_n1 + params.big_cb_n2)) ck

let rec drop_n count values =
  if count <= 0 then values
  else
    match values with
    | [] -> []
    | _ :: rest -> drop_n (count - 1) rest

let big_rand_commit_key params ck =
  List.map (drop_n params.big_cb_n1) ck

let bigint_vec_add left right =
  List.map2 bigint_add left right

let bigint_scalar_mult scalar values =
  List.map (bigint_mul scalar) values

let bigint_mat_vec_mult matrix vector =
  List.map
    (fun row ->
       if List.length row <> List.length vector then
         invalid_arg "matrix row length must match vector length";
       List.fold_left2
         (fun acc left right -> bigint_add acc (bigint_mul left right))
         bigint_zero
         row
         vector)
    matrix

let bigint_vec_mod values modulus =
  List.map (fun value -> bigint_mod value modulus) values

let bigint_mat_vec_mult_mod matrix vector modulus =
  bigint_vec_mod (bigint_mat_vec_mult matrix vector) modulus

let big_rand_commit params ck r =
  bigint_mat_vec_mult_mod (big_rand_commit_key params ck) r params.big_cb_q

let bigint_all_bounded values bound =
  compare_bigint bound bigint_zero >= 0 &&
  List.for_all (fun value -> bigint_abs_leq value bound) values

let valid_big_witness params r =
  valid_big_cb_params params &&
  valid_big_vec params.big_cb_n2 r &&
  bigint_all_bounded r (bigint_mul_small params.big_cb_beta 4)

let valid_big_mask params gamma y =
  valid_big_cb_params params &&
  valid_big_vec params.big_cb_n2 y &&
  bigint_all_bounded y gamma

let valid_big_response params gamma challenge z =
  (challenge = 0 || challenge = 1) &&
  valid_big_cb_params params &&
  valid_big_vec params.big_cb_n2 z &&
  bigint_all_bounded z
    (bigint_add gamma (bigint_mul_small params.big_cb_beta (4 * challenge)))

let big_balance_relation params ck c r =
  try
    valid_big_commit_key params ck &&
    valid_big_vec params.big_cb_m c &&
    valid_big_witness params r &&
    big_rand_commit params ck r = c
  with Invalid_argument _ -> false

let big_sigma_respond r y challenge =
  bigint_vec_add y (bigint_scalar_mult (bigint_of_int challenge) r)

let big_fs_transcript_bytes domain round fields =
  ascii_bytes big_cb_transcript_dst
  @ bignum_length_le_bytes domain
  @ bignum_length_le_bytes round
  @ bignum_length_le_bytes (List.length fields)
  @ List.concat (List.map encode_bigint_value fields)

let big_binary_fs_challenge domain fields round =
  match Repeated_fs.sha3_256 (big_fs_transcript_bytes domain round fields) with
  | first :: _ -> first land 1
  | [] -> failwith "sha3_256 produced no output"

let bigint_sum values =
  List.fold_left bigint_add bigint_zero values

let bigint_matrix_sum rows =
  List.fold_left (fun acc row -> bigint_add acc (bigint_sum row)) bigint_zero rows

let big_fs_fields ck c as_ =
  [bigint_matrix_sum ck; bigint_sum c; bigint_matrix_sum as_]

let big_fs_challenges ck c as_ rounds =
  let fields = big_fs_fields ck c as_ in
  List.init rounds (fun round -> big_binary_fs_challenge big_cb_fs_domain fields round)

let big_sigma_verify params gamma ck c a challenge z =
  try
    valid_big_commit_key params ck &&
    valid_big_vec params.big_cb_m c &&
    valid_big_vec params.big_cb_m a &&
    valid_big_response params gamma challenge z &&
    big_rand_commit params ck z =
      bigint_vec_mod
        (bigint_vec_add a (bigint_scalar_mult (bigint_of_int challenge) c))
        params.big_cb_q
  with Invalid_argument _ -> false

let big_fs_prove params gamma ck c r ys =
  try
    let as_ = List.map (big_rand_commit params ck) ys in
    let challenges = big_fs_challenges ck c as_ big_cb_fs_rounds in
    let zs = List.map2 (big_sigma_respond r) ys challenges in
    if List.length ys = big_cb_fs_rounds &&
       big_balance_relation params ck c r &&
       List.for_all (valid_big_mask params gamma) ys &&
       List.for_all2 (valid_big_response params gamma) challenges zs
    then Some (as_, zs)
    else None
  with Invalid_argument _ -> None

let big_fs_verify params gamma ck c as_ zs =
  try
    let challenges = big_fs_challenges ck c as_ big_cb_fs_rounds in
    valid_big_cb_params params &&
    valid_big_commit_key params ck &&
    List.length as_ = big_cb_fs_rounds &&
    List.length zs = big_cb_fs_rounds &&
    List.for_all2
      (fun a (challenge, z) -> big_sigma_verify params gamma ck c a challenge z)
      as_
      (List.combine challenges zs)
  with Invalid_argument _ -> false

let big_opening msg rand =
  { big_open_msg = msg; big_open_rand = rand }

let valid_big_opening_shape params opening =
  valid_big_cb_params params &&
  valid_big_vec params.big_cb_n1 opening.big_open_msg &&
  valid_big_vec params.big_cb_n2 opening.big_open_rand

let valid_big_opening params opening =
  valid_big_opening_shape params opening &&
  bigint_all_bounded opening.big_open_msg params.big_cb_beta &&
  bigint_all_bounded opening.big_open_rand params.big_cb_beta

let valid_big_bit_opening params opening =
  valid_big_opening params opening &&
  bigint_all_bounded opening.big_open_msg bigint_one

let big_commit params ck opening =
  bigint_mat_vec_mult_mod ck (opening.big_open_msg @ opening.big_open_rand) params.big_cb_q

let big_zero_opening params =
  { big_open_msg = List.init params.big_cb_n1 (fun _ -> bigint_zero);
    big_open_rand = List.init params.big_cb_n2 (fun _ -> bigint_zero) }

let big_one_opening params =
  { big_open_msg = [bigint_one];
    big_open_rand = List.init params.big_cb_n2 (fun _ -> bigint_zero) }

let big_opening_add left right =
  { big_open_msg = bigint_vec_add left.big_open_msg right.big_open_msg;
    big_open_rand = bigint_vec_add left.big_open_rand right.big_open_rand }

let big_opening_sub left right =
  { big_open_msg = bigint_vec_add left.big_open_msg (bigint_scalar_mult (bigint_of_int (-1)) right.big_open_msg);
    big_open_rand = bigint_vec_add left.big_open_rand (bigint_scalar_mult (bigint_of_int (-1)) right.big_open_rand) }

let big_opening_scale scalar opening =
  { big_open_msg = bigint_scalar_mult scalar opening.big_open_msg;
    big_open_rand = bigint_scalar_mult scalar opening.big_open_rand }

let big_weighted_opening params base openings =
  List.fold_right
    (fun opening acc -> big_opening_add opening (big_opening_scale base acc))
    openings
    (big_zero_opening params)

let big_weighted_commitment params ck base commitments =
  List.fold_right
    (fun row acc ->
       bigint_vec_mod
         (bigint_vec_add row (bigint_scalar_mult base acc))
         params.big_cb_q)
    commitments
    (big_rand_commit params ck (List.init params.big_cb_n2 (fun _ -> bigint_zero)))

let big_amount_of_opening opening =
  match opening.big_open_msg with
  | value :: _ -> value
  | [] -> bigint_zero

let big_bit_pair_relation params bit_opening comp_opening =
  valid_big_bit_opening params bit_opening &&
  valid_big_bit_opening params comp_opening &&
  compare_bigint
    (bigint_add (big_amount_of_opening bit_opening) (big_amount_of_opening comp_opening))
    bigint_one = 0

let big_recompose_bits openings =
  let rec loop weight acc = function
    | [] -> acc
    | opening :: rest ->
        loop
          (bigint_mul_small weight 2)
          (bigint_add acc (bigint_mul (big_amount_of_opening opening) weight))
          rest
  in
  loop bigint_one bigint_zero openings

let big_cr_amount_commitment params ck c_amount c_bits =
  bigint_vec_mod
    (bigint_vec_add
       c_amount
       (bigint_scalar_mult (bigint_of_int (-1)) (big_weighted_commitment params ck (bigint_of_int 2) c_bits)))
    params.big_cb_q

let big_cr_pair_commitment params ck c_bit c_comp =
  bigint_vec_mod
    (bigint_vec_add
       (bigint_vec_add c_bit c_comp)
       (bigint_scalar_mult (bigint_of_int (-1)) (big_commit params ck (big_one_opening params))))
    params.big_cb_q

let big_cr_pair_commitments params ck c_bits c_comps =
  List.map2 (big_cr_pair_commitment params ck) c_bits c_comps

let big_cr_amount_opening params amount_opening bit_openings =
  big_opening_sub amount_opening (big_weighted_opening params (bigint_of_int 2) bit_openings)

let big_cr_pair_opening params bit_opening comp_opening =
  big_opening_sub (big_opening_add bit_opening comp_opening) (big_one_opening params)

let big_cr_pair_openings params bit_openings comp_openings =
  List.map2 (big_cr_pair_opening params) bit_openings comp_openings

let bigint_pow2 exponent =
  if exponent < 0 then invalid_arg "negative exponent";
  let rec loop acc remaining =
    if remaining = 0 then acc
    else loop (bigint_mul_small acc 2) (remaining - 1)
  in
  loop bigint_one exponent

let big_cr_amount_witness_bound params k =
  bigint_mul (bigint_pow2 k) params.big_cb_beta

let big_cr_pair_witness_bound params =
  bigint_mul_small params.big_cb_beta 2

let valid_big_cr_amount_witness params k r =
  k >= 0 &&
  valid_big_vec params.big_cb_n2 r &&
  bigint_all_bounded r (big_cr_amount_witness_bound params k)

let valid_big_cr_pair_witness params r =
  valid_big_vec params.big_cb_n2 r &&
  bigint_all_bounded r (big_cr_pair_witness_bound params)

let big_cr_amount_response_bound params gamma k challenge =
  bigint_add gamma (bigint_mul_small (big_cr_amount_witness_bound params k) challenge)

let big_cr_pair_response_bound params gamma challenge =
  bigint_add gamma (bigint_mul_small (big_cr_pair_witness_bound params) challenge)

let valid_big_cr_amount_response params gamma k challenge z =
  (challenge = 0 || challenge = 1) &&
  valid_big_vec params.big_cb_n2 z &&
  bigint_all_bounded z (big_cr_amount_response_bound params gamma k challenge)

let valid_big_cr_pair_response params gamma challenge z =
  (challenge = 0 || challenge = 1) &&
  valid_big_vec params.big_cb_n2 z &&
  bigint_all_bounded z (big_cr_pair_response_bound params gamma challenge)

let big_cr_relation params ck c_amount amount_opening bit_openings comp_openings =
  try
    valid_big_cb_params params &&
    valid_big_commit_key params ck &&
    valid_big_vec params.big_cb_m c_amount &&
    List.length bit_openings = List.length comp_openings &&
    big_commit params ck amount_opening = c_amount &&
    List.for_all2 (big_bit_pair_relation params) bit_openings comp_openings &&
    compare_bigint (big_amount_of_opening amount_opening) (big_recompose_bits bit_openings) = 0
  with Invalid_argument _ -> false

let bigint_cube_sum cubes =
  List.fold_left (fun acc rows -> bigint_add acc (bigint_matrix_sum rows)) bigint_zero cubes

let big_cr_fs_fields ck c_amount c_bits c_comps amount_as pair_ass =
  [ bigint_matrix_sum ck;
    bigint_sum c_amount;
    bigint_matrix_sum c_bits;
    bigint_matrix_sum c_comps;
    bigint_matrix_sum amount_as;
    bigint_cube_sum pair_ass ]

let big_cr_fs_challenges ck c_amount c_bits c_comps amount_as pair_ass rounds =
  let fields = big_cr_fs_fields ck c_amount c_bits c_comps amount_as pair_ass in
  List.init rounds (fun round -> big_binary_fs_challenge big_cr_fs_domain fields round)

let big_cr_sigma_verify params ck c a challenge z valid_response =
  try
    valid_big_commit_key params ck &&
    valid_big_vec params.big_cb_m c &&
    valid_big_vec params.big_cb_m a &&
    valid_response challenge z &&
    big_rand_commit params ck z =
      bigint_vec_mod
        (bigint_vec_add a (bigint_scalar_mult (bigint_of_int challenge) c))
        params.big_cb_q
  with Invalid_argument _ -> false

let big_cr_fs_prove params gamma k ck c_amount amount_opening bit_openings comp_openings y_amounts y_pairss =
  try
    let bits = List.map (big_commit params ck) bit_openings in
    let comps = List.map (big_commit params ck) comp_openings in
    let amount_witness = (big_cr_amount_opening params amount_opening bit_openings).big_open_rand in
    let pair_witnesses = List.map (fun opening -> opening.big_open_rand) (big_cr_pair_openings params bit_openings comp_openings) in
    let amount_as = List.map (big_rand_commit params ck) y_amounts in
    let pair_ass = List.map (List.map (big_rand_commit params ck)) y_pairss in
    let challenges = big_cr_fs_challenges ck c_amount bits comps amount_as pair_ass big_cb_fs_rounds in
    let amount_zs = List.map2 (big_sigma_respond amount_witness) y_amounts challenges in
    let pair_zss =
      List.map2
        (fun round_masks challenge ->
           List.map2 (fun mask witness -> big_sigma_respond witness mask challenge) round_masks pair_witnesses)
        y_pairss
        challenges
    in
    if k >= 0 &&
       List.length bit_openings = k &&
       List.length comp_openings = k &&
       List.length y_amounts = big_cb_fs_rounds &&
       List.length y_pairss = big_cb_fs_rounds &&
       List.for_all (fun round_masks -> List.length round_masks = k) y_pairss &&
       big_cr_relation params ck c_amount amount_opening bit_openings comp_openings &&
       List.for_all (valid_big_mask params gamma) y_amounts &&
       List.for_all (List.for_all (valid_big_mask params gamma)) y_pairss &&
       valid_big_cr_amount_witness params k amount_witness &&
       List.for_all (valid_big_cr_pair_witness params) pair_witnesses &&
       List.for_all2 (valid_big_cr_amount_response params gamma k) challenges amount_zs &&
       List.for_all2
         (fun challenge responses -> List.for_all (valid_big_cr_pair_response params gamma challenge) responses)
         challenges
         pair_zss
    then Some (bits, comps, amount_as, amount_zs, pair_ass, pair_zss)
    else None
  with Invalid_argument _ -> None

let big_cr_fs_verify params gamma k ck c_amount bits comps amount_as amount_zs pair_ass pair_zss =
  try
    let amount_commit = big_cr_amount_commitment params ck c_amount bits in
    let pairs = big_cr_pair_commitments params ck bits comps in
    let challenges = big_cr_fs_challenges ck c_amount bits comps amount_as pair_ass big_cb_fs_rounds in
    k >= 0 &&
    valid_big_cb_params params &&
    valid_big_commit_key params ck &&
    valid_big_vec params.big_cb_m c_amount &&
    List.length bits = k &&
    List.length comps = k &&
    List.length amount_as = big_cb_fs_rounds &&
    List.length amount_zs = big_cb_fs_rounds &&
    List.length pair_ass = big_cb_fs_rounds &&
    List.length pair_zss = big_cb_fs_rounds &&
    List.for_all (fun round_ass -> List.length round_ass = k) pair_ass &&
    List.for_all (fun round_zs -> List.length round_zs = k) pair_zss &&
    List.for_all2
      (fun a (challenge, z) ->
         big_cr_sigma_verify
           params
           ck
           amount_commit
           a
           challenge
           z
           (valid_big_cr_amount_response params gamma k))
      amount_as
      (List.combine challenges amount_zs) &&
    List.for_all2
      (fun round_ass (challenge, round_zs) ->
         List.for_all2
           (fun a (pair, z) ->
              big_cr_sigma_verify
                params
                ck
                pair
                a
                challenge
                z
                (valid_big_cr_pair_response params gamma))
           round_ass
           (List.combine pairs round_zs))
      pair_ass
      (List.combine challenges pair_zss)
  with Invalid_argument _ -> false

let valid_big_nf_mask params gamma opening =
  valid_big_opening_shape params opening &&
  bigint_all_bounded opening.big_open_msg gamma &&
  bigint_all_bounded opening.big_open_rand gamma

let big_nf_response_bound params gamma challenge =
  bigint_add gamma (bigint_mul_small params.big_cb_beta challenge)

let valid_big_nf_response params gamma challenge opening =
  (challenge = 0 || challenge = 1) &&
  valid_big_opening_shape params opening &&
  bigint_all_bounded opening.big_open_msg (big_nf_response_bound params gamma challenge) &&
  bigint_all_bounded opening.big_open_rand (big_nf_response_bound params gamma challenge)

let big_nf_sigma_respond opening mask challenge =
  { big_open_msg = big_sigma_respond opening.big_open_msg mask.big_open_msg challenge;
    big_open_rand = big_sigma_respond opening.big_open_rand mask.big_open_rand challenge }

let big_nf_relation params ck nk c nf opening =
  try
    valid_big_cb_params params &&
    valid_big_commit_key params ck &&
    valid_big_commit_key params nk &&
    valid_big_vec params.big_cb_m c &&
    valid_big_vec params.big_cb_m nf &&
    valid_big_opening params opening &&
    big_commit params ck opening = c &&
    big_commit params nk opening = nf
  with Invalid_argument _ -> false

let big_nf_fs_fields ck nk c nf a_commits a_nullifiers =
  [ bigint_matrix_sum ck;
    bigint_matrix_sum nk;
    bigint_sum c;
    bigint_sum nf;
    bigint_matrix_sum a_commits;
    bigint_matrix_sum a_nullifiers ]

let big_nf_fs_challenges ck nk c nf a_commits a_nullifiers rounds =
  let fields = big_nf_fs_fields ck nk c nf a_commits a_nullifiers in
  List.init rounds (fun round -> big_binary_fs_challenge big_nf_fs_domain fields round)

let big_nf_sigma_verify params gamma key target announcement challenge response =
  try
    valid_big_commit_key params key &&
    valid_big_vec params.big_cb_m target &&
    valid_big_vec params.big_cb_m announcement &&
    valid_big_nf_response params gamma challenge response &&
    big_commit params key response =
      bigint_vec_mod
        (bigint_vec_add announcement (bigint_scalar_mult (bigint_of_int challenge) target))
        params.big_cb_q
  with Invalid_argument _ -> false

let big_nf_fs_prove params gamma ck nk c nf opening masks =
  try
    let a_commits = List.map (big_commit params ck) masks in
    let a_nullifiers = List.map (big_commit params nk) masks in
    let challenges = big_nf_fs_challenges ck nk c nf a_commits a_nullifiers big_cb_fs_rounds in
    let responses = List.map2 (big_nf_sigma_respond opening) masks challenges in
    if List.length masks = big_cb_fs_rounds &&
       big_nf_relation params ck nk c nf opening &&
       List.for_all (valid_big_nf_mask params gamma) masks &&
       List.for_all2 (valid_big_nf_response params gamma) challenges responses
    then Some
      ( a_commits,
        a_nullifiers,
        List.map (fun response -> response.big_open_msg) responses,
        List.map (fun response -> response.big_open_rand) responses )
    else None
  with Invalid_argument _ -> None

let big_nf_fs_verify params gamma ck nk c nf a_commits a_nullifiers z_msgs z_rands =
  try
    let challenges = big_nf_fs_challenges ck nk c nf a_commits a_nullifiers big_cb_fs_rounds in
    let responses = List.map2 big_opening z_msgs z_rands in
    valid_big_cb_params params &&
    valid_big_commit_key params ck &&
    valid_big_commit_key params nk &&
    valid_big_vec params.big_cb_m c &&
    valid_big_vec params.big_cb_m nf &&
    List.length a_commits = big_cb_fs_rounds &&
    List.length a_nullifiers = big_cb_fs_rounds &&
    List.length z_msgs = big_cb_fs_rounds &&
    List.length z_rands = big_cb_fs_rounds &&
    List.for_all2
      (fun a_commit (a_nullifier, challenge, response) ->
         big_nf_sigma_verify params gamma ck c a_commit challenge response &&
         big_nf_sigma_verify params gamma nk nf a_nullifier challenge response)
      a_commits
      (List.map2
         (fun a_nullifier (challenge, response) -> (a_nullifier, challenge, response))
         a_nullifiers
         (List.combine challenges responses))
  with Invalid_argument _ -> false

let hex_of_bytes bytes =
  String.concat "" (List.map (Printf.sprintf "%02x") bytes)

let ct_bignum_merkle_dst = "ISABELLA-CT-MERKLE-BIGNUM-v1"
let ct_bignum_transaction_dst = "ISABELLA-CT-TX-BIGNUM-v1"
let ct_transaction_protocol_id = "ISABELLA-CT-SIS-NOTE"

let encode_i64_nonnegative label value =
  if value < 0 then invalid_arg (label ^ " must be non-negative");
  Repeated_fs.int64_le_bytes (Int64.of_int value)

let encode_printable_ascii label value =
  let bytes = ascii_bytes value in
  List.iteri
    (fun index byte ->
       if byte < 0x20 || byte > 0x7e then
         invalid_arg (Printf.sprintf "%s[%d] must be printable ASCII" label index))
    bytes;
  encode_i64_nonnegative (label ^ ".length") (List.length bytes) @ bytes

let encode_digest label digest =
  match Confidential_merkle.hex_to_bytes digest with
  | Some bytes -> encode_i64_nonnegative (label ^ ".length") (List.length bytes) @ bytes
  | None -> invalid_arg (label ^ " must be a canonical lowercase SHA3-256 digest")

let encode_digest_vec label digests =
  encode_i64_nonnegative (label ^ ".length") (List.length digests)
  @ List.concat
      (List.mapi
         (fun index digest -> encode_digest (Printf.sprintf "%s[%d]" label index) digest)
         digests)

let encode_bool_vec label values =
  encode_i64_nonnegative (label ^ ".length") (List.length values)
  @ List.concat
      (List.map (fun value -> encode_i64_nonnegative label (if value then 1 else 0)) values)

let encode_bigint_vec label values =
  encode_i64_nonnegative (label ^ ".length") (List.length values)
  @ List.concat (List.map encode_bigint_value values)

let encode_bigint_mat label rows =
  encode_i64_nonnegative (label ^ ".length") (List.length rows)
  @ List.concat
      (List.mapi
         (fun index row -> encode_bigint_vec (Printf.sprintf "%s[%d]" label index) row)
         rows)

let encode_bigint_cube label cubes =
  encode_i64_nonnegative (label ^ ".length") (List.length cubes)
  @ List.concat
      (List.mapi
         (fun index rows -> encode_bigint_mat (Printf.sprintf "%s[%d]" label index) rows)
         cubes)

let digest_bytes bytes =
  hex_of_bytes (Repeated_fs.sha3_256 bytes)

let ct_bignum_merkle_preimage tag body =
  ascii_bytes ct_bignum_merkle_dst @ encode_i64_nonnegative "merkle tag" tag @ body

let ct_bignum_merkle_leaf commitment =
  digest_bytes (ct_bignum_merkle_preimage 0 (encode_bigint_vec "commitment" commitment))

let ct_bignum_merkle_empty width =
  digest_bytes (ct_bignum_merkle_preimage 2 (encode_i64_nonnegative "width" width))

let ct_bignum_merkle_node left right =
  digest_bytes (ct_bignum_merkle_preimage 1 (encode_digest "left" left @ encode_digest "right" right))

let ct_bignum_same_width commitments width =
  List.for_all (fun commitment -> List.length commitment = width) commitments

let ct_bignum_merkle_compress_level width level =
  let rec loop acc = function
    | [] -> List.rev acc
    | [left] -> List.rev (ct_bignum_merkle_node left (ct_bignum_merkle_empty width) :: acc)
    | left :: right :: rest -> loop (ct_bignum_merkle_node left right :: acc) rest
  in
  match level with
  | [] -> []
  | [x] -> [x]
  | xs -> loop [] xs

let ct_bignum_merkle_root commitments =
  let width =
    match commitments with
    | [] -> 0
    | first :: _ -> List.length first
  in
  if not (ct_bignum_same_width commitments width) then
    invalid_arg "Bignum Merkle commitments must all have the same width";
  match commitments with
  | [] -> ct_bignum_merkle_empty 0
  | _ ->
    let rec loop level =
      match level with
      | [] -> ct_bignum_merkle_empty width
      | [x] -> x
      | xs -> loop (ct_bignum_merkle_compress_level width xs)
    in
    loop (List.map ct_bignum_merkle_leaf commitments)

let ct_bignum_merkle_path_root commitment siblings directions =
  let rec loop acc siblings directions =
    match siblings, directions with
    | [], [] -> Some acc
    | sibling :: rest_siblings, false :: rest_directions ->
      (try loop (ct_bignum_merkle_node acc sibling) rest_siblings rest_directions
       with Invalid_argument _ -> None)
    | sibling :: rest_siblings, true :: rest_directions ->
      (try loop (ct_bignum_merkle_node sibling acc) rest_siblings rest_directions
       with Invalid_argument _ -> None)
    | _ -> None
  in
  loop (ct_bignum_merkle_leaf commitment) siblings directions

let ct_bignum_merkle_membership_index ledger commitment =
  let rec loop index = function
    | [] -> None
    | x :: xs -> if x = commitment then Some index else loop (index + 1) xs
  in
  loop 0 ledger

let ct_bignum_merkle_membership_prove ledger commitment =
  match ct_bignum_merkle_membership_index ledger commitment with
  | None -> None
  | Some index ->
    let width =
      match ledger with
      | [] -> List.length commitment
      | first :: _ -> List.length first
    in
    if not (ct_bignum_same_width ledger width) then
      invalid_arg "Bignum Merkle commitments must all have the same width";
    let rec loop current level siblings directions =
      match level with
      | [] -> None
      | [rt] ->
        Some
          {
            Confidential_merkle.merkle_index = index;
            merkle_root = rt;
            merkle_siblings = List.rev siblings;
            merkle_directions = List.rev directions;
          }
      | _ ->
        let is_right = current mod 2 = 1 in
        let sibling =
          if is_right then List.nth level (current - 1)
          else if current + 1 < List.length level then List.nth level (current + 1)
          else ct_bignum_merkle_empty width
        in
        loop
          (current / 2)
          (ct_bignum_merkle_compress_level width level)
          (sibling :: siblings)
          (is_right :: directions)
    in
    loop index (List.map ct_bignum_merkle_leaf ledger) [] []

let rec ct_index_directions depth index =
  if depth <= 0 then []
  else (index mod 2 = 1) :: ct_index_directions (depth - 1) (index / 2)

let ct_bignum_merkle_membership_verify commitment proof =
  proof.Confidential_merkle.merkle_directions =
    ct_index_directions (List.length proof.Confidential_merkle.merkle_siblings)
      proof.Confidential_merkle.merkle_index &&
  match
    Confidential_merkle.hex_to_bytes proof.Confidential_merkle.merkle_root,
    ct_bignum_merkle_path_root
      commitment
      proof.Confidential_merkle.merkle_siblings
      proof.Confidential_merkle.merkle_directions
  with
  | Some _, Some root -> root = proof.Confidential_merkle.merkle_root
  | _ -> false

let compare_bigint_vec left right =
  let rec loop left right =
    match left, right with
    | [], [] -> 0
    | [], _ -> -1
    | _, [] -> 1
    | l :: ls, r :: rs ->
      let cmp = compare_bigint l r in
      if cmp <> 0 then cmp else loop ls rs
  in
  loop left right

let compare_accepted_root (left_digest, left_depth) (right_digest, right_depth) =
  let digest_cmp = String.compare left_digest right_digest in
  if digest_cmp <> 0 then digest_cmp else compare left_depth right_depth

let require_sorted_unique compare_value label values =
  let rec loop previous = function
    | [] -> ()
    | value :: rest ->
      (match previous with
       | Some prev when compare_value prev value >= 0 ->
         invalid_arg (label ^ " must be sorted with no duplicates")
       | _ -> loop (Some value) rest)
  in
  loop None values

let encode_accepted_root label (root, depth) =
  encode_digest (label ^ ".digest") root @ encode_i64_nonnegative (label ^ ".depth") depth

let encode_accepted_root_vec label roots =
  encode_i64_nonnegative (label ^ ".length") (List.length roots)
  @ List.concat
      (List.mapi
         (fun index root -> encode_accepted_root (Printf.sprintf "%s[%d]" label index) root)
         roots)

let encode_accepted_root_window_entry label (root, depth, valid_from_epoch, expires_at_epoch) =
  if expires_at_epoch <= valid_from_epoch then
    invalid_arg (label ^ ".expiresAtEpoch must be greater than validFromEpoch");
  encode_accepted_root (label ^ ".root") (root, depth)
  @ encode_i64_nonnegative (label ^ ".validFromEpoch") valid_from_epoch
  @ encode_i64_nonnegative (label ^ ".expiresAtEpoch") expires_at_epoch

let encode_accepted_root_window_entries label entries =
  encode_i64_nonnegative (label ^ ".length") (List.length entries)
  @ List.concat
      (List.mapi
         (fun index entry ->
            encode_accepted_root_window_entry (Printf.sprintf "%s[%d]" label index) entry)
         entries)

let require_accepted_root_set label roots =
  if roots = [] then invalid_arg (label ^ " must not be empty");
  List.iteri
    (fun index root -> ignore (encode_accepted_root (Printf.sprintf "%s[%d]" label index) root))
    roots;
  require_sorted_unique compare_accepted_root label roots

let require_accepted_root_window ledger_epoch label entries =
  if entries = [] then invalid_arg (label ^ " must not be empty");
  List.iteri
    (fun index entry ->
       ignore (encode_accepted_root_window_entry (Printf.sprintf "%s[%d]" label index) entry))
    entries;
  List.iteri
    (fun index (_root, _depth, valid_from_epoch, expires_at_epoch) ->
       if valid_from_epoch > ledger_epoch || ledger_epoch >= expires_at_epoch then
         invalid_arg (Printf.sprintf "%s[%d] is not live at ledgerEpoch" label index))
    entries;
  require_sorted_unique
    compare_accepted_root
    label
    (List.map (fun (root, depth, _valid_from, _expires_at) -> (root, depth)) entries)

let ct_bignum_transaction_tagged_preimage tag body =
  ascii_bytes ct_bignum_transaction_dst
  @ encode_i64_nonnegative "transaction tag" tag
  @ encode_printable_ascii "protocolId" ct_transaction_protocol_id
  @ body

let ct_bignum_transaction_context_preimage
    protocol_version
    network_id
    asset_id
    ledger_epoch
    root
    root_depth
    public_fee
    c_in1
    c_in2
    c_out1
    c_out2
    nf1
    nf2 =
  ascii_bytes ct_bignum_transaction_dst
  @ encode_i64_nonnegative "transaction tag" 0
  @ encode_printable_ascii "protocolId" ct_transaction_protocol_id
  @ encode_i64_nonnegative "protocolVersion" protocol_version
  @ encode_printable_ascii "networkId" network_id
  @ encode_i64_nonnegative "assetId" asset_id
  @ encode_i64_nonnegative "ledgerEpoch" ledger_epoch
  @ encode_accepted_root "root" (root, root_depth)
  @ encode_bigint_value public_fee
  @ encode_bigint_vec "cIn1" c_in1
  @ encode_bigint_vec "cIn2" c_in2
  @ encode_bigint_vec "cOut1" c_out1
  @ encode_bigint_vec "cOut2" c_out2
  @ encode_bigint_vec "nf1" nf1
  @ encode_bigint_vec "nf2" nf2

let ct_bignum_transaction_context_digest
    protocol_version network_id asset_id ledger_epoch root root_depth public_fee
    c_in1 c_in2 c_out1 c_out2 nf1 nf2 =
  digest_bytes
    (ct_bignum_transaction_context_preimage
       protocol_version network_id asset_id ledger_epoch root root_depth public_fee
       c_in1 c_in2 c_out1 c_out2 nf1 nf2)

let ct_bignum_accepted_root_window_digest
    protocol_version network_id asset_id ledger_epoch roots root_depths valid_from_epochs expires_at_epochs =
  if List.length roots <> List.length root_depths ||
     List.length roots <> List.length valid_from_epochs ||
     List.length roots <> List.length expires_at_epochs
  then invalid_arg "acceptedRootWindow.roots vectors must have the same length";
  let entries = List.map2
      (fun root (depth, valid_from, expires_at) -> (root, depth, valid_from, expires_at))
      roots
      (List.map2
         (fun depth (valid_from, expires_at) -> (depth, valid_from, expires_at))
         root_depths
         (List.combine valid_from_epochs expires_at_epochs))
  in
  require_accepted_root_window ledger_epoch "acceptedRootWindow.roots" entries;
  digest_bytes
    (ct_bignum_transaction_tagged_preimage
       4
       (encode_i64_nonnegative "acceptedRootWindow.protocolVersion" protocol_version
        @ encode_printable_ascii "acceptedRootWindow.networkId" network_id
        @ encode_i64_nonnegative "acceptedRootWindow.assetId" asset_id
        @ encode_i64_nonnegative "acceptedRootWindow.ledgerEpoch" ledger_epoch
        @ encode_accepted_root_window_entries "acceptedRootWindow.roots" entries))

let ct_bignum_merkle_membership_preimage label proof =
  if List.length proof.Confidential_merkle.merkle_siblings <>
     List.length proof.Confidential_merkle.merkle_directions
  then invalid_arg (label ^ ".siblings and directions must have the same length");
  encode_i64_nonnegative (label ^ ".index") proof.Confidential_merkle.merkle_index
  @ encode_digest (label ^ ".root") proof.Confidential_merkle.merkle_root
  @ encode_digest_vec (label ^ ".siblings") proof.Confidential_merkle.merkle_siblings
  @ encode_bool_vec (label ^ ".directions") proof.Confidential_merkle.merkle_directions

type ct_bignum_nullifier_proof = {
  bignum_nf_a_commits : cli_bigint list list;
  bignum_nf_a_nullifiers : cli_bigint list list;
  bignum_nf_z_msgs : cli_bigint list list;
  bignum_nf_z_rands : cli_bigint list list;
}

type ct_bignum_balance_proof = {
  bignum_balance_as : cli_bigint list list;
  bignum_balance_zs : cli_bigint list list;
}

type ct_bignum_range_proof = {
  bignum_range_bits : cli_bigint list list;
  bignum_range_comps : cli_bigint list list;
  bignum_range_amount_as : cli_bigint list list;
  bignum_range_amount_zs : cli_bigint list list;
  bignum_range_pair_ass : cli_bigint list list list;
  bignum_range_pair_zss : cli_bigint list list list;
}

type ct_bignum_merkle_transaction_proof = {
  bignum_in1_member : Confidential_merkle.membership_proof;
  bignum_in2_member : Confidential_merkle.membership_proof;
  bignum_in1_nullifier : ct_bignum_nullifier_proof;
  bignum_in2_nullifier : ct_bignum_nullifier_proof;
  bignum_balance : ct_bignum_balance_proof;
  bignum_out1_range : ct_bignum_range_proof;
  bignum_out2_range : ct_bignum_range_proof;
}

let ct_bignum_nullifier_proof_preimage label proof =
  encode_bigint_mat (label ^ ".aCommits") proof.bignum_nf_a_commits
  @ encode_bigint_mat (label ^ ".aNullifiers") proof.bignum_nf_a_nullifiers
  @ encode_bigint_mat (label ^ ".zMsgs") proof.bignum_nf_z_msgs
  @ encode_bigint_mat (label ^ ".zRands") proof.bignum_nf_z_rands

let ct_bignum_balance_proof_preimage label proof =
  encode_bigint_mat (label ^ ".as") proof.bignum_balance_as
  @ encode_bigint_mat (label ^ ".zs") proof.bignum_balance_zs

let ct_bignum_range_proof_preimage label proof =
  encode_bigint_mat (label ^ ".bits") proof.bignum_range_bits
  @ encode_bigint_mat (label ^ ".comps") proof.bignum_range_comps
  @ encode_bigint_mat (label ^ ".amountAs") proof.bignum_range_amount_as
  @ encode_bigint_mat (label ^ ".amountZs") proof.bignum_range_amount_zs
  @ encode_bigint_cube (label ^ ".pairAss") proof.bignum_range_pair_ass
  @ encode_bigint_cube (label ^ ".pairZss") proof.bignum_range_pair_zss

let ct_bignum_merkle_proof_preimage proof =
  ct_bignum_transaction_tagged_preimage
    1
    (ct_bignum_merkle_membership_preimage "in1Member" proof.bignum_in1_member
     @ ct_bignum_merkle_membership_preimage "in2Member" proof.bignum_in2_member
     @ ct_bignum_nullifier_proof_preimage "in1Nullifier" proof.bignum_in1_nullifier
     @ ct_bignum_nullifier_proof_preimage "in2Nullifier" proof.bignum_in2_nullifier
     @ ct_bignum_balance_proof_preimage "balance" proof.bignum_balance
     @ ct_bignum_range_proof_preimage "out1Range" proof.bignum_out1_range
     @ ct_bignum_range_proof_preimage "out2Range" proof.bignum_out2_range)

let ct_bignum_merkle_proof_digest proof =
  digest_bytes (ct_bignum_merkle_proof_preimage proof)

let ct_bignum_envelope_digest
    context_digest protocol_version network_id asset_id ledger_epoch root root_depth public_fee
    c_in1 c_in2 c_out1 c_out2 nf1 nf2 proof =
  let computed_context_digest =
    ct_bignum_transaction_context_digest
      protocol_version network_id asset_id ledger_epoch root root_depth public_fee
      c_in1 c_in2 c_out1 c_out2 nf1 nf2
  in
  if context_digest <> computed_context_digest then
    invalid_arg "contextDigest does not match canonical bignum transaction context";
  digest_bytes
    (ct_bignum_transaction_tagged_preimage
       2
       (encode_digest "contextDigest" computed_context_digest
        @ encode_digest "proofDigest" (ct_bignum_merkle_proof_digest proof)))

let ct_bignum_wallet_proof_request_digest
    protocol_version network_id asset_id ledger_epoch root root_depth public_fee
    c_in1 c_in2 c_out1 c_out2 nf1 nf2 accepted_roots accepted_root_depths spent_nullifiers =
  if List.length accepted_roots <> List.length accepted_root_depths then
    invalid_arg "acceptedRoots and acceptedRootDepths must have the same length";
  let accepted_root_pairs = List.combine accepted_roots accepted_root_depths in
  require_accepted_root_set "acceptedRoots" accepted_root_pairs;
  require_sorted_unique compare_bigint_vec "spentNullifiers" spent_nullifiers;
  let context_digest =
    ct_bignum_transaction_context_digest
      protocol_version network_id asset_id ledger_epoch root root_depth public_fee
      c_in1 c_in2 c_out1 c_out2 nf1 nf2
  in
  begin
    if not (List.mem (root, root_depth) accepted_root_pairs) then
      invalid_arg "context.root must be inside acceptedRoots";
    if nf1 = nf2 then invalid_arg "context nullifiers must be distinct";
    if List.mem nf1 spent_nullifiers || List.mem nf2 spent_nullifiers then
      invalid_arg "context nullifiers must be absent from spentNullifiers";
    digest_bytes
      (ct_bignum_transaction_tagged_preimage
         3
         (encode_digest "contextDigest" context_digest
          @ encode_accepted_root_vec "acceptedRoots" accepted_root_pairs
          @ encode_bigint_mat "spentNullifiers" spent_nullifiers))
  end

let json_of_cb_params params =
  Printf.sprintf
    "{\"n1\":%d,\"n2\":%d,\"m\":%d,\"q\":%d,\"beta\":%d}"
    params.Commit_sis.cp_n1
    params.Commit_sis.cp_n2
    params.Commit_sis.cp_m
    params.Commit_sis.cp_q
    params.Commit_sis.cp_beta

let json_of_opening opening =
  Printf.sprintf
    "{\"msg\":%s,\"rand\":%s}"
    (json_of_vec opening.Commit_sis.open_msg)
    (json_of_vec opening.Commit_sis.open_rand)

let json_of_openings openings =
  "[" ^ String.concat "," (List.map json_of_opening openings) ^ "]"

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

let parse_ct_merkle_membership_proof index_str root siblings_str directions_str =
  match parse_canonical_int index_str, parse_string_list siblings_str, parse_canonical_bool_vec01 directions_str with
  | Some index, Some siblings, Some directions ->
    Some (Confidential_transaction.make_merkle_membership_proof index root siblings directions)
  | _ -> None

let ct_merkle_proof_digest_usage =
  "Usage: ct-merkle-proof-digest IN1_INDEX IN1_ROOT IN1_SIBLINGS IN1_DIRECTIONS IN2_INDEX IN2_ROOT IN2_SIBLINGS IN2_DIRECTIONS IN1_A_COMMITS IN1_A_NULLIFIERS IN1_Z_MSGS IN1_Z_RANDS IN2_A_COMMITS IN2_A_NULLIFIERS IN2_Z_MSGS IN2_Z_RANDS BAL_AS BAL_ZS OUT1_BITS OUT1_COMPS OUT1_AMOUNT_AS OUT1_AMOUNT_ZS OUT1_PAIR_ASS OUT1_PAIR_ZSS OUT2_BITS OUT2_COMPS OUT2_AMOUNT_AS OUT2_AMOUNT_ZS OUT2_PAIR_ASS OUT2_PAIR_ZSS"

let ct_merkle_proof_args_usage =
  String.sub ct_merkle_proof_digest_usage 29 (String.length ct_merkle_proof_digest_usage - 29)

let parse_ct_merkle_proof_digest_args args =
  match args with
  | [in1_index_str; in1_root; in1_siblings_str; in1_directions_str;
     in2_index_str; in2_root; in2_siblings_str; in2_directions_str;
     in1_a_commits_str; in1_a_nullifiers_str; in1_z_msgs_str; in1_z_rands_str;
     in2_a_commits_str; in2_a_nullifiers_str; in2_z_msgs_str; in2_z_rands_str;
     balance_as_str; balance_zs_str;
     out1_bits_str; out1_comps_str; out1_amount_a_str; out1_amount_z_str;
     out1_pair_as_str; out1_pair_zs_str;
     out2_bits_str; out2_comps_str; out2_amount_a_str; out2_amount_z_str;
     out2_pair_as_str; out2_pair_zs_str] ->
    (match
       parse_ct_merkle_membership_proof in1_index_str in1_root in1_siblings_str in1_directions_str,
       parse_ct_merkle_membership_proof in2_index_str in2_root in2_siblings_str in2_directions_str,
       parse_canonical_mat in1_a_commits_str,
       parse_canonical_mat in1_a_nullifiers_str,
       parse_canonical_mat in1_z_msgs_str,
       parse_canonical_mat in1_z_rands_str,
       parse_canonical_mat in2_a_commits_str,
       parse_canonical_mat in2_a_nullifiers_str,
       parse_canonical_mat in2_z_msgs_str,
       parse_canonical_mat in2_z_rands_str,
       parse_canonical_mat balance_as_str,
       parse_canonical_mat balance_zs_str,
       parse_canonical_mat out1_bits_str,
       parse_canonical_mat out1_comps_str,
       parse_canonical_mat out1_amount_a_str,
       parse_canonical_mat out1_amount_z_str,
       parse_canonical_cube out1_pair_as_str,
       parse_canonical_cube out1_pair_zs_str,
       parse_canonical_mat out2_bits_str,
       parse_canonical_mat out2_comps_str,
       parse_canonical_mat out2_amount_a_str,
       parse_canonical_mat out2_amount_z_str,
       parse_canonical_cube out2_pair_as_str,
       parse_canonical_cube out2_pair_zs_str
     with
     | Some in1_member, Some in2_member,
       Some in1_a_commits, Some in1_a_nullifiers, Some in1_z_msgs, Some in1_z_rands,
       Some in2_a_commits, Some in2_a_nullifiers, Some in2_z_msgs, Some in2_z_rands,
       Some balance_as, Some balance_zs,
       Some out1_bits, Some out1_comps, Some out1_amount_a, Some out1_amount_z,
       Some out1_pair_as, Some out1_pair_zs,
       Some out2_bits, Some out2_comps, Some out2_amount_a, Some out2_amount_z,
       Some out2_pair_as, Some out2_pair_zs ->
       Ok
         (Confidential_transaction.make_merkle_transaction_proof
            in1_member
            in2_member
            (Confidential_transaction.make_nullifier_proof in1_a_commits in1_a_nullifiers in1_z_msgs in1_z_rands)
            (Confidential_transaction.make_nullifier_proof in2_a_commits in2_a_nullifiers in2_z_msgs in2_z_rands)
            (Confidential_balance.make_balance_proof balance_as balance_zs)
            (Confidential_range.make_range_proof out1_bits out1_comps out1_amount_a out1_amount_z out1_pair_as out1_pair_zs)
            (Confidential_range.make_range_proof out2_bits out2_comps out2_amount_a out2_amount_z out2_pair_as out2_pair_zs))
     | _ -> Error "Expected Merkle membership and transaction-proof fields")
  | _ -> Error ct_merkle_proof_digest_usage

let ct_bignum_merkle_proof_digest_usage =
  "Usage: ct-bignum-merkle-proof-digest IN1_INDEX IN1_ROOT IN1_SIBLINGS IN1_DIRECTIONS IN2_INDEX IN2_ROOT IN2_SIBLINGS IN2_DIRECTIONS IN1_A_COMMITS IN1_A_NULLIFIERS IN1_Z_MSGS IN1_Z_RANDS IN2_A_COMMITS IN2_A_NULLIFIERS IN2_Z_MSGS IN2_Z_RANDS BAL_AS BAL_ZS OUT1_BITS OUT1_COMPS OUT1_AMOUNT_AS OUT1_AMOUNT_ZS OUT1_PAIR_ASS OUT1_PAIR_ZSS OUT2_BITS OUT2_COMPS OUT2_AMOUNT_AS OUT2_AMOUNT_ZS OUT2_PAIR_ASS OUT2_PAIR_ZSS"

let ct_bignum_merkle_proof_args_usage =
  String.sub
    ct_bignum_merkle_proof_digest_usage
    (String.length "Usage: ct-bignum-merkle-proof-digest ")
    (String.length ct_bignum_merkle_proof_digest_usage
     - String.length "Usage: ct-bignum-merkle-proof-digest ")

let parse_ct_bignum_merkle_proof_digest_args args =
  match args with
  | [in1_index_str; in1_root; in1_siblings_str; in1_directions_str;
     in2_index_str; in2_root; in2_siblings_str; in2_directions_str;
     in1_a_commits_str; in1_a_nullifiers_str; in1_z_msgs_str; in1_z_rands_str;
     in2_a_commits_str; in2_a_nullifiers_str; in2_z_msgs_str; in2_z_rands_str;
     balance_as_str; balance_zs_str;
     out1_bits_str; out1_comps_str; out1_amount_a_str; out1_amount_z_str;
     out1_pair_as_str; out1_pair_zs_str;
     out2_bits_str; out2_comps_str; out2_amount_a_str; out2_amount_z_str;
     out2_pair_as_str; out2_pair_zs_str] ->
    (match
       parse_ct_merkle_membership_proof in1_index_str in1_root in1_siblings_str in1_directions_str,
       parse_ct_merkle_membership_proof in2_index_str in2_root in2_siblings_str in2_directions_str,
       parse_canonical_bigint_mat in1_a_commits_str,
       parse_canonical_bigint_mat in1_a_nullifiers_str,
       parse_canonical_bigint_mat in1_z_msgs_str,
       parse_canonical_bigint_mat in1_z_rands_str,
       parse_canonical_bigint_mat in2_a_commits_str,
       parse_canonical_bigint_mat in2_a_nullifiers_str,
       parse_canonical_bigint_mat in2_z_msgs_str,
       parse_canonical_bigint_mat in2_z_rands_str,
       parse_canonical_bigint_mat balance_as_str,
       parse_canonical_bigint_mat balance_zs_str,
       parse_canonical_bigint_mat out1_bits_str,
       parse_canonical_bigint_mat out1_comps_str,
       parse_canonical_bigint_mat out1_amount_a_str,
       parse_canonical_bigint_mat out1_amount_z_str,
       parse_canonical_bigint_cube out1_pair_as_str,
       parse_canonical_bigint_cube out1_pair_zs_str,
       parse_canonical_bigint_mat out2_bits_str,
       parse_canonical_bigint_mat out2_comps_str,
       parse_canonical_bigint_mat out2_amount_a_str,
       parse_canonical_bigint_mat out2_amount_z_str,
       parse_canonical_bigint_cube out2_pair_as_str,
       parse_canonical_bigint_cube out2_pair_zs_str
     with
     | Some in1_member, Some in2_member,
       Some in1_a_commits, Some in1_a_nullifiers, Some in1_z_msgs, Some in1_z_rands,
       Some in2_a_commits, Some in2_a_nullifiers, Some in2_z_msgs, Some in2_z_rands,
       Some balance_as, Some balance_zs,
       Some out1_bits, Some out1_comps, Some out1_amount_a, Some out1_amount_z,
       Some out1_pair_as, Some out1_pair_zs,
       Some out2_bits, Some out2_comps, Some out2_amount_a, Some out2_amount_z,
       Some out2_pair_as, Some out2_pair_zs ->
       Ok
         {
           bignum_in1_member = in1_member;
           bignum_in2_member = in2_member;
           bignum_in1_nullifier =
             {
               bignum_nf_a_commits = in1_a_commits;
               bignum_nf_a_nullifiers = in1_a_nullifiers;
               bignum_nf_z_msgs = in1_z_msgs;
               bignum_nf_z_rands = in1_z_rands;
             };
           bignum_in2_nullifier =
             {
               bignum_nf_a_commits = in2_a_commits;
               bignum_nf_a_nullifiers = in2_a_nullifiers;
               bignum_nf_z_msgs = in2_z_msgs;
               bignum_nf_z_rands = in2_z_rands;
             };
           bignum_balance =
             {
               bignum_balance_as = balance_as;
               bignum_balance_zs = balance_zs;
             };
           bignum_out1_range =
             {
               bignum_range_bits = out1_bits;
               bignum_range_comps = out1_comps;
               bignum_range_amount_as = out1_amount_a;
               bignum_range_amount_zs = out1_amount_z;
               bignum_range_pair_ass = out1_pair_as;
               bignum_range_pair_zss = out1_pair_zs;
             };
           bignum_out2_range =
             {
               bignum_range_bits = out2_bits;
               bignum_range_comps = out2_comps;
               bignum_range_amount_as = out2_amount_a;
               bignum_range_amount_zs = out2_amount_z;
               bignum_range_pair_ass = out2_pair_as;
               bignum_range_pair_zss = out2_pair_zs;
             };
         }
     | _ -> Error "Expected bignum Merkle membership and transaction-proof fields")
  | _ -> Error ct_bignum_merkle_proof_digest_usage

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

let scaffold_compat_enabled () =
  match Sys.getenv_opt "ISABELLA_ENABLE_SCAFFOLD_COMPAT" with
  | Some "1" | Some "true" -> true
  | _ -> false

let require_scaffold_compat action =
  if scaffold_compat_enabled () then action ()
  else
    output_error
      "Scaffold compatibility commands require ISABELLA_ENABLE_SCAFFOLD_COMPAT=1 and are excluded from launch builds"

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

let make_canonical_cb_params m_str n2_str q_str beta_str =
  match
    parse_canonical_int m_str,
    parse_canonical_int n2_str,
    parse_canonical_int q_str,
    parse_canonical_int beta_str
  with
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

let output_sample f =
  try f ()
  with
  | Invalid_argument msg -> output_error msg
  | Sys_error msg -> output_error msg

let cmd_ct_sample_opening args =
  match args with
  | [msg_len_str; rand_len_str; bound_str] ->
    (match parse_int msg_len_str, parse_int rand_len_str, parse_int bound_str with
     | Some msg_len, Some rand_len, Some bound ->
       output_sample (fun () ->
         let result = Confidential_sampling.opening msg_len rand_len bound in
         (match !output_format with
          | Human -> Printf.printf "sample_opening = %s\n" (json_of_opening result)
          | Json -> Printf.printf "{\"result\":%s}\n" (json_of_opening result)))
     | _ -> output_error "Expected message length, randomness length, and bound")
  | _ -> output_error "Usage: ct-sample-opening MSG_LEN RAND_LEN BOUND"

let cmd_ct_sample_openings args =
  match args with
  | [count_str; msg_len_str; rand_len_str; bound_str] ->
    (match parse_int count_str, parse_int msg_len_str, parse_int rand_len_str, parse_int bound_str with
     | Some count, Some msg_len, Some rand_len, Some bound ->
       output_sample (fun () ->
         let result = Confidential_sampling.openings count msg_len rand_len bound in
         (match !output_format with
          | Human -> Printf.printf "sample_openings = %s\n" (json_of_openings result)
          | Json -> Printf.printf "{\"result\":%s}\n" (json_of_openings result)))
     | _ -> output_error "Expected count, message length, randomness length, and bound")
  | _ -> output_error "Usage: ct-sample-openings COUNT MSG_LEN RAND_LEN BOUND"

let cmd_cb_sample_mask args =
  match args with
  | [m_str; n2_str; q_str; beta_str; gamma_str] ->
    (match make_cb_params m_str n2_str q_str beta_str, parse_int gamma_str with
     | Some params, Some gamma ->
       output_sample (fun () ->
         let result = Confidential_balance.sample_mask params gamma in
         (match !output_format with
          | Human -> Printf.printf "sample_balance_mask = %s\n" (string_of_vec result)
          | Json -> Printf.printf "{\"result\":%s}\n" (json_of_vec result)))
     | _ -> output_error "Expected params (M N2 Q BETA) and gamma")
  | _ -> output_error "Usage: cb-sample-mask M N2 Q BETA GAMMA"

let cmd_cb_sample_masks args =
  match args with
  | [m_str; n2_str; q_str; beta_str; gamma_str; rounds_str] ->
    (match make_cb_params m_str n2_str q_str beta_str, parse_int gamma_str, parse_int rounds_str with
     | Some params, Some gamma, Some rounds ->
       output_sample (fun () ->
         let result = Confidential_balance.sample_masks params gamma rounds in
         (match !output_format with
          | Human -> Printf.printf "sample_balance_masks = %s\n" (string_of_mat result)
          | Json -> Printf.printf "{\"result\":%s}\n" (json_of_mat result)))
     | _ -> output_error "Expected params (M N2 Q BETA), gamma, and rounds")
  | _ -> output_error "Usage: cb-sample-masks M N2 Q BETA GAMMA ROUNDS"

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

let cmd_ct_balance_bigint_rand_commit args =
  match args with
  | [m_str; n2_str; q_str; beta_str; ck_str; r_str] ->
    (match
       make_big_cb_params m_str n2_str q_str beta_str,
       parse_canonical_bigint_mat ck_str,
       parse_canonical_bigint_vec r_str
     with
     | Some params, Some ck, Some r
       when valid_big_commit_key params ck && valid_big_vec params.big_cb_n2 r ->
         let result = big_rand_commit params ck r in
         (match !output_format with
          | Human -> Printf.printf "ct_balance_bigint_rand_commit = %s\n" (bigint_vec_text result)
          | Json -> Printf.printf "{\"result\":%s}\n" (json_of_bigint_vec result))
     | _ -> output_error "Expected params (M N2 Q BETA), BigInt commitment key matrix, and witness vector")
  | _ -> output_error "Usage: ct-balance-bigint-rand-commit M N2 Q BETA \"[[row1],[row2]]\" \"[r]\""

let cmd_ct_balance_bigint_fs_fields args =
  match args with
  | [ck_str; c_str; as_str] ->
    (match
       parse_canonical_bigint_mat ck_str,
       parse_canonical_bigint_vec c_str,
       parse_canonical_bigint_mat as_str
     with
     | Some ck, Some c, Some as_ ->
         let result = big_fs_fields ck c as_ in
         (match !output_format with
          | Human -> Printf.printf "ct_balance_bigint_fs_fields = %s\n" (bigint_vec_text result)
          | Json -> Printf.printf "{\"result\":%s}\n" (json_of_bigint_vec result))
     | _ -> output_error "Expected BigInt commitment key matrix, commitment vector, and announcement matrix")
  | _ -> output_error "Usage: ct-balance-bigint-fs-fields \"[[ck]]\" \"[c]\" \"[[a1],[a2],...]\""

let cmd_ct_balance_bigint_fs_challenges args =
  match args with
  | [m_str; n2_str; q_str; beta_str; ck_str; c_str; as_str; rounds_str] ->
    (match
       make_big_cb_params m_str n2_str q_str beta_str,
       parse_canonical_bigint_mat ck_str,
       parse_canonical_bigint_vec c_str,
       parse_canonical_bigint_mat as_str,
       parse_canonical_int rounds_str
     with
     | Some params, Some ck, Some c, Some as_, Some rounds
       when valid_big_cb_params params &&
            valid_big_commit_key params ck &&
            valid_big_vec params.big_cb_m c &&
            rounds >= 0 ->
         let result = big_fs_challenges ck c as_ rounds in
         output_result "ct_balance_bigint_fs_challenges"
           ("[" ^ String.concat "," (List.map string_of_int result) ^ "]")
     | _ -> output_error "Expected params, BigInt commitment key matrix, commitment vector, announcement matrix, and round count")
  | _ -> output_error "Usage: ct-balance-bigint-fs-challenges M N2 Q BETA \"[[ck]]\" \"[c]\" \"[[a1],[a2],...]\" ROUNDS"

let cmd_ct_balance_bigint_prove args =
  match args with
  | [m_str; n2_str; q_str; beta_str; gamma_str; ck_str; c_str; r_str; ys_str] ->
    (match
       make_big_cb_params m_str n2_str q_str beta_str,
       parse_canonical_bigint gamma_str,
       parse_canonical_bigint_mat ck_str,
       parse_canonical_bigint_vec c_str,
       parse_canonical_bigint_vec r_str,
       parse_canonical_bigint_mat ys_str
     with
     | Some params, Some gamma, Some ck, Some c, Some r, Some ys ->
         (match big_fs_prove params gamma ck c r ys with
          | Some (as_, zs) ->
              (match !output_format with
               | Human -> Printf.printf "ct_balance_bigint_proof = %s\n" (json_of_bigint_balance_proof as_ zs)
               | Json -> Printf.printf "{\"result\":%s}\n" (json_of_bigint_balance_proof as_ zs))
          | None ->
              (match !output_format with
               | Human -> print_endline "ct_balance_bigint_proof = null"
               | Json -> print_endline "{\"result\":null}"))
     | _ -> output_error "Expected params, gamma, BigInt commitment key matrix, commitment vector, witness vector, and mask matrix")
  | _ -> output_error "Usage: ct-balance-bigint-prove M N2 Q BETA GAMMA \"[[ck]]\" \"[c]\" \"[r]\" \"[[y1],[y2],...]\""

let cmd_ct_balance_bigint_verify args =
  match args with
  | [m_str; n2_str; q_str; beta_str; gamma_str; ck_str; c_str; as_str; zs_str] ->
    (match
       make_big_cb_params m_str n2_str q_str beta_str,
       parse_canonical_bigint gamma_str,
       parse_canonical_bigint_mat ck_str,
       parse_canonical_bigint_vec c_str,
       parse_canonical_bigint_mat as_str,
       parse_canonical_bigint_mat zs_str
     with
     | Some params, Some gamma, Some ck, Some c, Some as_, Some zs ->
         let result = big_fs_verify params gamma ck c as_ zs in
         output_result "ct_balance_bigint_verify" (if result then "true" else "false")
     | _ -> output_error "Expected params, gamma, BigInt commitment key matrix, commitment vector, announcement matrix, and response matrix")
  | _ -> output_error "Usage: ct-balance-bigint-verify M N2 Q BETA GAMMA \"[[ck]]\" \"[c]\" \"[[a1],[a2],...]\" \"[[z1],[z2],...]\""

let rec make_big_scalar_openings values rands =
  match values, rands with
  | [], [] -> Some []
  | value :: rest_values, rand :: rest_rands ->
      Option.map (fun rest -> big_opening [value] rand :: rest)
        (make_big_scalar_openings rest_values rest_rands)
  | _ -> None

let cmd_ct_range_bigint_fs_fields args =
  match args with
  | [ck_str; c_amount_str; bits_str; comps_str; amount_as_str; pair_ass_str] ->
    (match
       parse_canonical_bigint_mat ck_str,
       parse_canonical_bigint_vec c_amount_str,
       parse_canonical_bigint_mat bits_str,
       parse_canonical_bigint_mat comps_str,
       parse_canonical_bigint_mat amount_as_str,
       parse_canonical_bigint_cube pair_ass_str
     with
     | Some ck, Some c_amount, Some bits, Some comps, Some amount_as, Some pair_ass ->
         let result = big_cr_fs_fields ck c_amount bits comps amount_as pair_ass in
         (match !output_format with
          | Human -> Printf.printf "ct_range_bigint_fs_fields = %s\n" (bigint_vec_text result)
          | Json -> Printf.printf "{\"result\":%s}\n" (json_of_bigint_vec result))
     | _ -> output_error "Expected BigInt commitment key, amount commitment, bit commitments, complement commitments, amount announcements, and pair announcements")
  | _ -> output_error "Usage: ct-range-bigint-fs-fields \"[[ck]]\" \"[cAmount]\" \"[[bits]]\" \"[[comps]]\" \"[[amountAs]]\" \"[[[pairAss]]]\""

let cmd_ct_range_bigint_fs_challenges args =
  match args with
  | [m_str; n2_str; q_str; beta_str; ck_str; c_amount_str; bits_str; comps_str; amount_as_str; pair_ass_str; rounds_str] ->
    (match
       make_big_cb_params m_str n2_str q_str beta_str,
       parse_canonical_bigint_mat ck_str,
       parse_canonical_bigint_vec c_amount_str,
       parse_canonical_bigint_mat bits_str,
       parse_canonical_bigint_mat comps_str,
       parse_canonical_bigint_mat amount_as_str,
       parse_canonical_bigint_cube pair_ass_str,
       parse_canonical_int rounds_str
     with
     | Some params, Some ck, Some c_amount, Some bits, Some comps, Some amount_as, Some pair_ass, Some rounds
       when valid_big_cb_params params &&
            valid_big_commit_key params ck &&
            valid_big_vec params.big_cb_m c_amount &&
            rounds >= 0 ->
         let result = big_cr_fs_challenges ck c_amount bits comps amount_as pair_ass rounds in
         output_result "ct_range_bigint_fs_challenges"
           ("[" ^ String.concat "," (List.map string_of_int result) ^ "]")
     | _ -> output_error "Expected params, BigInt range transcript fields, and round count")
  | _ -> output_error "Usage: ct-range-bigint-fs-challenges M N2 Q BETA \"[[ck]]\" \"[cAmount]\" \"[[bits]]\" \"[[comps]]\" \"[[amountAs]]\" \"[[[pairAss]]]\" ROUNDS"

let cmd_ct_range_bigint_prove args =
  match args with
  | [m_str; n2_str; q_str; beta_str; gamma_str; k_str; ck_str; c_amount_str; amount_str; amount_rand_str; bits_str; bit_rands_str; comps_str; comp_rands_str; y_amounts_str; y_pairss_str] ->
    (match
       make_big_cb_params m_str n2_str q_str beta_str,
       parse_canonical_bigint gamma_str,
       parse_canonical_int k_str,
       parse_canonical_bigint_mat ck_str,
       parse_canonical_bigint_vec c_amount_str,
       parse_canonical_bigint amount_str,
       parse_canonical_bigint_vec amount_rand_str,
       parse_canonical_bigint_vec bits_str,
       parse_canonical_bigint_mat bit_rands_str,
       parse_canonical_bigint_vec comps_str,
       parse_canonical_bigint_mat comp_rands_str,
       parse_canonical_bigint_mat y_amounts_str,
       parse_canonical_bigint_cube y_pairss_str
     with
     | Some params, Some gamma, Some k, Some ck, Some c_amount, Some amount, Some amount_rand, Some bits, Some bit_rands, Some comps, Some comp_rands, Some y_amounts, Some y_pairss ->
       (match make_big_scalar_openings bits bit_rands, make_big_scalar_openings comps comp_rands with
        | Some bit_openings, Some comp_openings ->
          (match big_cr_fs_prove params gamma k ck c_amount (big_opening [amount] amount_rand) bit_openings comp_openings y_amounts y_pairss with
           | Some (bits, comps, amount_as, amount_zs, pair_ass, pair_zss) ->
             (match !output_format with
              | Human ->
                Printf.printf
                  "ct_range_bigint_proof = %s\n"
                  (json_of_bigint_range_proof bits comps amount_as amount_zs pair_ass pair_zss)
              | Json ->
                Printf.printf
                  "{\"result\":%s}\n"
                  (json_of_bigint_range_proof bits comps amount_as amount_zs pair_ass pair_zss))
           | None ->
             (match !output_format with
              | Human -> print_endline "ct_range_bigint_proof = null"
              | Json -> print_endline "{\"result\":null}"))
        | _ -> output_error "Bit/complement counts must match their randomness matrices")
     | _ -> output_error "Expected params, gamma, BigInt commitment key, amount opening, bit openings, complement openings, and masks")
  | _ -> output_error "Usage: ct-range-bigint-prove M N2 Q BETA GAMMA K \"[[ck]]\" \"[cAmount]\" AMOUNT \"[amountRand]\" \"[bits]\" \"[[bitRands]]\" \"[comps]\" \"[[compRands]]\" \"[[yAmounts]]\" \"[[[yPairss]]]\""

let cmd_ct_range_bigint_verify args =
  match args with
  | [m_str; n2_str; q_str; beta_str; gamma_str; k_str; ck_str; c_amount_str; bits_str; comps_str; amount_as_str; amount_zs_str; pair_ass_str; pair_zss_str] ->
    (match
       make_big_cb_params m_str n2_str q_str beta_str,
       parse_canonical_bigint gamma_str,
       parse_canonical_int k_str,
       parse_canonical_bigint_mat ck_str,
       parse_canonical_bigint_vec c_amount_str,
       parse_canonical_bigint_mat bits_str,
       parse_canonical_bigint_mat comps_str,
       parse_canonical_bigint_mat amount_as_str,
       parse_canonical_bigint_mat amount_zs_str,
       parse_canonical_bigint_cube pair_ass_str,
       parse_canonical_bigint_cube pair_zss_str
     with
     | Some params, Some gamma, Some k, Some ck, Some c_amount, Some bits, Some comps, Some amount_as, Some amount_zs, Some pair_ass, Some pair_zss ->
         let result = big_cr_fs_verify params gamma k ck c_amount bits comps amount_as amount_zs pair_ass pair_zss in
         output_result "ct_range_bigint_verify" (if result then "true" else "false")
     | _ -> output_error "Expected params, gamma, BigInt commitment key, amount commitment, and proof fields")
  | _ -> output_error "Usage: ct-range-bigint-verify M N2 Q BETA GAMMA K \"[[ck]]\" \"[cAmount]\" \"[[bits]]\" \"[[comps]]\" \"[[amountAs]]\" \"[[amountZs]]\" \"[[[pairAss]]]\" \"[[[pairZss]]]\""

let cmd_ct_nullifier_bigint args =
  match args with
  | [m_str; n2_str; q_str; beta_str; nk_str; amount_str; rand_str] ->
    (match
       make_big_cb_params m_str n2_str q_str beta_str,
       parse_canonical_bigint_mat nk_str,
       parse_canonical_bigint amount_str,
       parse_canonical_bigint_vec rand_str
     with
     | Some params, Some nk, Some amount, Some rand
       when valid_big_commit_key params nk && valid_big_opening params (big_opening [amount] rand) ->
         let result = big_commit params nk (big_opening [amount] rand) in
         (match !output_format with
          | Human -> Printf.printf "ct_nullifier_bigint = %s\n" (bigint_vec_text result)
          | Json -> Printf.printf "{\"result\":%s}\n" (json_of_bigint_vec result))
     | _ -> output_error "Expected params, BigInt nullifier key, scalar amount, and randomness vector")
  | _ -> output_error "Usage: ct-nullifier-bigint M N2 Q BETA \"[[nk]]\" AMOUNT \"[rand]\""

let cmd_ct_nullifier_bigint_fs_fields args =
  match args with
  | [ck_str; nk_str; c_str; nf_str; a_commits_str; a_nullifiers_str] ->
    (match
       parse_canonical_bigint_mat ck_str,
       parse_canonical_bigint_mat nk_str,
       parse_canonical_bigint_vec c_str,
       parse_canonical_bigint_vec nf_str,
       parse_canonical_bigint_mat a_commits_str,
       parse_canonical_bigint_mat a_nullifiers_str
     with
     | Some ck, Some nk, Some c, Some nf, Some a_commits, Some a_nullifiers ->
         let result = big_nf_fs_fields ck nk c nf a_commits a_nullifiers in
         (match !output_format with
          | Human -> Printf.printf "ct_nullifier_bigint_fs_fields = %s\n" (bigint_vec_text result)
          | Json -> Printf.printf "{\"result\":%s}\n" (json_of_bigint_vec result))
     | _ -> output_error "Expected BigInt keys, commitment, nullifier, commitment announcements, and nullifier announcements")
  | _ -> output_error "Usage: ct-nullifier-bigint-fs-fields \"[[ck]]\" \"[[nk]]\" \"[c]\" \"[nf]\" \"[[aCommits]]\" \"[[aNullifiers]]\""

let cmd_ct_nullifier_bigint_fs_challenges args =
  match args with
  | [m_str; n2_str; q_str; beta_str; ck_str; nk_str; c_str; nf_str; a_commits_str; a_nullifiers_str; rounds_str] ->
    (match
       make_big_cb_params m_str n2_str q_str beta_str,
       parse_canonical_bigint_mat ck_str,
       parse_canonical_bigint_mat nk_str,
       parse_canonical_bigint_vec c_str,
       parse_canonical_bigint_vec nf_str,
       parse_canonical_bigint_mat a_commits_str,
       parse_canonical_bigint_mat a_nullifiers_str,
       parse_canonical_int rounds_str
     with
     | Some params, Some ck, Some nk, Some c, Some nf, Some a_commits, Some a_nullifiers, Some rounds
       when valid_big_cb_params params &&
            valid_big_commit_key params ck &&
            valid_big_commit_key params nk &&
            valid_big_vec params.big_cb_m c &&
            valid_big_vec params.big_cb_m nf &&
            rounds >= 0 ->
         let result = big_nf_fs_challenges ck nk c nf a_commits a_nullifiers rounds in
         output_result "ct_nullifier_bigint_fs_challenges"
           ("[" ^ String.concat "," (List.map string_of_int result) ^ "]")
     | _ -> output_error "Expected params, BigInt nullifier transcript fields, and round count")
  | _ -> output_error "Usage: ct-nullifier-bigint-fs-challenges M N2 Q BETA \"[[ck]]\" \"[[nk]]\" \"[c]\" \"[nf]\" \"[[aCommits]]\" \"[[aNullifiers]]\" ROUNDS"

let cmd_ct_nullifier_bigint_prove args =
  match args with
  | [m_str; n2_str; q_str; beta_str; gamma_str; ck_str; nk_str; c_str; nf_str; amount_str; rand_str; y_msgs_str; y_rands_str] ->
    (match
       make_big_cb_params m_str n2_str q_str beta_str,
       parse_canonical_bigint gamma_str,
       parse_canonical_bigint_mat ck_str,
       parse_canonical_bigint_mat nk_str,
       parse_canonical_bigint_vec c_str,
       parse_canonical_bigint_vec nf_str,
       parse_canonical_bigint amount_str,
       parse_canonical_bigint_vec rand_str,
       parse_canonical_bigint_vec y_msgs_str,
       parse_canonical_bigint_mat y_rands_str
     with
     | Some params, Some gamma, Some ck, Some nk, Some c, Some nf, Some amount, Some rand, Some y_msgs, Some y_rands ->
       (match make_big_scalar_openings y_msgs y_rands with
        | Some masks ->
          (match big_nf_fs_prove params gamma ck nk c nf (big_opening [amount] rand) masks with
           | Some (a_commits, a_nullifiers, z_msgs, z_rands) ->
             (match !output_format with
              | Human ->
                Printf.printf
                  "ct_nullifier_bigint_proof = %s\n"
                  (json_of_bigint_nullifier_proof a_commits a_nullifiers z_msgs z_rands)
              | Json ->
                Printf.printf
                  "{\"result\":%s}\n"
                  (json_of_bigint_nullifier_proof a_commits a_nullifiers z_msgs z_rands))
           | None ->
             (match !output_format with
              | Human -> print_endline "ct_nullifier_bigint_proof = null"
              | Json -> print_endline "{\"result\":null}"))
        | _ -> output_error "Nullifier-mask counts must match their randomness matrices")
     | _ -> output_error "Expected params, gamma, BigInt keys, commitment, nullifier, opening, and masks")
  | _ -> output_error "Usage: ct-nullifier-bigint-prove M N2 Q BETA GAMMA \"[[ck]]\" \"[[nk]]\" \"[c]\" \"[nf]\" AMOUNT \"[rand]\" \"[yMsgs]\" \"[[yRands]]\""

let cmd_ct_nullifier_bigint_verify args =
  match args with
  | [m_str; n2_str; q_str; beta_str; gamma_str; ck_str; nk_str; c_str; nf_str; a_commits_str; a_nullifiers_str; z_msgs_str; z_rands_str] ->
    (match
       make_big_cb_params m_str n2_str q_str beta_str,
       parse_canonical_bigint gamma_str,
       parse_canonical_bigint_mat ck_str,
       parse_canonical_bigint_mat nk_str,
       parse_canonical_bigint_vec c_str,
       parse_canonical_bigint_vec nf_str,
       parse_canonical_bigint_mat a_commits_str,
       parse_canonical_bigint_mat a_nullifiers_str,
       parse_canonical_bigint_mat z_msgs_str,
       parse_canonical_bigint_mat z_rands_str
     with
     | Some params, Some gamma, Some ck, Some nk, Some c, Some nf, Some a_commits, Some a_nullifiers, Some z_msgs, Some z_rands ->
         let result = big_nf_fs_verify params gamma ck nk c nf a_commits a_nullifiers z_msgs z_rands in
         output_result "ct_nullifier_bigint_verify" (if result then "true" else "false")
     | _ -> output_error "Expected params, gamma, BigInt keys, commitment, nullifier, and proof fields")
  | _ -> output_error "Usage: ct-nullifier-bigint-verify M N2 Q BETA GAMMA \"[[ck]]\" \"[[nk]]\" \"[c]\" \"[nf]\" \"[[aCommits]]\" \"[[aNullifiers]]\" \"[[zMsgs]]\" \"[[zRands]]\""

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

let cmd_ct_bignum_encode args =
  match args with
  | [value] ->
    (try output_string_result "ct_bignum_encode" (hex_of_bytes (encode_bignum_decimal "value" value))
     with Invalid_argument msg -> output_error msg)
  | _ -> output_error "Usage: ct-bignum-encode INTEGER"

let cmd_ct_bignum_vector_encode args =
  try output_string_result "ct_bignum_vector_encode" (hex_of_bytes (encode_bignum_decimal_vec args))
  with Invalid_argument msg -> output_error msg

let cmd_ct_bignum_merkle_leaf args =
  match args with
  | [commitment_str] ->
    (match parse_canonical_bigint_vec commitment_str with
     | Some commitment ->
       (try output_string_result "ct_bignum_merkle_leaf" (ct_bignum_merkle_leaf commitment)
        with Invalid_argument msg -> output_error msg)
     | None -> output_error "Expected canonical bignum commitment vector")
  | _ -> output_error "Usage: ct-bignum-merkle-leaf \"[commitment]\""

let cmd_ct_bignum_merkle_empty args =
  match args with
  | [width_str] ->
    (match parse_canonical_int width_str with
     | Some width ->
       (try output_string_result "ct_bignum_merkle_empty" (ct_bignum_merkle_empty width)
        with Invalid_argument msg -> output_error msg)
     | None -> output_error "Expected non-negative width")
  | _ -> output_error "Usage: ct-bignum-merkle-empty WIDTH"

let cmd_ct_bignum_merkle_node args =
  match args with
  | [left; right] ->
    (try output_string_result "ct_bignum_merkle_node" (ct_bignum_merkle_node left right)
     with Invalid_argument msg -> output_error msg)
  | _ -> output_error "Usage: ct-bignum-merkle-node LEFT_DIGEST RIGHT_DIGEST"

let cmd_ct_bignum_merkle_root args =
  match args with
  | [ledger_str] ->
    (match parse_canonical_bigint_mat ledger_str with
     | Some ledger ->
       (try output_string_result "ct_bignum_merkle_root" (ct_bignum_merkle_root ledger)
        with Invalid_argument msg -> output_error msg)
     | None -> output_error "Expected canonical bignum ledger matrix")
  | _ -> output_error "Usage: ct-bignum-merkle-root \"[[commitment],...]\""

let cmd_ct_bignum_merkle_member_prove args =
  match args with
  | [ledger_str; commitment_str] ->
    (match parse_canonical_bigint_mat ledger_str, parse_canonical_bigint_vec commitment_str with
     | Some ledger, Some commitment ->
       (try
          match ct_bignum_merkle_membership_prove ledger commitment with
          | Some proof ->
            (match !output_format with
             | Human -> Printf.printf "ct_bignum_merkle_membership_proof = %s\n" (json_of_merkle_membership_proof proof)
             | Json -> Printf.printf "%s\n" (json_of_merkle_membership_proof proof))
          | None ->
            (match !output_format with
             | Human -> print_endline "ct_bignum_merkle_membership_proof = null"
             | Json -> print_endline "null")
        with Invalid_argument msg -> output_error msg)
     | _ -> output_error "Expected canonical bignum ledger matrix and commitment vector")
  | _ -> output_error "Usage: ct-bignum-merkle-member-prove \"[[commitment],...]\" \"[commitment]\""

let cmd_ct_bignum_merkle_member_verify args =
  match args with
  | [ledger_str; commitment_str] ->
    (match parse_canonical_bigint_mat ledger_str, parse_canonical_bigint_vec commitment_str with
     | Some ledger, Some commitment ->
       let result =
         try
           match ct_bignum_merkle_membership_prove ledger commitment with
           | Some proof -> ct_bignum_merkle_membership_verify commitment proof
           | None -> false
         with Invalid_argument _ -> false
       in
       output_result "ct_bignum_merkle_membership_verify" (if result then "true" else "false")
     | _ -> output_error "Expected canonical bignum ledger matrix and commitment vector")
  | _ -> output_error "Usage: ct-bignum-merkle-member-verify \"[[commitment],...]\" \"[commitment]\""

let cmd_ct_bignum_transaction_context args =
  match args with
  | [protocol_version_str; network_id; asset_id_str; ledger_epoch_str; root; root_depth_str;
     public_fee_str; c_in1_str; c_in2_str; c_out1_str; c_out2_str; nf1_str; nf2_str] ->
    (match
       parse_canonical_int protocol_version_str,
       parse_canonical_int asset_id_str,
       parse_canonical_int ledger_epoch_str,
       parse_canonical_int root_depth_str,
       parse_canonical_bigint public_fee_str,
       parse_canonical_bigint_vec c_in1_str,
       parse_canonical_bigint_vec c_in2_str,
       parse_canonical_bigint_vec c_out1_str,
       parse_canonical_bigint_vec c_out2_str,
       parse_canonical_bigint_vec nf1_str,
       parse_canonical_bigint_vec nf2_str
     with
     | Some protocol_version, Some asset_id, Some ledger_epoch, Some root_depth, Some public_fee,
       Some c_in1, Some c_in2, Some c_out1, Some c_out2, Some nf1, Some nf2 ->
       (try
          output_string_result "ct_bignum_transaction_context"
            (ct_bignum_transaction_context_digest
               protocol_version network_id asset_id ledger_epoch root root_depth public_fee
               c_in1 c_in2 c_out1 c_out2 nf1 nf2)
        with Invalid_argument msg -> output_error msg)
     | _ -> output_error "Expected bignum transaction context fields")
  | _ ->
    output_error "Usage: ct-bignum-transaction-context VERSION NETWORK_ID ASSET_ID LEDGER_EPOCH ROOT ROOT_DEPTH PUBLIC_FEE C_IN1 C_IN2 C_OUT1 C_OUT2 NF1 NF2"

let cmd_ct_bignum_merkle_proof_digest args =
  match parse_ct_bignum_merkle_proof_digest_args args with
  | Ok proof ->
    (try
       output_string_result "ct_bignum_merkle_proof_digest" (ct_bignum_merkle_proof_digest proof)
     with Invalid_argument msg -> output_error msg)
  | Error msg -> output_error msg

let cmd_ct_bignum_merkle_envelope_digest args =
  match args with
  | context_digest :: protocol_version_str :: network_id :: asset_id_str :: ledger_epoch_str ::
    root :: root_depth_str :: public_fee_str :: c_in1_str :: c_in2_str :: c_out1_str :: c_out2_str ::
    nf1_str :: nf2_str :: proof_args ->
    (match
       parse_canonical_int protocol_version_str,
       parse_canonical_int asset_id_str,
       parse_canonical_int ledger_epoch_str,
       parse_canonical_int root_depth_str,
       parse_canonical_bigint public_fee_str,
       parse_canonical_bigint_vec c_in1_str,
       parse_canonical_bigint_vec c_in2_str,
       parse_canonical_bigint_vec c_out1_str,
       parse_canonical_bigint_vec c_out2_str,
       parse_canonical_bigint_vec nf1_str,
       parse_canonical_bigint_vec nf2_str,
       parse_ct_bignum_merkle_proof_digest_args proof_args
     with
     | Some protocol_version, Some asset_id, Some ledger_epoch, Some root_depth, Some public_fee,
       Some c_in1, Some c_in2, Some c_out1, Some c_out2, Some nf1, Some nf2,
       Ok proof ->
       (try
          output_string_result "ct_bignum_merkle_envelope_digest"
            (ct_bignum_envelope_digest
               context_digest protocol_version network_id asset_id ledger_epoch root root_depth public_fee
               c_in1 c_in2 c_out1 c_out2 nf1 nf2 proof)
        with Invalid_argument msg -> output_error msg)
     | _ -> output_error "Expected context digest, bignum context fields, and bignum Merkle proof fields")
  | _ ->
    output_error ("Usage: ct-bignum-merkle-envelope-digest CONTEXT_DIGEST VERSION NETWORK_ID ASSET_ID LEDGER_EPOCH ROOT ROOT_DEPTH PUBLIC_FEE C_IN1 C_IN2 C_OUT1 C_OUT2 NF1 NF2 " ^ ct_bignum_merkle_proof_args_usage)

let cmd_ct_bignum_wallet_proof_request_digest args =
  match args with
  | [protocol_version_str; network_id; asset_id_str; ledger_epoch_str; root; root_depth_str;
     public_fee_str; c_in1_str; c_in2_str; c_out1_str; c_out2_str; nf1_str; nf2_str;
     accepted_roots_str; accepted_root_depths_str; spent_nullifiers_str] ->
    (match
       parse_canonical_int protocol_version_str,
       parse_canonical_int asset_id_str,
       parse_canonical_int ledger_epoch_str,
       parse_canonical_int root_depth_str,
       parse_canonical_bigint public_fee_str,
       parse_canonical_bigint_vec c_in1_str,
       parse_canonical_bigint_vec c_in2_str,
       parse_canonical_bigint_vec c_out1_str,
       parse_canonical_bigint_vec c_out2_str,
       parse_canonical_bigint_vec nf1_str,
       parse_canonical_bigint_vec nf2_str,
       parse_string_list accepted_roots_str,
       parse_canonical_vec accepted_root_depths_str,
       parse_canonical_bigint_mat spent_nullifiers_str
     with
     | Some protocol_version, Some asset_id, Some ledger_epoch, Some root_depth, Some public_fee,
       Some c_in1, Some c_in2, Some c_out1, Some c_out2, Some nf1, Some nf2,
       Some accepted_roots, Some accepted_root_depths, Some spent_nullifiers ->
       (try
          output_string_result "ct_bignum_wallet_proof_request_digest"
            (ct_bignum_wallet_proof_request_digest
               protocol_version network_id asset_id ledger_epoch root root_depth public_fee
               c_in1 c_in2 c_out1 c_out2 nf1 nf2 accepted_roots accepted_root_depths spent_nullifiers)
        with Invalid_argument msg -> output_error msg)
     | _ -> output_error "Expected bignum wallet proof request context, accepted roots, and spent nullifiers")
  | _ ->
    output_error "Usage: ct-bignum-wallet-proof-request-digest VERSION NETWORK_ID ASSET_ID LEDGER_EPOCH ROOT ROOT_DEPTH PUBLIC_FEE C_IN1 C_IN2 C_OUT1 C_OUT2 NF1 NF2 ACCEPTED_ROOTS ACCEPTED_ROOT_DEPTHS SPENT_NULLIFIERS"

let cmd_ct_bignum_accepted_root_window_digest args =
  match args with
  | [protocol_version_str; network_id; asset_id_str; ledger_epoch_str;
     roots_str; root_depths_str; valid_from_epochs_str; expires_at_epochs_str] ->
    (match
       parse_canonical_int protocol_version_str,
       parse_canonical_int asset_id_str,
       parse_canonical_int ledger_epoch_str,
       parse_string_list roots_str,
       parse_canonical_vec root_depths_str,
       parse_canonical_vec valid_from_epochs_str,
       parse_canonical_vec expires_at_epochs_str
     with
     | Some protocol_version, Some asset_id, Some ledger_epoch,
       Some roots, Some root_depths, Some valid_from_epochs, Some expires_at_epochs ->
       (try
          output_string_result "ct_bignum_accepted_root_window_digest"
            (ct_bignum_accepted_root_window_digest
               protocol_version network_id asset_id ledger_epoch roots root_depths valid_from_epochs expires_at_epochs)
        with Invalid_argument msg -> output_error msg)
     | _ -> output_error "Expected bignum accepted-root window fields")
  | _ ->
    output_error "Usage: ct-bignum-accepted-root-window-digest VERSION NETWORK_ID ASSET_ID LEDGER_EPOCH ROOTS ROOT_DEPTHS VALID_FROM_EPOCHS EXPIRES_AT_EPOCHS"

let cmd_ct_transaction_context args =
  match args with
  | [protocol_version_str; network_id; asset_id_str; ledger_epoch_str; root; root_depth_str;
     public_fee_str; c_in1_str; c_in2_str; c_out1_str; c_out2_str; nf1_str; nf2_str] ->
    (match
       parse_canonical_int protocol_version_str,
       parse_canonical_int asset_id_str,
       parse_canonical_int ledger_epoch_str,
       parse_canonical_int root_depth_str,
       parse_canonical_int public_fee_str,
       parse_canonical_vec c_in1_str,
       parse_canonical_vec c_in2_str,
       parse_canonical_vec c_out1_str,
       parse_canonical_vec c_out2_str,
       parse_canonical_vec nf1_str,
       parse_canonical_vec nf2_str
     with
     | Some protocol_version, Some asset_id, Some ledger_epoch, Some root_depth, Some public_fee,
       Some c_in1, Some c_in2, Some c_out1, Some c_out2, Some nf1, Some nf2 ->
       (try
          output_string_result "ct_transaction_context"
            (Confidential_transaction.transaction_context_digest
               protocol_version network_id asset_id ledger_epoch root root_depth public_fee
               c_in1 c_in2 c_out1 c_out2 nf1 nf2)
        with Invalid_argument msg -> output_error msg)
     | _ -> output_error "Expected transaction context fields")
  | _ ->
    output_error "Usage: ct-transaction-context VERSION NETWORK_ID ASSET_ID LEDGER_EPOCH ROOT ROOT_DEPTH PUBLIC_FEE C_IN1 C_IN2 C_OUT1 C_OUT2 NF1 NF2"

let cmd_ct_merkle_proof_digest args =
  match parse_ct_merkle_proof_digest_args args with
  | Ok proof ->
    (try
       output_string_result
         "ct_merkle_proof_digest"
         (Confidential_transaction.transaction_merkle_proof_digest proof)
     with Invalid_argument msg -> output_error msg)
  | Error msg -> output_error msg

let cmd_ct_merkle_envelope_digest args =
  match args with
  | context_digest :: protocol_version_str :: network_id :: asset_id_str :: ledger_epoch_str ::
    root :: root_depth_str :: public_fee_str :: c_in1_str :: c_in2_str :: c_out1_str :: c_out2_str ::
    nf1_str :: nf2_str :: proof_args ->
    (match
       parse_canonical_int protocol_version_str,
       parse_canonical_int asset_id_str,
       parse_canonical_int ledger_epoch_str,
       parse_canonical_int root_depth_str,
       parse_canonical_int public_fee_str,
       parse_canonical_vec c_in1_str,
       parse_canonical_vec c_in2_str,
       parse_canonical_vec c_out1_str,
       parse_canonical_vec c_out2_str,
       parse_canonical_vec nf1_str,
       parse_canonical_vec nf2_str,
       parse_ct_merkle_proof_digest_args proof_args
     with
     | Some protocol_version, Some asset_id, Some ledger_epoch, Some root_depth, Some public_fee,
       Some c_in1, Some c_in2, Some c_out1, Some c_out2, Some nf1, Some nf2,
       Ok proof ->
       (try
          output_string_result
            "ct_merkle_envelope_digest"
            (Confidential_transaction.transaction_envelope_digest
               context_digest protocol_version network_id asset_id ledger_epoch root root_depth public_fee
               c_in1 c_in2 c_out1 c_out2 nf1 nf2 proof)
        with Invalid_argument msg -> output_error msg)
     | _ -> output_error "Expected context digest, context fields, and Merkle proof fields")
  | _ ->
    output_error ("Usage: ct-merkle-envelope-digest CONTEXT_DIGEST VERSION NETWORK_ID ASSET_ID LEDGER_EPOCH ROOT ROOT_DEPTH PUBLIC_FEE C_IN1 C_IN2 C_OUT1 C_OUT2 NF1 NF2 " ^ ct_merkle_proof_args_usage)

let cmd_ct_wallet_proof_request_digest args =
  match args with
  | [protocol_version_str; network_id; asset_id_str; ledger_epoch_str; root; root_depth_str;
     public_fee_str; c_in1_str; c_in2_str; c_out1_str; c_out2_str; nf1_str; nf2_str;
     accepted_roots_str; accepted_root_depths_str; spent_nullifiers_str] ->
    (match
       parse_canonical_int protocol_version_str,
       parse_canonical_int asset_id_str,
       parse_canonical_int ledger_epoch_str,
       parse_canonical_int root_depth_str,
       parse_canonical_int public_fee_str,
       parse_canonical_vec c_in1_str,
       parse_canonical_vec c_in2_str,
       parse_canonical_vec c_out1_str,
       parse_canonical_vec c_out2_str,
       parse_canonical_vec nf1_str,
       parse_canonical_vec nf2_str,
       parse_string_list accepted_roots_str,
       parse_canonical_vec accepted_root_depths_str,
       parse_canonical_mat spent_nullifiers_str
     with
     | Some protocol_version, Some asset_id, Some ledger_epoch, Some root_depth, Some public_fee,
       Some c_in1, Some c_in2, Some c_out1, Some c_out2, Some nf1, Some nf2,
       Some accepted_roots, Some accepted_root_depths, Some spent_nullifiers ->
       (try
          output_string_result
            "ct_wallet_proof_request_digest"
            (Confidential_transaction.transaction_wallet_proof_request_digest
               protocol_version network_id asset_id ledger_epoch root root_depth public_fee
               c_in1 c_in2 c_out1 c_out2 nf1 nf2 accepted_roots accepted_root_depths spent_nullifiers)
        with Invalid_argument msg -> output_error msg)
     | _ -> output_error "Expected wallet proof request context, accepted roots, and spent nullifiers")
  | _ ->
    output_error "Usage: ct-wallet-proof-request-digest VERSION NETWORK_ID ASSET_ID LEDGER_EPOCH ROOT ROOT_DEPTH PUBLIC_FEE C_IN1 C_IN2 C_OUT1 C_OUT2 NF1 NF2 ACCEPTED_ROOTS ACCEPTED_ROOT_DEPTHS SPENT_NULLIFIERS"

let cmd_ct_accepted_root_window_digest args =
  match args with
  | [protocol_version_str; network_id; asset_id_str; ledger_epoch_str;
     roots_str; root_depths_str; valid_from_epochs_str; expires_at_epochs_str] ->
    (match
       parse_canonical_int protocol_version_str,
       parse_canonical_int asset_id_str,
       parse_canonical_int ledger_epoch_str,
       parse_string_list roots_str,
       parse_canonical_vec root_depths_str,
       parse_canonical_vec valid_from_epochs_str,
       parse_canonical_vec expires_at_epochs_str
     with
     | Some protocol_version, Some asset_id, Some ledger_epoch,
       Some roots, Some root_depths, Some valid_from_epochs, Some expires_at_epochs ->
       (try
          output_string_result
            "ct_accepted_root_window_digest"
            (Confidential_transaction.transaction_accepted_root_window_digest
               protocol_version network_id asset_id ledger_epoch
               roots root_depths valid_from_epochs expires_at_epochs)
        with Invalid_argument msg -> output_error msg)
     | _ -> output_error "Expected accepted-root window fields")
  | _ ->
    output_error "Usage: ct-accepted-root-window-digest VERSION NETWORK_ID ASSET_ID LEDGER_EPOCH ROOTS ROOT_DEPTHS VALID_FROM_EPOCHS EXPIRES_AT_EPOCHS"

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

let cmd_ct_sample_nullifier_mask args =
  match args with
  | [m_str; n2_str; q_str; beta_str; gamma_str] ->
    (match make_cb_params m_str n2_str q_str beta_str, parse_int gamma_str with
     | Some params, Some gamma ->
       output_sample (fun () ->
         let result = Confidential_transaction.sample_nullifier_mask params gamma in
         (match !output_format with
          | Human -> Printf.printf "sample_nullifier_mask = %s\n" (json_of_opening result)
          | Json -> Printf.printf "{\"result\":%s}\n" (json_of_opening result)))
     | _ -> output_error "Expected params (M N2 Q BETA) and gamma")
  | _ -> output_error "Usage: ct-sample-nullifier-mask M N2 Q BETA GAMMA"

let cmd_ct_sample_nullifier_masks args =
  match args with
  | [m_str; n2_str; q_str; beta_str; gamma_str; rounds_str] ->
    (match make_cb_params m_str n2_str q_str beta_str, parse_int gamma_str, parse_int rounds_str with
     | Some params, Some gamma, Some rounds ->
       output_sample (fun () ->
         let result = Confidential_transaction.sample_nullifier_masks params gamma rounds in
         (match !output_format with
          | Human -> Printf.printf "sample_nullifier_masks = %s\n" (json_of_openings result)
          | Json -> Printf.printf "{\"result\":%s}\n" (json_of_openings result)))
     | _ -> output_error "Expected params (M N2 Q BETA), gamma, and rounds")
  | _ -> output_error "Usage: ct-sample-nullifier-masks M N2 Q BETA GAMMA ROUNDS"

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

let ct_prove_usage command =
  Printf.sprintf "Usage: %s M N2 Q BETA G K CK NK LEDGER SPENT C1 C2 C3 C4 NF1 NF2 IN1_AMOUNT IN1_RAND IN2_AMOUNT IN2_RAND OUT1_AMOUNT OUT1_RAND OUT2_AMOUNT OUT2_RAND OUT1_BITS OUT1_BIT_RANDS OUT1_COMPS OUT1_COMP_RANDS OUT2_BITS OUT2_BIT_RANDS OUT2_COMPS OUT2_COMP_RANDS Y1_MSGS Y1_RANDS Y2_MSGS Y2_RANDS YBALS YOUT1_AMOUNTS YOUT1_PAIRSS YOUT2_AMOUNTS YOUT2_PAIRSS" command

let ct_verify_usage command =
  Printf.sprintf "Usage: %s M N2 Q BETA G K CK NK LEDGER SPENT C1 C2 C3 C4 NF1 NF2 IN1_A_COMMITS IN1_A_NULLIFIERS IN1_Z_MSGS IN1_Z_RANDS IN2_A_COMMITS IN2_A_NULLIFIERS IN2_Z_MSGS IN2_Z_RANDS BAL_AS BAL_ZS OUT1_BITS OUT1_COMPS OUT1_AMOUNT_AS OUT1_AMOUNT_ZS OUT1_PAIR_ASS OUT1_PAIR_ZSS OUT2_BITS OUT2_COMPS OUT2_AMOUNT_AS OUT2_AMOUNT_ZS OUT2_PAIR_ASS OUT2_PAIR_ZSS" command

let ct_verify_bench_usage command =
  Printf.sprintf "Usage: %s ITERATIONS WARMUP M N2 Q BETA G K CK NK LEDGER SPENT C1 C2 C3 C4 NF1 NF2 IN1_A_COMMITS IN1_A_NULLIFIERS IN1_Z_MSGS IN1_Z_RANDS IN2_A_COMMITS IN2_A_NULLIFIERS IN2_Z_MSGS IN2_Z_RANDS BAL_AS BAL_ZS OUT1_BITS OUT1_COMPS OUT1_AMOUNT_AS OUT1_AMOUNT_ZS OUT1_PAIR_ASS OUT1_PAIR_ZSS OUT2_BITS OUT2_COMPS OUT2_AMOUNT_AS OUT2_AMOUNT_ZS OUT2_PAIR_ASS OUT2_PAIR_ZSS" command

let cmd_ct_prove_with_usage command args =
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
  | _ -> output_error (ct_prove_usage command)

let cmd_ct_prove_scaffold args =
  cmd_ct_prove_with_usage "ct-prove-scaffold" args

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

let prepare_ct_verify_with_usage command args =
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
  | _ -> Error (ct_verify_usage command)

let prepare_ct_verify_scaffold args =
  prepare_ct_verify_with_usage "ct-verify-scaffold" args

let prepare_ct_verify_merkle_with_root ?public_fee ?root_depth root_override args =
  match args with
  | m_str :: n2_str :: q_str :: beta_str :: gamma_str :: k_str :: ck_str :: nk_str ::
    ledger_str :: spent_str :: c_in1_str :: c_in2_str :: c_out1_str :: c_out2_str ::
    nf1_str :: nf2_str :: proof_args ->
    (match
       make_canonical_cb_params m_str n2_str q_str beta_str,
       parse_canonical_int gamma_str,
       parse_canonical_int k_str,
       parse_canonical_mat ck_str,
       parse_canonical_mat nk_str,
       parse_canonical_mat ledger_str,
       parse_canonical_mat spent_str,
       parse_canonical_vec c_in1_str,
       parse_canonical_vec c_in2_str,
       parse_canonical_vec c_out1_str,
       parse_canonical_vec c_out2_str,
       parse_canonical_vec nf1_str,
       parse_canonical_vec nf2_str,
       parse_ct_merkle_proof_digest_args proof_args with
     | Some params, Some gamma, Some k, Some ck, Some nk, Some ledger, Some spent,
       Some c_in1, Some c_in2, Some c_out1, Some c_out2, Some nf1, Some nf2,
       Ok proof ->
       let root =
         match root_override with
         | Some root -> root
         | None -> Confidential_transaction.merkle_ledger_root ledger
       in
       let in1_depth =
         List.length proof.Confidential_transaction.tx_merkle_in1_member.Confidential_merkle.merkle_siblings
       in
       let in2_depth =
         List.length proof.Confidential_transaction.tx_merkle_in2_member.Confidential_merkle.merkle_siblings
       in
       let depth_ok =
         match root_depth with
         | None -> true
         | Some depth -> in1_depth = depth && in2_depth = depth
       in
       Ok
         (fun () ->
           depth_ok &&
           match public_fee with
           | None ->
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
               proof
           | Some fee ->
             Confidential_transaction.transaction_fs_verify_merkle_fee
               params
               gamma
               k
               ck
               nk
               root
               spent
               fee
               c_in1
               c_in2
               c_out1
               c_out2
               nf1
               nf2
               proof)
     | _ -> Error "Expected params, keys, ledger, commitments, nullifiers, and transaction-proof fields")
  | _ -> Error ("Usage: ct-verify-merkle M N2 Q BETA G K CK NK LEDGER SPENT C1 C2 C3 C4 NF1 NF2 " ^ ct_merkle_proof_args_usage)

let prepare_ct_verify_merkle args =
  prepare_ct_verify_merkle_with_root None args

let cmd_ct_verify_scaffold args =
  match prepare_ct_verify_scaffold args with
  | Ok verify -> output_result "transaction_fs_verify" (if verify () then "true" else "false")
  | Error msg -> output_error msg

let cmd_ct_verify_merkle args =
  match prepare_ct_verify_merkle args with
  | Ok verify -> output_result "transaction_fs_verify_merkle" (if verify () then "true" else "false")
  | Error msg -> output_error msg

let cmd_ct_verify_merkle_envelope args =
  match args with
  | m_str :: n2_str :: q_str :: beta_str :: gamma_str :: k_str :: ck_str :: nk_str ::
    ledger_str :: spent_str :: expected_version_str :: expected_network_id ::
    expected_asset_id_str :: expected_ledger_epoch_str :: expected_root ::
    expected_root_depth_str :: expected_public_fee_str :: context_digest :: protocol_version_str :: network_id ::
    asset_id_str :: ledger_epoch_str :: root :: root_depth_str :: public_fee_str :: c_in1_str ::
    c_in2_str :: c_out1_str :: c_out2_str :: nf1_str :: nf2_str :: proof_args ->
    (match
       parse_canonical_int expected_version_str,
       parse_canonical_int expected_asset_id_str,
       parse_canonical_int expected_ledger_epoch_str,
       parse_canonical_int expected_root_depth_str,
       parse_canonical_int expected_public_fee_str,
       parse_canonical_int protocol_version_str,
       parse_canonical_int asset_id_str,
       parse_canonical_int ledger_epoch_str,
       parse_canonical_int root_depth_str,
       parse_canonical_int public_fee_str,
       parse_canonical_vec c_in1_str,
       parse_canonical_vec c_in2_str,
       parse_canonical_vec c_out1_str,
       parse_canonical_vec c_out2_str,
       parse_canonical_vec nf1_str,
       parse_canonical_vec nf2_str with
     | Some expected_version, Some expected_asset_id, Some expected_ledger_epoch,
       Some expected_root_depth, Some expected_public_fee, Some protocol_version, Some asset_id,
       Some ledger_epoch, Some root_depth, Some public_fee, Some c_in1, Some c_in2,
       Some c_out1, Some c_out2, Some nf1, Some nf2 ->
       (try
          let computed_digest =
            Confidential_transaction.transaction_context_digest
              protocol_version network_id asset_id ledger_epoch root root_depth public_fee
              c_in1 c_in2 c_out1 c_out2 nf1 nf2
          in
          let policy_ok =
            expected_public_fee = public_fee &&
            protocol_version = expected_version &&
            network_id = expected_network_id &&
            asset_id = expected_asset_id &&
            ledger_epoch = expected_ledger_epoch &&
            root = expected_root &&
            root_depth = expected_root_depth &&
            context_digest = computed_digest
          in
          if not policy_ok then
            output_result "transaction_fs_verify_merkle_envelope" "false"
          else
            let merkle_args =
              [m_str; n2_str; q_str; beta_str; gamma_str; k_str; ck_str; nk_str;
               ledger_str; spent_str; c_in1_str; c_in2_str; c_out1_str; c_out2_str;
               nf1_str; nf2_str] @ proof_args
            in
            match prepare_ct_verify_merkle_with_root ~public_fee ~root_depth (Some root) merkle_args with
            | Ok verify ->
              output_result "transaction_fs_verify_merkle_envelope"
                (if verify () then "true" else "false")
            | Error msg -> output_error msg
        with Invalid_argument msg -> output_error msg)
     | _ -> output_error "Expected envelope policy, context, and proof fields")
  | _ ->
    output_error "Usage: ct-verify-merkle-envelope M N2 Q BETA G K CK NK LEDGER SPENT EXPECTED_VERSION EXPECTED_NETWORK EXPECTED_ASSET EXPECTED_EPOCH EXPECTED_ROOT EXPECTED_ROOT_DEPTH EXPECTED_FEE CONTEXT_DIGEST VERSION NETWORK ASSET EPOCH ROOT ROOT_DEPTH FEE C1 C2 C3 C4 NF1 NF2 IN1_A_COMMITS IN1_A_NULLIFIERS IN1_Z_MSGS IN1_Z_RANDS IN2_A_COMMITS IN2_A_NULLIFIERS IN2_Z_MSGS IN2_Z_RANDS BAL_AS BAL_ZS OUT1_BITS OUT1_COMPS OUT1_AMOUNT_AS OUT1_AMOUNT_ZS OUT1_PAIR_ASS OUT1_PAIR_ZSS OUT2_BITS OUT2_COMPS OUT2_AMOUNT_AS OUT2_AMOUNT_ZS OUT2_PAIR_ASS OUT2_PAIR_ZSS"

let cmd_ct_verify_bench_with_usage command prepare args =
  match args with
  | iterations_str :: warmup_str :: rest ->
    (match parse_int iterations_str, parse_int warmup_str with
     | Some iterations, Some warmup when iterations > 0 && warmup >= 0 ->
       (match prepare rest with
        | Ok verify -> output_bench_stats "transaction_fs_verify_bench" (benchmark_bool warmup iterations verify)
        | Error msg when String.length msg >= 5 && String.sub msg 0 5 = "Usage" ->
          output_error (ct_verify_bench_usage command)
        | Error msg -> output_error msg)
     | _ -> output_error "Expected positive ITERATIONS and non-negative WARMUP")
  | _ -> output_error (ct_verify_bench_usage command)

let cmd_ct_verify_bench_scaffold args =
  cmd_ct_verify_bench_with_usage "ct-verify-bench-scaffold" prepare_ct_verify_scaffold args

let cmd_ct_ledger_step_verify_scaffold args =
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
            Confidential_transaction.ledger_step_valid_scaffold
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
          output_result "ledger_step_valid_scaffold" (if result then "true" else "false")
        | _ -> output_error "Expected consistent verified-note inputs and membership proofs for both input commitments")
     | _ -> output_error "Expected params, keys, verified-note ledger fields, nullifiers, and transaction-proof fields")
  | _ -> output_error "Usage: ct-ledger-step-verify-scaffold M N2 Q BETA G K CK NK NOTE_COMMITMENTS NOTE_BITS NOTE_COMPS NOTE_AMOUNT_AS NOTE_AMOUNT_ZS NOTE_PAIR_AS NOTE_PAIR_ZS SPENT C1 C2 C3 C4 NF1 NF2 IN1_A_COMMITS IN1_A_NULLIFIERS IN1_Z_MSGS IN1_Z_RANDS IN2_A_COMMITS IN2_A_NULLIFIERS IN2_Z_MSGS IN2_Z_RANDS BAL_AS BAL_ZS OUT1_BITS OUT1_COMPS OUT1_AMOUNT_AS OUT1_AMOUNT_ZS OUT1_PAIR_ASS OUT1_PAIR_ZSS OUT2_BITS OUT2_COMPS OUT2_AMOUNT_AS OUT2_AMOUNT_ZS OUT2_PAIR_ASS OUT2_PAIR_ZSS"

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
  print_endline "  cb-sample-mask M N2 Q BETA G        Sample a CSPRNG balance mask";
  print_endline "  cb-sample-masks M N2 Q BETA G ROUNDS  Sample CSPRNG balance masks";
  print_endline "  cb-valid-response M N2 Q BETA G Z   Check response bounds";
  print_endline "  cb-balance-commitment C1 C2 C3 C4 Q Aggregate commitments for zero-balance checking";
  print_endline "  cb-canonical-challenge M N2 Q BETA CK C A  Deterministic Fiat-Shamir challenge";
  print_endline "  cb-sigma-commit M N2 Q BETA CK Y    Compute sigma announcement";
  print_endline "  cb-sigma-respond R Y E              Compute sigma response";
  print_endline "  cb-sigma-verify M N2 Q BETA G CK C A E Z  Verify sigma step";
  print_endline "  cb-prove M N2 Q BETA G CK C R Y     Build deterministic balance proof";
  print_endline "  cb-verify M N2 Q BETA G CK C A Z    Verify deterministic balance proof";
  print_endline "  ct-balance-bigint-rand-commit M N2 Q BETA CK R  Commit with widened integer arithmetic";
  print_endline "  ct-balance-bigint-fs-fields CK C AS  Compute widened balance Fiat-Shamir fields";
  print_endline "  ct-balance-bigint-fs-challenges M N2 Q BETA CK C AS ROUNDS  Expand widened balance challenges";
  print_endline "  ct-balance-bigint-prove M N2 Q BETA G CK C R YS  Build widened balance proof";
  print_endline "  ct-balance-bigint-verify M N2 Q BETA G CK C AS ZS  Verify widened balance proof";
  print_endline "  ct-range-bigint-fs-fields CK C BITS COMPS AMOUNT_AS PAIR_ASS  Compute widened range Fiat-Shamir fields";
  print_endline "  ct-range-bigint-fs-challenges M N2 Q BETA CK C BITS COMPS AMOUNT_AS PAIR_ASS ROUNDS  Expand widened range challenges";
  print_endline "  ct-range-bigint-prove M N2 Q BETA G K CK C AMOUNT RAND BITS BIT_RANDS COMPS COMP_RANDS YAMOUNTS YPAIRSS  Build widened range proof";
  print_endline "  ct-range-bigint-verify M N2 Q BETA G K CK C BITS COMPS AMOUNT_AS AMOUNT_ZS PAIR_ASS PAIR_ZSS  Verify widened range proof";
  print_endline "  ct-nullifier-bigint M N2 Q BETA NK AMOUNT RAND  Compute a widened note nullifier";
  print_endline "  ct-nullifier-bigint-fs-fields CK NK C NF ACOMMITS ANULLIFIERS  Compute widened nullifier Fiat-Shamir fields";
  print_endline "  ct-nullifier-bigint-fs-challenges M N2 Q BETA CK NK C NF ACOMMITS ANULLIFIERS ROUNDS  Expand widened nullifier challenges";
  print_endline "  ct-nullifier-bigint-prove M N2 Q BETA G CK NK C NF AMOUNT RAND YMSGS YRANDS  Build widened nullifier proof";
  print_endline "  ct-nullifier-bigint-verify M N2 Q BETA G CK NK C NF ACOMMITS ANULLIFIERS ZMSGS ZRANDS  Verify widened nullifier proof";
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
  print_endline "  ct-bignum-encode INTEGER     Encode a canonical signed arbitrary-precision integer";
  print_endline "  ct-bignum-vector-encode INTS... Encode canonical signed arbitrary-precision integers";
  print_endline "  ct-bignum-merkle-leaf C      Hash a bignum confidential note commitment leaf";
  print_endline "  ct-bignum-merkle-empty WIDTH Hash an empty bignum Merkle placeholder";
  print_endline "  ct-bignum-merkle-node LEFT RIGHT Hash an internal bignum Merkle node";
  print_endline "  ct-bignum-merkle-root LEDGER Compute bignum cryptographic Merkle root";
  print_endline "  ct-bignum-merkle-member-prove LEDGER C Build bignum Merkle membership proof";
  print_endline "  ct-bignum-merkle-member-verify LEDGER C Verify bignum Merkle membership proof";
  print_endline "  ct-bignum-transaction-context VERSION NETWORK ASSET EPOCH ROOT ROOT_DEPTH FEE C1 C2 C3 C4 NF1 NF2";
  print_endline "  ct-bignum-merkle-proof-digest ... Hash canonical bignum Merkle transaction proof bytes";
  print_endline "  ct-bignum-merkle-envelope-digest ... Hash canonical bignum context digest and proof digest bytes";
  print_endline "  ct-bignum-wallet-proof-request-digest ... Hash canonical bignum wallet proof request bytes";
  print_endline "  ct-bignum-accepted-root-window-digest ... Hash canonical bignum live accepted-root window bytes";
  print_endline "  ct-transaction-context VERSION NETWORK ASSET EPOCH ROOT ROOT_DEPTH FEE C1 C2 C3 C4 NF1 NF2";
  print_endline "  ct-merkle-proof-digest ... Hash canonical Merkle transaction proof bytes";
  print_endline "  ct-merkle-envelope-digest ... Hash canonical context digest and proof digest bytes";
  print_endline "  ct-wallet-proof-request-digest ... Hash canonical wallet proof request bytes";
  print_endline "  ct-accepted-root-window-digest ... Hash canonical live accepted-root window bytes";
  print_endline "";
  print_endline "Confidential Transaction Commands:";
  print_endline "  ct-sample-opening MSG_LEN RAND_LEN BOUND  Sample a bounded CSPRNG opening";
  print_endline "  ct-sample-openings COUNT MSG_LEN RAND_LEN BOUND  Sample bounded CSPRNG openings";
  print_endline "  ct-nullifier M N2 Q BETA NK AMOUNT RAND  Compute a deterministic note nullifier";
  print_endline "  ct-sample-nullifier-mask M N2 Q BETA G  Sample a CSPRNG nullifier mask";
  print_endline "  ct-sample-nullifier-masks M N2 Q BETA G ROUNDS  Sample CSPRNG nullifier masks";
  print_endline "  ct-nullifier-canonical-challenge M N2 Q BETA CK NK C NF ACOMMIT ANULLIFIER  Deterministic nullifier Fiat-Shamir challenge";
  print_endline "  ct-nullifier-prove M N2 Q BETA G CK NK C NF AMOUNT RAND YMSGS YRANDS  Build repeated-round deterministic nullifier proof";
  print_endline "  ct-nullifier-verify M N2 Q BETA G CK NK C NF ACOMMITS ANULLIFIERS ZMSGS ZRANDS  Verify repeated-round deterministic nullifier proof";
  print_endline "  ct-member-prove M N2 Q BETA LEDGER C   Build explicit ledger membership proof";
  print_endline "  ct-member-verify M N2 Q BETA LEDGER C  Verify explicit ledger membership proof";
  print_endline "  ct-ledger-step-verify-scaffold ... Verify scaffold ledger-step validity from verified input notes (requires ISABELLA_ENABLE_SCAFFOLD_COMPAT=1)";
  print_endline "  ct-prove-scaffold ...  Build scaffold confidential-transaction proof over the algebraic ledger hash (requires ISABELLA_ENABLE_SCAFFOLD_COMPAT=1)";
  print_endline "  ct-prove-merkle ...  Build deterministic confidential-transaction proof with Merkle membership";
  print_endline "  ct-verify-scaffold ... Verify scaffold confidential-transaction proof over the algebraic ledger hash (requires ISABELLA_ENABLE_SCAFFOLD_COMPAT=1)";
  print_endline "  ct-verify-merkle ... Verify deterministic confidential-transaction proof with Merkle membership";
  print_endline "  ct-verify-merkle-envelope ... Verify context digest, expected policy, and Merkle transaction proof";
  print_endline "  ct-verify-bench-scaffold I W ... Benchmark scaffold confidential-transaction verification natively (requires ISABELLA_ENABLE_SCAFFOLD_COMPAT=1)";
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
  | "cb-sample-mask" -> cmd_cb_sample_mask args
  | "cb-sample-masks" -> cmd_cb_sample_masks args
  | "cb-valid-response" -> cmd_cb_valid_response args
  | "cb-balance-commitment" -> cmd_cb_balance_commitment args
  | "cb-canonical-challenge" -> cmd_cb_canonical_challenge args
  | "cb-sigma-commit" -> cmd_cb_sigma_commit args
  | "cb-sigma-respond" -> cmd_cb_sigma_respond args
  | "cb-sigma-verify" -> cmd_cb_sigma_verify args
  | "cb-prove" -> cmd_cb_prove args
  | "cb-verify" -> cmd_cb_verify args
  | "ct-balance-bigint-rand-commit" -> cmd_ct_balance_bigint_rand_commit args
  | "ct-balance-bigint-fs-fields" -> cmd_ct_balance_bigint_fs_fields args
  | "ct-balance-bigint-fs-challenges" -> cmd_ct_balance_bigint_fs_challenges args
  | "ct-balance-bigint-prove" -> cmd_ct_balance_bigint_prove args
  | "ct-balance-bigint-verify" -> cmd_ct_balance_bigint_verify args
  | "ct-range-bigint-fs-fields" -> cmd_ct_range_bigint_fs_fields args
  | "ct-range-bigint-fs-challenges" -> cmd_ct_range_bigint_fs_challenges args
  | "ct-range-bigint-prove" -> cmd_ct_range_bigint_prove args
  | "ct-range-bigint-verify" -> cmd_ct_range_bigint_verify args
  | "ct-nullifier-bigint" -> cmd_ct_nullifier_bigint args
  | "ct-nullifier-bigint-fs-fields" -> cmd_ct_nullifier_bigint_fs_fields args
  | "ct-nullifier-bigint-fs-challenges" -> cmd_ct_nullifier_bigint_fs_challenges args
  | "ct-nullifier-bigint-prove" -> cmd_ct_nullifier_bigint_prove args
  | "ct-nullifier-bigint-verify" -> cmd_ct_nullifier_bigint_verify args
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
  | "ct-bignum-encode" -> cmd_ct_bignum_encode args
  | "ct-bignum-vector-encode" -> cmd_ct_bignum_vector_encode args
  | "ct-bignum-merkle-leaf" -> cmd_ct_bignum_merkle_leaf args
  | "ct-bignum-merkle-empty" -> cmd_ct_bignum_merkle_empty args
  | "ct-bignum-merkle-node" -> cmd_ct_bignum_merkle_node args
  | "ct-bignum-merkle-root" -> cmd_ct_bignum_merkle_root args
  | "ct-bignum-merkle-member-prove" -> cmd_ct_bignum_merkle_member_prove args
  | "ct-bignum-merkle-member-verify" -> cmd_ct_bignum_merkle_member_verify args
  | "ct-bignum-transaction-context" -> cmd_ct_bignum_transaction_context args
  | "ct-bignum-merkle-proof-digest" -> cmd_ct_bignum_merkle_proof_digest args
  | "ct-bignum-merkle-envelope-digest" -> cmd_ct_bignum_merkle_envelope_digest args
  | "ct-bignum-wallet-proof-request-digest" -> cmd_ct_bignum_wallet_proof_request_digest args
  | "ct-bignum-accepted-root-window-digest" -> cmd_ct_bignum_accepted_root_window_digest args
  | "ct-transaction-context" -> cmd_ct_transaction_context args
  | "ct-merkle-proof-digest" -> cmd_ct_merkle_proof_digest args
  | "ct-merkle-envelope-digest" -> cmd_ct_merkle_envelope_digest args
  | "ct-wallet-proof-request-digest" -> cmd_ct_wallet_proof_request_digest args
  | "ct-accepted-root-window-digest" -> cmd_ct_accepted_root_window_digest args
  | "ct-sample-opening" -> cmd_ct_sample_opening args
  | "ct-sample-openings" -> cmd_ct_sample_openings args
  | "ct-nullifier" -> cmd_ct_nullifier args
  | "ct-sample-nullifier-mask" -> cmd_ct_sample_nullifier_mask args
  | "ct-sample-nullifier-masks" -> cmd_ct_sample_nullifier_masks args
  | "ct-nullifier-canonical-challenge" -> cmd_ct_nullifier_canonical_challenge args
  | "ct-nullifier-prove" -> cmd_ct_nullifier_prove args
  | "ct-nullifier-verify" -> cmd_ct_nullifier_verify args
  | "ct-member-prove" -> cmd_ct_member_prove args
  | "ct-member-verify" -> cmd_ct_member_verify args
  | "ct-ledger-step-verify-scaffold" -> require_scaffold_compat (fun () -> cmd_ct_ledger_step_verify_scaffold args)
  | "ct-prove-scaffold" -> require_scaffold_compat (fun () -> cmd_ct_prove_scaffold args)
  | "ct-prove-merkle" -> cmd_ct_prove_merkle args
  | "ct-verify-scaffold" -> require_scaffold_compat (fun () -> cmd_ct_verify_scaffold args)
  | "ct-verify-merkle" -> cmd_ct_verify_merkle args
  | "ct-verify-merkle-envelope" -> cmd_ct_verify_merkle_envelope args
  | "ct-verify-bench-scaffold" -> require_scaffold_compat (fun () -> cmd_ct_verify_bench_scaffold args)
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
