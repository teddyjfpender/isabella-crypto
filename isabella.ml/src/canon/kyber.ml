(** CRYSTALS-Kyber (ML-KEM) Key Encapsulation Mechanism
    Generated from Canon/Crypto/Kyber.thy

    FIPS 203 standardized lattice-based KEM for post-quantum security.
    Uses Module-LWE hardness and O(n log n) NTT for efficiency. *)

(** Kyber polynomial: 256 coefficients mod q *)
type kyber_poly = int list

(** Kyber vector: k polynomials *)
type kyber_vec = kyber_poly list

(** Kyber matrix: k x k polynomials *)
type kyber_matrix = kyber_poly list list

(** Kyber parameters *)
type kyber_params = {
  kyber_n : int;     (** Polynomial degree (always 256) *)
  kyber_q : int;     (** Modulus (always 3329) *)
  kyber_k : int;     (** Module dimension (2, 3, or 4) *)
  kyber_eta1 : int;  (** Noise parameter for keygen *)
  kyber_eta2 : int;  (** Noise parameter for encryption *)
  kyber_du : int;    (** Compression parameter for u *)
  kyber_dv : int;    (** Compression parameter for v *)
}

(** Kyber public key *)
type kyber_pk = {
  pk_A : kyber_matrix;  (** Public matrix A *)
  pk_t : kyber_vec;     (** Public vector t = As + e *)
}

(** Kyber secret key *)
type kyber_sk = {
  sk_s : kyber_vec;   (** Secret vector s *)
  sk_pk : kyber_pk;   (** Cached public key *)
}

(** Kyber ciphertext *)
type kyber_ct = {
  ct_u : kyber_vec;   (** Encrypted vector u *)
  ct_v : kyber_poly;  (** Encrypted polynomial v *)
}

(** Create Kyber parameters *)
let make_kyber_params n q k eta1 eta2 du dv = {
  kyber_n = n; kyber_q = q; kyber_k = k;
  kyber_eta1 = eta1; kyber_eta2 = eta2;
  kyber_du = du; kyber_dv = dv
}

(** Validate Kyber parameters *)
let valid_kyber_params p =
  p.kyber_n = 256 &&
  p.kyber_q = 3329 &&
  List.mem p.kyber_k [2; 3; 4] &&
  p.kyber_eta1 > 0 &&
  p.kyber_eta2 > 0 &&
  p.kyber_du > 0 && p.kyber_du <= 12 &&
  p.kyber_dv > 0 && p.kyber_dv <= 12

(** Kyber-512 parameters (NIST Level 1) *)
let kyber512_params = {
  kyber_n = 256; kyber_q = 3329; kyber_k = 2;
  kyber_eta1 = 3; kyber_eta2 = 2;
  kyber_du = 10; kyber_dv = 4
}

(** Kyber-768 parameters (NIST Level 3) *)
let kyber768_params = {
  kyber_n = 256; kyber_q = 3329; kyber_k = 3;
  kyber_eta1 = 2; kyber_eta2 = 2;
  kyber_du = 10; kyber_dv = 4
}

(** Kyber-1024 parameters (NIST Level 5) *)
let kyber1024_params = {
  kyber_n = 256; kyber_q = 3329; kyber_k = 4;
  kyber_eta1 = 2; kyber_eta2 = 2;
  kyber_du = 11; kyber_dv = 5
}

(* Kyber constants *)
let kyber_q = 3329
let kyber_n = 256
let kyber_omega = 17

(** Forward NTT for Kyber polynomial *)
let kyber_ntt a = Ntt.ntt_fast a kyber_omega kyber_q kyber_n

(** Inverse NTT for Kyber polynomial *)
let kyber_intt a_hat = Ntt.intt_fast a_hat kyber_omega kyber_q kyber_n

(** Polynomial multiplication via NTT *)
let kyber_poly_mult_ntt a b =
  let a_hat = kyber_ntt a in
  let b_hat = kyber_ntt b in
  let c_hat = Ntt.ntt_pointwise_mult a_hat b_hat kyber_q in
  kyber_intt c_hat

(** Polynomial addition mod q *)
let kyber_poly_add a b =
  List.map2 (fun x y -> (x + y) mod kyber_q) a b

(** Polynomial subtraction mod q *)
let kyber_poly_sub a b =
  List.map2 (fun x y -> ((x - y) mod kyber_q + kyber_q) mod kyber_q) a b

(** Vector addition *)
let kyber_vec_add = List.map2 kyber_poly_add

(** Apply NTT to each polynomial in vector *)
let kyber_vec_ntt = List.map kyber_ntt

(** Apply inverse NTT to each polynomial in vector *)
let kyber_vec_intt = List.map kyber_intt

(** Inner product of two vectors in NTT domain *)
let kyber_inner_prod_ntt u v =
  let products = List.map2 (fun a b -> Ntt.ntt_pointwise_mult a b kyber_q) u v in
  let zero = List.init kyber_n (fun _ -> 0) in
  List.fold_left kyber_poly_add zero products

(** Matrix-vector multiplication in NTT domain *)
let kyber_mat_vec_mult_ntt a_hat s_hat =
  List.map (fun row -> kyber_inner_prod_ntt row s_hat) a_hat

(** Matrix transpose *)
let rec kyber_transpose = function
  | [] -> []
  | [] :: _ -> []
  | rows -> List.map List.hd rows :: kyber_transpose (List.map List.tl rows)

(** Encode message bits as polynomial *)
let kyber_encode_msg msg =
  let half_q = (kyber_q + 1) / 2 in
  let rec take n lst = match n, lst with
    | 0, _ | _, [] -> []
    | n, x :: xs -> x :: take (n - 1) xs
  in
  List.map (fun b -> if b = 1 then half_q else 0) (take kyber_n msg)

(** Decode polynomial to message bits *)
let kyber_decode_msg v =
  let quarter_q = (kyber_q + 2) / 4 in
  let centered c =
    let r = c mod kyber_q in
    if r > kyber_q / 2 then r - kyber_q else r
  in
  let decode c = if abs (centered c) > quarter_q then 1 else 0 in
  List.map decode v

(** Key generation *)
let kyber_keygen a s e =
  let a_hat = List.map (List.map kyber_ntt) a in
  let s_hat = kyber_vec_ntt s in
  let e_hat = kyber_vec_ntt e in
  let t_hat = kyber_vec_add (kyber_mat_vec_mult_ntt a_hat s_hat) e_hat in
  let t = kyber_vec_intt t_hat in
  let pk = { pk_A = a; pk_t = t } in
  let sk = { sk_s = s; sk_pk = pk } in
  (pk, sk)

(** Encryption *)
let kyber_encrypt pk msg r e1 e2 =
  let a_hat = List.map (List.map kyber_ntt) pk.pk_A in
  let t_hat = kyber_vec_ntt pk.pk_t in
  let r_hat = kyber_vec_ntt r in
  (* u = A^T * r + e1 *)
  let at_hat = kyber_transpose a_hat in
  let u_hat = kyber_mat_vec_mult_ntt at_hat r_hat in
  let u = kyber_vec_add (kyber_vec_intt u_hat) e1 in
  (* v = t^T * r + e2 + encode(msg) *)
  let v_hat = kyber_inner_prod_ntt t_hat r_hat in
  let v_base = kyber_poly_add (kyber_intt v_hat) e2 in
  let v = kyber_poly_add v_base (kyber_encode_msg msg) in
  { ct_u = u; ct_v = v }

(** Decryption *)
let kyber_decrypt sk ct =
  let s_hat = kyber_vec_ntt sk.sk_s in
  let u_hat = kyber_vec_ntt ct.ct_u in
  (* v - s^T * u *)
  let inner_hat = kyber_inner_prod_ntt s_hat u_hat in
  let inner = kyber_intt inner_hat in
  let m_poly = kyber_poly_sub ct.ct_v inner in
  kyber_decode_msg m_poly

(** Simple KEM encapsulation *)
let kyber_encaps_simple pk msg r e1 e2 =
  let ct = kyber_encrypt pk msg r e1 e2 in
  (msg, ct)

(** Simple KEM decapsulation *)
let kyber_decaps_simple = kyber_decrypt
