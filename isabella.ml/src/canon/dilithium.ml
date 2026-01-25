(** CRYSTALS-Dilithium (ML-DSA) Digital Signature Scheme
    Generated from Canon/Crypto/Dilithium.thy

    FIPS 204 standardized lattice-based digital signature for post-quantum security.
    Uses Module-LWE/Module-SIS hardness with Fiat-Shamir with Aborts paradigm. *)

(** Dilithium polynomial: 256 coefficients mod q *)
type dil_poly = int list

(** Dilithium vector: polynomials *)
type dil_vec = dil_poly list

(** Dilithium matrix: vectors of polynomials *)
type dil_matrix = dil_vec list

(** Dilithium parameters (FIPS 204 ML-DSA) *)
type dilithium_params = {
  dil_n : int;       (** Polynomial degree (always 256) *)
  dil_q : int;       (** Modulus (always 8380417) *)
  dil_k : int;       (** Rows of A (determines pk size) *)
  dil_l : int;       (** Columns of A (determines sig size) *)
  dil_eta : int;     (** Secret coefficient bound *)
  dil_tau : int;     (** Number of +/-1s in challenge *)
  dil_beta : int;    (** tau * eta *)
  dil_gamma1 : int;  (** y coefficient bound *)
  dil_gamma2 : int;  (** Low-order rounding range *)
  dil_d : int;       (** Dropped bits in t *)
  dil_omega : int;   (** Max hint weight *)
}

(** Dilithium public key *)
type dil_pk = {
  pk_rho : int list;  (** Seed for A (32 bytes) *)
  pk_t1 : dil_vec;    (** t1 = Power2Round(t, d).high *)
}

(** Dilithium secret key *)
type dil_sk = {
  sk_rho : int list;  (** Seed for A *)
  sk_K : int list;    (** Key for PRF *)
  sk_tr : int list;   (** H(pk) *)
  sk_s1 : dil_vec;    (** Secret vector (length l) *)
  sk_s2 : dil_vec;    (** Secret vector (length k) *)
  sk_t0 : dil_vec;    (** t0 = Power2Round(t, d).low *)
}

(** Dilithium signature *)
type dil_signature = {
  sig_c_tilde : int list;   (** Challenge seed (32 bytes) *)
  sig_z : dil_vec;          (** Response vector (length l) *)
  sig_h : int list list;    (** Hint (indices of 1s) *)
}

(** ML-DSA-44 parameters (NIST security level 2) *)
let mldsa44_params = {
  dil_n = 256;
  dil_q = 8380417;
  dil_k = 4;
  dil_l = 4;
  dil_eta = 2;
  dil_tau = 39;
  dil_beta = 78;
  dil_gamma1 = 131072;   (* 2^17 *)
  dil_gamma2 = 95232;    (* (q-1)/88 *)
  dil_d = 13;
  dil_omega = 80;
}

(** ML-DSA-65 parameters (NIST security level 3) *)
let mldsa65_params = {
  dil_n = 256;
  dil_q = 8380417;
  dil_k = 6;
  dil_l = 5;
  dil_eta = 4;
  dil_tau = 49;
  dil_beta = 196;
  dil_gamma1 = 524288;   (* 2^19 *)
  dil_gamma2 = 261888;   (* (q-1)/32 *)
  dil_d = 13;
  dil_omega = 55;
}

(** ML-DSA-87 parameters (NIST security level 5) *)
let mldsa87_params = {
  dil_n = 256;
  dil_q = 8380417;
  dil_k = 8;
  dil_l = 7;
  dil_eta = 2;
  dil_tau = 60;
  dil_beta = 120;
  dil_gamma1 = 524288;   (* 2^19 *)
  dil_gamma2 = 261888;   (* (q-1)/32 *)
  dil_d = 13;
  dil_omega = 75;
}

(** Dilithium NTT parameters *)
let dil_ntt_q = 8380417
let dil_ntt_omega = 1753  (* Primitive 512th root of unity mod q *)

(** Centered modular reduction: r mod+/- m *)
let mod_centered r m =
  let r' = r mod m in
  let r' = if r' < 0 then r' + m else r' in
  if r' > m / 2 then r' - m else r'

(** Power2Round: split r into (r1, r0) where r = r1 * 2^d + r0 *)
let power2round_coeff r d =
  let two_d = 1 lsl d in
  let r0 = mod_centered r two_d in
  let r1 = (r - r0) / two_d in
  (r1, r0)

(** Power2Round on polynomial *)
let power2round_poly p d =
  let pairs = List.map (fun c -> power2round_coeff c d) p in
  (List.map fst pairs, List.map snd pairs)

(** Power2Round on vector *)
let power2round_vec v d =
  let pairs = List.map (fun p -> power2round_poly p d) v in
  (List.map fst pairs, List.map snd pairs)

(** Decompose: split r into high and low bits using alpha *)
let decompose_coeff r alpha =
  let r0 = mod_centered r alpha in
  let r1 = (r - r0) / alpha in
  if r - r0 = dil_ntt_q - 1 then (0, r0 - 1)
  else (r1, r0)

(** HighBits: extract high-order bits *)
let highbits_coeff r alpha = fst (decompose_coeff r alpha)

(** LowBits: extract low-order bits *)
let lowbits_coeff r alpha = snd (decompose_coeff r alpha)

(** HighBits on polynomial *)
let highbits_poly p alpha = List.map (fun c -> highbits_coeff c alpha) p

(** LowBits on polynomial *)
let lowbits_poly p alpha = List.map (fun c -> lowbits_coeff c alpha) p

(** HighBits on vector *)
let highbits_vec v alpha = List.map (fun p -> highbits_poly p alpha) v

(** LowBits on vector *)
let lowbits_vec v alpha = List.map (fun p -> lowbits_poly p alpha) v

(** MakeHint: compute hint bit *)
let makehint_coeff z r alpha =
  if highbits_coeff r alpha <> highbits_coeff (r + z) alpha then 1 else 0

(** UseHint: recover high bits using hint *)
let usehint_coeff h r alpha =
  let (r1, r0) = decompose_coeff r alpha in
  let m = (dil_ntt_q - 1) / alpha in
  if h = 0 then r1
  else if r0 > 0 then (r1 + 1) mod (m + 1)
  else ((r1 - 1 + m + 1) mod (m + 1))

(** MakeHint on polynomial *)
let makehint_poly z r alpha =
  List.map2 (fun zc rc -> makehint_coeff zc rc alpha) z r

(** UseHint on polynomial *)
let usehint_poly h r alpha =
  List.map2 (fun hc rc -> usehint_coeff hc rc alpha) h r

(** MakeHint on vector *)
let makehint_vec z_vec r_vec alpha =
  List.map2 (fun z r -> makehint_poly z r alpha) z_vec r_vec

(** UseHint on vector *)
let usehint_vec h_vec r_vec alpha =
  List.map2 (fun h r -> usehint_poly h r alpha) h_vec r_vec

(** Hint weight: total number of 1s *)
let hint_weight h =
  List.fold_left (+) 0 (List.map (List.fold_left (+) 0) h)

(** Check if coefficient is in range *)
let coeff_in_range c bnd = abs c < bnd

(** Check infinity norm bound on polynomial *)
let poly_linf_bound p bnd = List.for_all (fun c -> coeff_in_range c bnd) p

(** Check infinity norm bound on vector *)
let vec_linf_bound v bnd = List.for_all (fun p -> poly_linf_bound p bnd) v

(** Check z bound for signing *)
let check_z_bound params z =
  vec_linf_bound z (params.dil_gamma1 - params.dil_beta)

(** Check low bits bound for signing *)
let check_lowbits_bound params r0 =
  vec_linf_bound r0 (params.dil_gamma2 - params.dil_beta)

(** Check ct0 bound for signing *)
let check_ct0_bound params ct0 =
  vec_linf_bound ct0 params.dil_gamma2

(** Valid challenge polynomial: tau coefficients in {-1, 0, 1} *)
let valid_challenge c tau =
  List.length c = 256 &&
  List.for_all (fun coeff -> coeff = -1 || coeff = 0 || coeff = 1) c &&
  List.length (List.filter (fun x -> x <> 0) c) = tau

(** Challenge weight: number of non-zero coefficients *)
let challenge_weight c = List.length (List.filter (fun x -> x <> 0) c)

(** Validate Dilithium parameters *)
let valid_dilithium_params p =
  p.dil_n = 256 &&
  p.dil_q = 8380417 &&
  p.dil_k > 0 && p.dil_k <= 8 &&
  p.dil_l > 0 && p.dil_l <= 7 &&
  p.dil_eta > 0 &&
  p.dil_tau > 0 &&
  p.dil_beta = p.dil_tau * p.dil_eta &&
  p.dil_gamma1 > 0 &&
  p.dil_gamma2 > 0 &&
  p.dil_d > 0 && p.dil_d <= 13 &&
  p.dil_omega > 0
