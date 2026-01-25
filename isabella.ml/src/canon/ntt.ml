(** Number Theoretic Transform (NTT)
    Generated from Canon/Rings/NTT.thy

    Provides O(n log n) NTT operations for polynomial multiplication
    in lattice cryptography (Kyber, Dilithium). *)

(** NTT parameters *)
type ntt_params = {
  ntt_n : int;      (** Polynomial degree (power of 2) *)
  ntt_q : int;      (** Modulus *)
  ntt_omega : int;  (** Primitive n-th root of unity mod q *)
}

(** Create NTT parameters *)
let make_ntt_params n q omega = { ntt_n = n; ntt_q = q; ntt_omega = omega }

(** Modular exponentiation: a^k mod m *)
let rec power_mod a k m =
  if k = 0 then 1 mod m
  else if k mod 2 = 0 then
    power_mod ((a * a) mod m) (k / 2) m
  else
    (a * power_mod a (k - 1) m) mod m

(** Extended Euclidean algorithm *)
let rec extended_gcd a b =
  if b = 0 then (a, 1, 0)
  else
    let (g, x, y) = extended_gcd b (a mod b) in
    (g, y, x - (a / b) * y)

(** Modular multiplicative inverse *)
let mod_inverse a m =
  let (_, x, _) = extended_gcd a m in
  ((x mod m) + m) mod m

(** Check if omega is a primitive n-th root of unity mod q *)
let is_primitive_root omega n q =
  power_mod omega n q = 1 &&
  List.for_all (fun k -> power_mod omega k q <> 1) (List.init (n - 1) (fun i -> i + 1))

(** Validate NTT parameters *)
let valid_ntt_params params =
  params.ntt_n > 0 &&
  params.ntt_q > 1 &&
  is_primitive_root params.ntt_omega params.ntt_n params.ntt_q

(** Twiddle factor: omega^k mod q *)
let twiddle omega k q = power_mod omega k q

(** Precompute all twiddle factors *)
let twiddle_factors omega n q =
  List.init n (fun k -> twiddle omega k q)

(** Single NTT coefficient *)
let ntt_coeff a omega q k =
  let terms = List.mapi (fun i ai -> (ai * twiddle omega (k * i) q) mod q) a in
  List.fold_left (fun acc x -> (acc + x) mod q) 0 terms

(** Naive NTT: O(n^2) *)
let ntt_naive a omega q =
  let n = List.length a in
  List.init n (fun k -> ntt_coeff a omega q k)

(** Single INTT coefficient *)
let intt_coeff a_hat omega q k =
  let n = List.length a_hat in
  let omega_inv = mod_inverse omega q in
  let terms = List.mapi (fun i ai -> (ai * twiddle omega_inv (k * i) q) mod q) a_hat in
  let sum_val = List.fold_left (fun acc x -> (acc + x) mod q) 0 terms in
  let n_inv = mod_inverse n q in
  (sum_val * n_inv) mod q

(** Naive inverse NTT: O(n^2) *)
let intt_naive a_hat omega q =
  let n = List.length a_hat in
  List.init n (fun k -> intt_coeff a_hat omega q k)

(** Butterfly operation *)
let butterfly u v tw q =
  let t = (v * tw) mod q in
  let u' = (u + t) mod q in
  let v' = ((u - t) mod q + q) mod q in
  (u', v')

(** Replace element at index in list *)
let replace_at idx value lst =
  List.mapi (fun i x -> if i = idx then value else x) lst

(** Bit reversal of index *)
let bit_reverse i log_n =
  let rec aux acc b =
    if b >= log_n then acc
    else
      let new_acc = if (i lsr b) land 1 = 1 then acc lor (1 lsl (log_n - 1 - b)) else acc in
      aux new_acc (b + 1)
  in aux 0 0

(** Bit-reversal permutation *)
let bit_reverse_copy a n =
  let log_n = int_of_float (log (float_of_int n) /. log 2.0) in
  List.init n (fun i -> List.nth a (bit_reverse i log_n))

(** Fast NTT using Cooley-Tukey: O(n log n) *)
let ntt_fast a omega q n =
  if List.length a <> n then failwith "ntt_fast: input length must equal n"
  else
    let a_br = bit_reverse_copy a n in
    let rec outer_loop arr len =
      if len >= n then arr
      else
        let wlen = power_mod omega (n / (2 * len)) q in
        let rec inner_loop arr' group =
          if group >= n / (2 * len) then arr'
          else
            let start = group * 2 * len in
            let rec butterfly_loop arr'' j =
              if j >= len then arr''
              else
                let w = power_mod wlen j q in
                let idx_u = start + j in
                let idx_v = start + j + len in
                let u = List.nth arr'' idx_u in
                let v = List.nth arr'' idx_v in
                let t = (v * w) mod q in
                let u' = (u + t) mod q in
                let v' = ((u - t) mod q + q) mod q in
                let arr''' = replace_at idx_u u' (replace_at idx_v v' arr'') in
                butterfly_loop arr''' (j + 1)
            in
            inner_loop (butterfly_loop arr' 0) (group + 1)
        in
        outer_loop (inner_loop arr 0) (len * 2)
    in
    outer_loop a_br 1

(** Fast inverse NTT: O(n log n) *)
let intt_fast a_hat omega q n =
  let omega_inv = mod_inverse omega q in
  let n_inv = mod_inverse n q in
  let result = ntt_fast a_hat omega_inv q n in
  List.map (fun x -> (x * n_inv) mod q) result

(** Pointwise multiplication in NTT domain *)
let ntt_pointwise_mult a_hat b_hat q =
  List.map2 (fun x y -> (x * y) mod q) a_hat b_hat

(** Kyber NTT parameters: n=256, q=3329, omega=17 *)
let kyber_ntt_params = { ntt_n = 256; ntt_q = 3329; ntt_omega = 17 }

(** Dilithium NTT parameters: n=256, q=8380417, omega=1753 *)
let dilithium_ntt_params = { ntt_n = 256; ntt_q = 8380417; ntt_omega = 1753 }
