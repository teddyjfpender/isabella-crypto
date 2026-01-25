(** Regev public-key encryption scheme
    Generated from Canon/Crypto/Regev_PKE.thy *)

type regev_params = {
  regev_lwe : Lwe_def.lwe_params;
  regev_Br : int;
}

let make_regev_params n m q bs be br =
  { regev_lwe = Lwe_def.make_lwe_params n m q bs be; regev_Br = br }

let valid_regev_params p =
  p.regev_lwe.lwe_n > 0 &&
  p.regev_lwe.lwe_m > 0 &&
  p.regev_lwe.lwe_q > 1 &&
  p.regev_lwe.lwe_Bs >= 0 &&
  p.regev_lwe.lwe_Be >= 0 &&
  p.regev_Br >= 0

type regev_pk = int list list * int list
type regev_sk = int list
type regev_ct = int list * int

let valid_pk p (a, b) =
  Listvec.valid_matrix p.regev_lwe.lwe_m p.regev_lwe.lwe_n a &&
  Listvec.valid_vec p.regev_lwe.lwe_m b

let valid_sk p sk = Listvec.valid_vec p.regev_lwe.lwe_n sk

let valid_ct p (c1, _) = Listvec.valid_vec p.regev_lwe.lwe_n c1

let valid_randomness p r =
  Listvec.valid_vec p.regev_lwe.lwe_m r &&
  Norms.all_bounded r p.regev_Br

let regev_keygen a s e q = ((a, Lwe_def.lwe_sample a s e q), s)

let regev_encrypt (a, b) r m q =
  let c1 = Zq.vec_mod (Listvec.mat_vec_mult (Listvec.transpose a) r) q in
  let c2 = (Listvec.inner_prod b r + Zq.encode_bit q m) mod q in
  (c1, c2)

let decrypt_payload s (c1, c2) q =
  ((c2 - Listvec.inner_prod s c1) mod q + q) mod q

let regev_decrypt s ct q = Zq.decode_bit q (decrypt_payload s ct q)
