theory LatticeCrypto
  imports Main "HOL-Library.Code_Target_Numeral"
begin

type_synonym int_vec = "int list"
type_synonym int_matrix = "int list list"

definition dot :: "int_vec => int_vec => int" where
  "dot v w = sum_list (map2 (*) v w)"

definition mat_vec_mult :: "int_matrix => int_vec => int_vec" where
  "mat_vec_mult A v = map (%row. dot row v) A"

definition transpose :: "int_matrix => int_matrix" where
  "transpose A =
     (let m = length A;
          n = (if m = 0 then 0 else length (hd A))
      in map (%j. map (%i. (A ! i) ! j) [0..<m]) [0..<n])"

record lwe_params =
  lwe_n :: nat
  lwe_q :: int

record lwe_secret_key =
  lwe_s :: int_vec

record lwe_public_key =
  lwe_A :: int_matrix
  lwe_b :: int_vec

definition encode_bit :: "lwe_params => bool => int" where
  "encode_bit params m = (if m then lwe_q params div 2 else 0)"

definition decode_bit :: "lwe_params => int => bool" where
  "decode_bit params v = (abs (v - lwe_q params div 2) < lwe_q params div 4)"

definition lwe_encrypt :: "lwe_public_key => lwe_params => bool => int_vec => (int_vec * int)" where
  "lwe_encrypt pk params m r =
     (let u = mat_vec_mult (transpose (lwe_A pk)) r;
          v = dot (lwe_b pk) r + encode_bit params m
      in (u, v))"

definition lwe_decrypt :: "lwe_secret_key => lwe_params => (int_vec * int) => bool" where
  "lwe_decrypt sk params ct =
     (let u = fst ct;
          v = snd ct;
          d = v - dot (lwe_s sk) u
      in decode_bit params d)"

definition lwe_correctness_condition ::
  "lwe_params => lwe_public_key => lwe_secret_key => int_vec => bool => bool" where
  "lwe_correctness_condition params pk sk r m =
     (lwe_decrypt sk params (lwe_encrypt pk params m r) = m)"

lemma lwe_correctness_condition_lemma:
  assumes "lwe_correctness_condition params pk sk r m"
  shows "lwe_decrypt sk params (lwe_encrypt pk params m r) = m"
  using assms unfolding lwe_correctness_condition_def by simp

export_code
  dot mat_vec_mult transpose
  encode_bit decode_bit
  lwe_encrypt lwe_decrypt
  lwe_correctness_condition
  lwe_params.make lwe_n lwe_q
  lwe_secret_key.make lwe_s
  lwe_public_key.make lwe_A lwe_b
  in Haskell module_name "Lattice.LWE"

end
