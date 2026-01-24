module LWE_Regev : sig
  type int
  type num
  type 'a lwe_ciphertext_ext
  type 'a lwe_public_key_ext
  type 'a lwe_secret_key_ext
  val transpose : ('a list) list -> ('a list) list
  val vec_add : int list -> int list -> int list
  val vec_mod : int list -> int -> int list
  val decode_bit : int -> int -> bool
  val encode_bit : int -> bool -> int
  val inner_prod : int list -> int list -> int
  val lwe_decrypt :
    unit lwe_secret_key_ext -> int -> unit lwe_ciphertext_ext -> bool
  val mat_vec_mult : (int list) list -> int list -> int list
  val mat_transpose_vec_mult : (int list) list -> int list -> int list
  val lwe_encrypt :
    unit lwe_public_key_ext ->
      int -> int list -> bool -> unit lwe_ciphertext_ext
end = struct

type int = Int_of_integer of Z.t;;

let rec integer_of_int (Int_of_integer k) = k;;

let rec plus_inta
  k l = Int_of_integer (Z.add (integer_of_int k) (integer_of_int l));;

type 'a plus = {plus : 'a -> 'a -> 'a};;
let plus _A = _A.plus;;

let plus_int = ({plus = plus_inta} : int plus);;

let zero_inta : int = Int_of_integer Z.zero;;

type 'a zero = {zero : 'a};;
let zero _A = _A.zero;;

let zero_int = ({zero = zero_inta} : int zero);;

type 'a semigroup_add = {plus_semigroup_add : 'a plus};;

type 'a monoid_add =
  {semigroup_add_monoid_add : 'a semigroup_add; zero_monoid_add : 'a zero};;

let semigroup_add_int = ({plus_semigroup_add = plus_int} : int semigroup_add);;

let monoid_add_int =
  ({semigroup_add_monoid_add = semigroup_add_int; zero_monoid_add = zero_int} :
    int monoid_add);;

type num = One | Bit0 of num | Bit1 of num;;

type 'a lwe_ciphertext_ext = Lwe_ciphertext_ext of int list * int * 'a;;

type 'a lwe_public_key_ext =
  Lwe_public_key_ext of (int list) list * int list * 'a;;

type 'a lwe_secret_key_ext = Lwe_secret_key_ext of int list * 'a;;

let rec id x = (fun xa -> xa) x;;

let rec comp f g = (fun x -> f (g x));;

let rec zip xs ys = match xs, ys with [], ys -> []
              | xs, [] -> []
              | x :: xs, y :: ys -> (x, y) :: zip xs ys;;

let rec maps f x1 = match f, x1 with f, [] -> []
               | f, x :: xs -> f x @ maps f xs;;

let rec foldr f x1 = match f, x1 with f, [] -> id
                | f, x :: xs -> comp (f x) (foldr f xs);;

let rec map f x1 = match f, x1 with f, [] -> []
              | f, x21 :: x22 -> f x21 :: map f x22;;

let rec transpose
  = function [] -> []
    | [] :: xss -> transpose xss
    | (x :: xs) :: xss ->
        (x :: maps (fun a -> (match a with [] -> [] | h :: _ -> [h])) xss) ::
          transpose
            (xs ::
              maps (fun a -> (match a with [] -> [] | _ :: t -> [t])) xss);;

let rec apsnd f (x, y) = (x, f y);;

let rec vec_add xs ys = map (fun (a, b) -> plus_inta a b) (zip xs ys);;

let rec divmod_integer
  k l = (if Z.equal k Z.zero then (Z.zero, Z.zero)
          else (if Z.lt Z.zero l
                 then (if Z.lt Z.zero k
                        then (fun k l -> if Z.equal Z.zero l then
                               (Z.zero, l) else Z.div_rem (Z.abs k) (Z.abs l))
                               k l
                        else (let (r, s) =
                                (fun k l -> if Z.equal Z.zero l then
                                  (Z.zero, l) else Z.div_rem (Z.abs k)
                                  (Z.abs l))
                                  k l
                                in
                               (if Z.equal s Z.zero then (Z.neg r, Z.zero)
                                 else (Z.sub (Z.neg r) (Z.of_int 1),
Z.sub l s))))
                 else (if Z.equal l Z.zero then (Z.zero, k)
                        else apsnd Z.neg
                               (if Z.lt k Z.zero
                                 then (fun k l -> if Z.equal Z.zero l then
(Z.zero, l) else Z.div_rem (Z.abs k) (Z.abs l))
k l
                                 else (let (r, s) =
 (fun k l -> if Z.equal Z.zero l then (Z.zero, l) else Z.div_rem (Z.abs k)
   (Z.abs l))
   k l
 in
(if Z.equal s Z.zero then (Z.neg r, Z.zero)
  else (Z.sub (Z.neg r) (Z.of_int 1), Z.sub (Z.neg l) s)))))));;

let rec snd (x1, x2) = x2;;

let rec modulo_integer k l = snd (divmod_integer k l);;

let rec modulo_int
  k l = Int_of_integer (modulo_integer (integer_of_int k) (integer_of_int l));;

let rec vec_mod v q = map (fun x -> modulo_int x q) v;;

let rec fst (x1, x2) = x1;;

let rec divide_integer k l = fst (divmod_integer k l);;

let rec divide_int
  k l = Int_of_integer (divide_integer (integer_of_int k) (integer_of_int l));;

let rec less_eq_int k l = Z.leq (integer_of_int k) (integer_of_int l);;

let rec decode_bit
  q d = less_eq_int (divide_int q (Int_of_integer (Z.of_int 2))) d;;

let rec encode_bit
  q b = (if b then divide_int q (Int_of_integer (Z.of_int 2)) else zero_inta);;

let rec sum_list _A
  xs = foldr (plus _A.semigroup_add_monoid_add.plus_semigroup_add) xs
         (zero _A.zero_monoid_add);;

let rec times_int
  k l = Int_of_integer (Z.mul (integer_of_int k) (integer_of_int l));;

let rec inner_prod
  u v = sum_list monoid_add_int (map (fun (a, b) -> times_int a b) (zip u v));;

let rec sk_s (Lwe_secret_key_ext (sk_s, more)) = sk_s;;

let rec ct_v (Lwe_ciphertext_ext (ct_u, ct_v, more)) = ct_v;;

let rec ct_u (Lwe_ciphertext_ext (ct_u, ct_v, more)) = ct_u;;

let rec minus_int
  k l = Int_of_integer (Z.sub (integer_of_int k) (integer_of_int l));;

let rec lwe_decrypt
  sk q ct =
    (let a = modulo_int (minus_int (ct_v ct) (inner_prod (sk_s sk) (ct_u ct))) q
       in
      decode_bit q a);;

let rec mat_vec_mult a x = map (fun row -> inner_prod row x) a;;

let rec mat_transpose_vec_mult a r = mat_vec_mult (transpose a) r;;

let rec pk_b (Lwe_public_key_ext (pk_A, pk_b, more)) = pk_b;;

let rec pk_A (Lwe_public_key_ext (pk_A, pk_b, more)) = pk_A;;

let rec lwe_encrypt
  pk q r m =
    (let u = vec_mod (mat_transpose_vec_mult (pk_A pk) r) q in
     let v = modulo_int (plus_inta (inner_prod (pk_b pk) r) (encode_bit q m)) q
       in
      Lwe_ciphertext_ext (u, v, ()));;

end;; (*struct LWE_Regev*)
