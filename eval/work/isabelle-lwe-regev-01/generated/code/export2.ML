structure LWE_Regev : sig
  type int
  type num
  type 'a lwe_ciphertext_ext
  type 'a lwe_public_key_ext
  type 'a lwe_secret_key_ext
  val transpose : ('a list) list -> ('a list) list
  val dist0 : int -> int -> int
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

datatype int = Int_of_integer of IntInf.int;

fun integer_of_int (Int_of_integer k) = k;

fun plus_inta k l =
  Int_of_integer (IntInf.+ (integer_of_int k, integer_of_int l));

type 'a plus = {plus : 'a -> 'a -> 'a};
val plus = #plus : 'a plus -> 'a -> 'a -> 'a;

val plus_int = {plus = plus_inta} : int plus;

val zero_inta : int = Int_of_integer (0 : IntInf.int);

type 'a zero = {zero : 'a};
val zero = #zero : 'a zero -> 'a;

val zero_int = {zero = zero_inta} : int zero;

type 'a semigroup_add = {plus_semigroup_add : 'a plus};
val plus_semigroup_add = #plus_semigroup_add : 'a semigroup_add -> 'a plus;

type 'a monoid_add =
  {semigroup_add_monoid_add : 'a semigroup_add, zero_monoid_add : 'a zero};
val semigroup_add_monoid_add = #semigroup_add_monoid_add :
  'a monoid_add -> 'a semigroup_add;
val zero_monoid_add = #zero_monoid_add : 'a monoid_add -> 'a zero;

val semigroup_add_int = {plus_semigroup_add = plus_int} : int semigroup_add;

val monoid_add_int =
  {semigroup_add_monoid_add = semigroup_add_int, zero_monoid_add = zero_int} :
  int monoid_add;

datatype num = One | Bit0 of num | Bit1 of num;

datatype 'a lwe_ciphertext_ext = Lwe_ciphertext_ext of int list * int * 'a;

datatype 'a lwe_public_key_ext =
  Lwe_public_key_ext of (int list) list * int list * 'a;

datatype 'a lwe_secret_key_ext = Lwe_secret_key_ext of int list * 'a;

fun id x = (fn xa => xa) x;

fun zip [] ys = []
  | zip xs [] = []
  | zip (x :: xs) (y :: ys) = (x, y) :: zip xs ys;

fun maps f [] = []
  | maps f (x :: xs) = f x @ maps f xs;

fun foldr f [] = id
  | foldr f (x :: xs) = f x o foldr f xs;

fun map f [] = []
  | map f (x21 :: x22) = f x21 :: map f x22;

fun transpose [] = []
  | transpose ([] :: xss) = transpose xss
  | transpose ((x :: xs) :: xss) =
    (x :: maps (fn a => (case a of [] => [] | h :: _ => [h])) xss) ::
      transpose (xs :: maps (fn a => (case a of [] => [] | _ :: t => [t])) xss);

fun apsnd f (x, y) = (x, f y);

fun divmod_integer k l =
  (if ((k : IntInf.int) = (0 : IntInf.int))
    then ((0 : IntInf.int), (0 : IntInf.int))
    else (if IntInf.< ((0 : IntInf.int), l)
           then (if IntInf.< ((0 : IntInf.int), k)
                  then IntInf.divMod (IntInf.abs k, IntInf.abs l)
                  else let
                         val (r, s) =
                           IntInf.divMod (IntInf.abs k, IntInf.abs l);
                       in
                         (if ((s : IntInf.int) = (0 : IntInf.int))
                           then (IntInf.~ r, (0 : IntInf.int))
                           else (IntInf.- (IntInf.~ r, (1 : IntInf.int)),
                                  IntInf.- (l, s)))
                       end)
           else (if ((l : IntInf.int) = (0 : IntInf.int))
                  then ((0 : IntInf.int), k)
                  else apsnd IntInf.~
                         (if IntInf.< (k, (0 : IntInf.int))
                           then IntInf.divMod (IntInf.abs k, IntInf.abs l)
                           else let
                                  val (r, s) =
                                    IntInf.divMod (IntInf.abs k, IntInf.abs l);
                                in
                                  (if ((s : IntInf.int) = (0 : IntInf.int))
                                    then (IntInf.~ r, (0 : IntInf.int))
                                    else (IntInf.- (IntInf.~
              r, (1 : IntInf.int)),
   IntInf.- (IntInf.~ l, s)))
                                end))));

fun snd (x1, x2) = x2;

fun modulo_integer k l = snd (divmod_integer k l);

fun modulo_int k l =
  Int_of_integer (modulo_integer (integer_of_int k) (integer_of_int l));

fun fst (x1, x2) = x1;

fun divide_integer k l = fst (divmod_integer k l);

fun divide_int k l =
  Int_of_integer (divide_integer (integer_of_int k) (integer_of_int l));

fun minus_int k l =
  Int_of_integer (IntInf.- (integer_of_int k, integer_of_int l));

fun less_int k l = IntInf.< (integer_of_int k, integer_of_int l);

fun dist0 q d =
  let
    val da = modulo_int d q;
  in
    (if less_int (divide_int q (Int_of_integer (2 : IntInf.int))) da
      then minus_int q da else da)
  end;

fun vec_add xs ys = map (fn (a, b) => plus_inta a b) (zip xs ys);

fun vec_mod v q = map (fn x => modulo_int x q) v;

fun decode_bit q d =
  less_int (divide_int q (Int_of_integer (4 : IntInf.int))) (dist0 q d);

fun encode_bit q b =
  (if b then divide_int q (Int_of_integer (2 : IntInf.int)) else zero_inta);

fun sum_list A_ xs =
  foldr (plus ((plus_semigroup_add o semigroup_add_monoid_add) A_)) xs
    (zero (zero_monoid_add A_));

fun times_int k l =
  Int_of_integer (IntInf.* (integer_of_int k, integer_of_int l));

fun inner_prod u v =
  sum_list monoid_add_int (map (fn (a, b) => times_int a b) (zip u v));

fun sk_s (Lwe_secret_key_ext (sk_s, more)) = sk_s;

fun ct_v (Lwe_ciphertext_ext (ct_u, ct_v, more)) = ct_v;

fun ct_u (Lwe_ciphertext_ext (ct_u, ct_v, more)) = ct_u;

fun lwe_decrypt sk q ct =
  let
    val a = modulo_int (minus_int (ct_v ct) (inner_prod (sk_s sk) (ct_u ct))) q;
  in
    decode_bit q a
  end;

fun mat_vec_mult a x = map (fn row => inner_prod row x) a;

fun mat_transpose_vec_mult a r = mat_vec_mult (transpose a) r;

fun pk_b (Lwe_public_key_ext (pk_A, pk_b, more)) = pk_b;

fun pk_A (Lwe_public_key_ext (pk_A, pk_b, more)) = pk_A;

fun lwe_encrypt pk q r m =
  let
    val u = vec_mod (mat_transpose_vec_mult (pk_A pk) r) q;
    val v = modulo_int (plus_inta (inner_prod (pk_b pk) r) (encode_bit q m)) q;
  in
    Lwe_ciphertext_ext (u, v, ())
  end;

end; (*struct LWE_Regev*)
