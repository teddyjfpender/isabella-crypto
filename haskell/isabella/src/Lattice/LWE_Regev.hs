{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Lattice.LWE_Regev(Int, Num, Lwe_ciphertext_ext, Lwe_public_key_ext,
                     Lwe_secret_key_ext, transpose, vec_add, vec_mod,
                     decode_bit, encode_bit, inner_prod, lwe_decrypt,
                     mat_vec_mult, mat_transpose_vec_mult, lwe_encrypt)
  where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import Data.Bits ((.&.), (.|.), (.^.));
import qualified Prelude;
import qualified Data.Bits;

newtype Int = Int_of_integer Integer;

integer_of_int :: Int -> Integer;
integer_of_int (Int_of_integer k) = k;

plus_int :: Int -> Int -> Int;
plus_int k l = Int_of_integer (integer_of_int k + integer_of_int l);

class Plus a where {
  plus :: a -> a -> a;
};

instance Plus Int where {
  plus = plus_int;
};

zero_int :: Int;
zero_int = Int_of_integer (0 :: Integer);

class Zero a where {
  zero :: a;
};

instance Zero Int where {
  zero = zero_int;
};

class (Plus a) => Semigroup_add a where {
};

class (Semigroup_add a, Zero a) => Monoid_add a where {
};

instance Semigroup_add Int where {
};

instance Monoid_add Int where {
};

data Num = One | Bit0 Num | Bit1 Num;

data Lwe_ciphertext_ext a = Lwe_ciphertext_ext [Int] Int a;

data Lwe_public_key_ext a = Lwe_public_key_ext [[Int]] [Int] a;

data Lwe_secret_key_ext a = Lwe_secret_key_ext [Int] a;

foldr :: forall a b. (a -> b -> b) -> [a] -> b -> b;
foldr f [] = id;
foldr f (x : xs) = f x . foldr f xs;

transpose :: forall a. [[a]] -> [[a]];
transpose [] = [];
transpose ([] : xss) = transpose xss;
transpose ((x : xs) : xss) =
  (x : concatMap (\ a -> (case a of {
                           [] -> [];
                           h : _ -> [h];
                         }))
         xss) :
    transpose (xs : concatMap (\ a -> (case a of {
[] -> [];
_ : t -> [t];
                                      }))
                      xss);

apsnd :: forall a b c. (a -> b) -> (c, a) -> (c, b);
apsnd f (x, y) = (x, f y);

vec_add :: [Int] -> [Int] -> [Int];
vec_add xs ys = map (\ (a, b) -> plus_int a b) (zip xs ys);

divmod_integer :: Integer -> Integer -> (Integer, Integer);
divmod_integer k l =
  (if k == (0 :: Integer) then ((0 :: Integer), (0 :: Integer))
    else (if (0 :: Integer) < l
           then (if (0 :: Integer) < k then divMod (abs k) (abs l)
                  else (case divMod (abs k) (abs l) of {
                         (r, s) ->
                           (if s == (0 :: Integer)
                             then (negate r, (0 :: Integer))
                             else (negate r - (1 :: Integer), l - s));
                       }))
           else (if l == (0 :: Integer) then ((0 :: Integer), k)
                  else apsnd negate
                         (if k < (0 :: Integer) then divMod (abs k) (abs l)
                           else (case divMod (abs k) (abs l) of {
                                  (r, s) ->
                                    (if s == (0 :: Integer)
                                      then (negate r, (0 :: Integer))
                                      else (negate r - (1 :: Integer),
     negate l - s));
                                })))));

modulo_integer :: Integer -> Integer -> Integer;
modulo_integer k l = snd (divmod_integer k l);

modulo_int :: Int -> Int -> Int;
modulo_int k l =
  Int_of_integer (modulo_integer (integer_of_int k) (integer_of_int l));

vec_mod :: [Int] -> Int -> [Int];
vec_mod v q = map (\ x -> modulo_int x q) v;

divide_integer :: Integer -> Integer -> Integer;
divide_integer k l = fst (divmod_integer k l);

divide_int :: Int -> Int -> Int;
divide_int k l =
  Int_of_integer (divide_integer (integer_of_int k) (integer_of_int l));

less_eq_int :: Int -> Int -> Bool;
less_eq_int k l = integer_of_int k <= integer_of_int l;

decode_bit :: Int -> Int -> Bool;
decode_bit q d = less_eq_int (divide_int q (Int_of_integer (2 :: Integer))) d;

encode_bit :: Int -> Bool -> Int;
encode_bit q b =
  (if b then divide_int q (Int_of_integer (2 :: Integer)) else zero_int);

sum_list :: forall a. (Monoid_add a) => [a] -> a;
sum_list xs = foldr plus xs zero;

times_int :: Int -> Int -> Int;
times_int k l = Int_of_integer (integer_of_int k * integer_of_int l);

inner_prod :: [Int] -> [Int] -> Int;
inner_prod u v = sum_list (map (\ (a, b) -> times_int a b) (zip u v));

sk_s :: forall a. Lwe_secret_key_ext a -> [Int];
sk_s (Lwe_secret_key_ext sk_s more) = sk_s;

ct_v :: forall a. Lwe_ciphertext_ext a -> Int;
ct_v (Lwe_ciphertext_ext ct_u ct_v more) = ct_v;

ct_u :: forall a. Lwe_ciphertext_ext a -> [Int];
ct_u (Lwe_ciphertext_ext ct_u ct_v more) = ct_u;

minus_int :: Int -> Int -> Int;
minus_int k l = Int_of_integer (integer_of_int k - integer_of_int l);

lwe_decrypt :: Lwe_secret_key_ext () -> Int -> Lwe_ciphertext_ext () -> Bool;
lwe_decrypt sk q ct =
  let {
    a = modulo_int (minus_int (ct_v ct) (inner_prod (sk_s sk) (ct_u ct))) q;
  } in decode_bit q a;

mat_vec_mult :: [[Int]] -> [Int] -> [Int];
mat_vec_mult a x = map (\ row -> inner_prod row x) a;

mat_transpose_vec_mult :: [[Int]] -> [Int] -> [Int];
mat_transpose_vec_mult a r = mat_vec_mult (transpose a) r;

pk_b :: forall a. Lwe_public_key_ext a -> [Int];
pk_b (Lwe_public_key_ext pk_A pk_b more) = pk_b;

pk_A :: forall a. Lwe_public_key_ext a -> [[Int]];
pk_A (Lwe_public_key_ext pk_A pk_b more) = pk_A;

lwe_encrypt ::
  Lwe_public_key_ext () -> Int -> [Int] -> Bool -> Lwe_ciphertext_ext ();
lwe_encrypt pk q r m =
  let {
    u = vec_mod (mat_transpose_vec_mult (pk_A pk) r) q;
    v = modulo_int (plus_int (inner_prod (pk_b pk) r) (encode_bit q m)) q;
  } in Lwe_ciphertext_ext u v ();

}
