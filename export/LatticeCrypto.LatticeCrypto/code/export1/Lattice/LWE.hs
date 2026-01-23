{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Lattice.LWE(Int, Num, Lwe_params_ext, Lwe_public_key_ext, Lwe_secret_key_ext,
               decode_bit, encode_bit, lwe_decrypt, lwe_encrypt)
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

newtype Nat = Nat Integer;

data Num = One | Bit0 Num | Bit1 Num;

data Lwe_params_ext a = Lwe_params_ext Nat Int a;

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

sum_list :: forall a. (Monoid_add a) => [a] -> a;
sum_list xs = foldr plus xs zero;

times_int :: Int -> Int -> Int;
times_int k l = Int_of_integer (integer_of_int k * integer_of_int l);

vec_dot :: [Int] -> [Int] -> Int;
vec_dot v w = sum_list (map (\ (a, b) -> times_int a b) (zip v w));

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

uminus_int :: Int -> Int;
uminus_int k = Int_of_integer (negate (integer_of_int k));

less_int :: Int -> Int -> Bool;
less_int k l = integer_of_int k < integer_of_int l;

abs_int :: Int -> Int;
abs_int i = (if less_int i zero_int then uminus_int i else i);

divide_integer :: Integer -> Integer -> Integer;
divide_integer k l = fst (divmod_integer k l);

divide_int :: Int -> Int -> Int;
divide_int k l =
  Int_of_integer (divide_integer (integer_of_int k) (integer_of_int l));

lwe_q :: forall a. Lwe_params_ext a -> Int;
lwe_q (Lwe_params_ext lwe_n lwe_q more) = lwe_q;

minus_int :: Int -> Int -> Int;
minus_int k l = Int_of_integer (integer_of_int k - integer_of_int l);

decode_bit :: Lwe_params_ext () -> Int -> Bool;
decode_bit params v =
  let {
    q = lwe_q params;
    va = modulo_int v q;
  } in less_int
         (abs_int (minus_int va (divide_int q (Int_of_integer (2 :: Integer)))))
         (divide_int q (Int_of_integer (4 :: Integer)));

encode_bit :: Lwe_params_ext () -> Bool -> Int;
encode_bit params m =
  (if m then divide_int (lwe_q params) (Int_of_integer (2 :: Integer))
    else zero_int);

sk_s :: forall a. Lwe_secret_key_ext a -> [Int];
sk_s (Lwe_secret_key_ext sk_s more) = sk_s;

lwe_decrypt ::
  Lwe_params_ext () -> Lwe_secret_key_ext () -> ([Int], Int) -> Bool;
lwe_decrypt params sk ct =
  (case ct of {
    (u, v) -> let {
                q = lwe_q params;
                a = modulo_int (minus_int v (vec_dot (sk_s sk) u)) q;
              } in decode_bit params a;
  });

pk_b :: forall a. Lwe_public_key_ext a -> [Int];
pk_b (Lwe_public_key_ext pk_A pk_b more) = pk_b;

pk_A :: forall a. Lwe_public_key_ext a -> [[Int]];
pk_A (Lwe_public_key_ext pk_A pk_b more) = pk_A;

mat_vec_mult :: [[Int]] -> [Int] -> [Int];
mat_vec_mult a x = map (\ row -> vec_dot row x) a;

lwe_encrypt ::
  Lwe_params_ext () -> Lwe_public_key_ext () -> Bool -> [Int] -> ([Int], Int);
lwe_encrypt params pk m r =
  let {
    q = lwe_q params;
    u = vec_mod (mat_vec_mult (transpose (pk_A pk)) r) q;
    a = modulo_int (plus_int (vec_dot (pk_b pk) r) (encode_bit params m)) q;
  } in (u, a);

}
