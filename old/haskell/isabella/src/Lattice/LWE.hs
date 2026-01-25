{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Lattice.LWE(Int(..), Nat, Num(..), Lwe_params_ext, Lwe_public_key_ext(..),
               Lwe_secret_key_ext(..), dot, transpose, lwe_q, decode_bit,
               encode_bit, lwe_s, lwe_decrypt, lwe_b, lwe_A, mat_vec_mult,
               lwe_encrypt, make, lwe_n, makea, makeb,
               lwe_correctness_condition)
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

class Ord a where {
  less_eq :: a -> a -> Bool;
  less :: a -> a -> Bool;
};

instance Ord Integer where {
  less_eq = (\ a b -> a <= b);
  less = (\ a b -> a < b);
};

newtype Nat = Nat Integer;

data Num = One | Bit0 Num | Bit1 Num;

data Lwe_params_ext a = Lwe_params_ext Nat Int a;

data Lwe_public_key_ext a = Lwe_public_key_ext [[Int]] [Int] a;

data Lwe_secret_key_ext a = Lwe_secret_key_ext [Int] a;

integer_of_nat :: Nat -> Integer;
integer_of_nat (Nat x) = x;

plus_nat :: Nat -> Nat -> Nat;
plus_nat m n = Nat (integer_of_nat m + integer_of_nat n);

one_nat :: Nat;
one_nat = Nat (1 :: Integer);

suc :: Nat -> Nat;
suc n = plus_nat n one_nat;

max :: forall a. (Ord a) => a -> a -> a;
max a b = (if less_eq a b then b else a);

minus_nat :: Nat -> Nat -> Nat;
minus_nat m n = Nat (max (0 :: Integer) (integer_of_nat m - integer_of_nat n));

equal_nat :: Nat -> Nat -> Bool;
equal_nat m n = integer_of_nat m == integer_of_nat n;

zero_nat :: Nat;
zero_nat = Nat (0 :: Integer);

nth :: forall a. [a] -> Nat -> a;
nth (x : xs) n =
  (if equal_nat n zero_nat then x else nth xs (minus_nat n one_nat));

less_nat :: Nat -> Nat -> Bool;
less_nat m n = integer_of_nat m < integer_of_nat n;

upt :: Nat -> Nat -> [Nat];
upt i j = (if less_nat i j then i : upt (suc i) j else []);

foldr :: forall a b. (a -> b -> b) -> [a] -> b -> b;
foldr f [] = id;
foldr f (x : xs) = f x . foldr f xs;

hd :: forall a. [a] -> a;
hd (x21 : x22) = x21;

sum_list :: forall a. (Monoid_add a) => [a] -> a;
sum_list xs = foldr plus xs zero;

times_int :: Int -> Int -> Int;
times_int k l = Int_of_integer (integer_of_int k * integer_of_int l);

dot :: [Int] -> [Int] -> Int;
dot v w = sum_list (map (\ (a, b) -> times_int a b) (zip v w));

apsnd :: forall a b c. (a -> b) -> (c, a) -> (c, b);
apsnd f (x, y) = (x, f y);

length_tailrec :: forall a. [a] -> Nat -> Nat;
length_tailrec [] n = n;
length_tailrec (x : xs) n = length_tailrec xs (suc n);

size_list :: forall a. [a] -> Nat;
size_list xs = length_tailrec xs zero_nat;

transpose :: [[Int]] -> [[Int]];
transpose a =
  let {
    m = size_list a;
    n = (if equal_nat m zero_nat then zero_nat else size_list (hd a));
  } in map (\ j -> map (\ i -> nth (nth a i) j) (upt zero_nat m))
         (upt zero_nat n);

uminus_int :: Int -> Int;
uminus_int k = Int_of_integer (negate (integer_of_int k));

less_int :: Int -> Int -> Bool;
less_int k l = integer_of_int k < integer_of_int l;

abs_int :: Int -> Int;
abs_int i = (if less_int i zero_int then uminus_int i else i);

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
  less_int
    (abs_int
      (minus_int v (divide_int (lwe_q params) (Int_of_integer (2 :: Integer)))))
    (divide_int (lwe_q params) (Int_of_integer (4 :: Integer)));

encode_bit :: Lwe_params_ext () -> Bool -> Int;
encode_bit params m =
  (if m then divide_int (lwe_q params) (Int_of_integer (2 :: Integer))
    else zero_int);

lwe_s :: forall a. Lwe_secret_key_ext a -> [Int];
lwe_s (Lwe_secret_key_ext lwe_s more) = lwe_s;

lwe_decrypt ::
  Lwe_secret_key_ext () -> Lwe_params_ext () -> ([Int], Int) -> Bool;
lwe_decrypt sk params ct = let {
                             u = fst ct;
                             v = snd ct;
                             a = minus_int v (dot (lwe_s sk) u);
                           } in decode_bit params a;

lwe_b :: forall a. Lwe_public_key_ext a -> [Int];
lwe_b (Lwe_public_key_ext lwe_A lwe_b more) = lwe_b;

lwe_A :: forall a. Lwe_public_key_ext a -> [[Int]];
lwe_A (Lwe_public_key_ext lwe_A lwe_b more) = lwe_A;

mat_vec_mult :: [[Int]] -> [Int] -> [Int];
mat_vec_mult a v = map (\ row -> dot row v) a;

lwe_encrypt ::
  Lwe_public_key_ext () -> Lwe_params_ext () -> Bool -> [Int] -> ([Int], Int);
lwe_encrypt pk params m r =
  let {
    u = mat_vec_mult (transpose (lwe_A pk)) r;
    a = plus_int (dot (lwe_b pk) r) (encode_bit params m);
  } in (u, a);

make :: Nat -> Int -> Lwe_params_ext ();
make lwe_n lwe_q = Lwe_params_ext lwe_n lwe_q ();

lwe_n :: forall a. Lwe_params_ext a -> Nat;
lwe_n (Lwe_params_ext lwe_n lwe_q more) = lwe_n;

makea :: [[Int]] -> [Int] -> Lwe_public_key_ext ();
makea lwe_A lwe_b = Lwe_public_key_ext lwe_A lwe_b ();

makeb :: [Int] -> Lwe_secret_key_ext ();
makeb lwe_s = Lwe_secret_key_ext lwe_s ();

lwe_correctness_condition ::
  Lwe_params_ext () ->
    Lwe_public_key_ext () -> Lwe_secret_key_ext () -> [Int] -> Bool -> Bool;
lwe_correctness_condition params pk sk r m =
  lwe_decrypt sk params (lwe_encrypt pk params m r) == m;

}
