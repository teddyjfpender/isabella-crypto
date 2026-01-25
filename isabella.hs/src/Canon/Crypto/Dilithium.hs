{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Canon.Crypto.Dilithium(Int, Num, Nat, Set, Dil_pk_ext, Dil_sk_ext,
                          Dil_signature_ext, Dil_sign_state_ext,
                          Dilithium_params_ext, dil_ntt_omega, dil_ntt_q,
                          dil_ntt, dil_intt, dil_gamma2, dil_poly_mult_ntt,
                          dil_poly_add, dil_mat_vec_mult_ntt,
                          challenge_vec_mult, mod_centered, decompose_coeff,
                          highbits_coeff, makehint_coeff, makehint_poly,
                          makehint_vec, highbits_poly, highbits_vec,
                          dil_vec_intt, sk_t0, sk_s2, sk_s1, lowbits_coeff,
                          lowbits_poly, lowbits_vec, dil_poly_sub, dil_vec_sub,
                          dil_vec_ntt, dil_vec_add, dil_sign_compute, dil_omega,
                          dil_beta, poly_linf_bound, vec_linf_bound,
                          check_lowbits_bound, check_ct0_bound, dil_gamma1,
                          check_z_bound, hint_weight, dil_sign_accept, dil_sign,
                          dil_d, power2round_coeff, power2round_poly,
                          power2round_vec, dil_keygen, sig_z, sig_h, pk_t1,
                          usehint_coeff, usehint_poly, usehint_vec, dil_verify,
                          make, makea, sk_K, sk_tr, pk_rho, sk_rho,
                          mldsa44_params, mldsa65_params, mldsa87_params,
                          valid_challenge, challenge_weight, makeb, makec,
                          dil_k, dil_l, dil_n, dil_q, dil_tau, dil_eta,
                          valid_dilithium_params, sig_c_tilde)
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

equal_int :: Int -> Int -> Bool;
equal_int k l = integer_of_int k == integer_of_int l;

instance Eq Int where {
  a == b = equal_int a b;
};

times_int :: Int -> Int -> Int;
times_int k l = Int_of_integer (integer_of_int k * integer_of_int l);

class Times a where {
  times :: a -> a -> a;
};

class (Times a) => Dvd a where {
};

instance Times Int where {
  times = times_int;
};

instance Dvd Int where {
};

data Num = One | Bit0 Num | Bit1 Num;

one_int :: Int;
one_int = Int_of_integer (1 :: Integer);

class One a where {
  one :: a;
};

instance One Int where {
  one = one_int;
};

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

class (One a, Semigroup_add a) => Numeral a where {
};

instance Semigroup_add Int where {
};

instance Numeral Int where {
};

class (One a, Times a) => Power a where {
};

instance Power Int where {
};

minus_int :: Int -> Int -> Int;
minus_int k l = Int_of_integer (integer_of_int k - integer_of_int l);

class Minus a where {
  minus :: a -> a -> a;
};

instance Minus Int where {
  minus = minus_int;
};

apsnd :: forall a b c. (a -> b) -> (c, a) -> (c, b);
apsnd f (x, y) = (x, f y);

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

class Divide a where {
  divide :: a -> a -> a;
};

instance Divide Int where {
  divide = divide_int;
};

modulo_integer :: Integer -> Integer -> Integer;
modulo_integer k l = snd (divmod_integer k l);

modulo_int :: Int -> Int -> Int;
modulo_int k l =
  Int_of_integer (modulo_integer (integer_of_int k) (integer_of_int l));

class (Divide a, Dvd a) => Modulo a where {
  modulo :: a -> a -> a;
};

instance Modulo Int where {
  modulo = modulo_int;
};

class (Semigroup_add a) => Ab_semigroup_add a where {
};

class (Semigroup_add a, Zero a) => Monoid_add a where {
};

class (Ab_semigroup_add a, Monoid_add a) => Comm_monoid_add a where {
};

class (Times a, Zero a) => Mult_zero a where {
};

class (Times a) => Semigroup_mult a where {
};

class (Ab_semigroup_add a, Semigroup_mult a) => Semiring a where {
};

class (Comm_monoid_add a, Mult_zero a, Semiring a) => Semiring_0 a where {
};

class (Semiring_0 a) => Semiring_no_zero_divisors a where {
};

class (Semigroup_mult a, Power a) => Monoid_mult a where {
};

class (Monoid_mult a, Numeral a, Semiring a) => Semiring_numeral a where {
};

class (One a, Zero a) => Zero_neq_one a where {
};

class (Semiring_numeral a, Semiring_0 a, Zero_neq_one a) => Semiring_1 a where {
};

class (Semiring_1 a,
        Semiring_no_zero_divisors a) => Semiring_1_no_zero_divisors a where {
};

class (Semigroup_add a) => Cancel_semigroup_add a where {
};

class (Ab_semigroup_add a, Cancel_semigroup_add a,
        Minus a) => Cancel_ab_semigroup_add a where {
};

class (Cancel_ab_semigroup_add a,
        Comm_monoid_add a) => Cancel_comm_monoid_add a where {
};

class (Cancel_comm_monoid_add a, Semiring_0 a) => Semiring_0_cancel a where {
};

class (Semigroup_mult a) => Ab_semigroup_mult a where {
};

class (Ab_semigroup_mult a, Semiring a) => Comm_semiring a where {
};

class (Comm_semiring a, Semiring_0 a) => Comm_semiring_0 a where {
};

class (Comm_semiring_0 a,
        Semiring_0_cancel a) => Comm_semiring_0_cancel a where {
};

class (Semiring_0_cancel a, Semiring_1 a) => Semiring_1_cancel a where {
};

class (Ab_semigroup_mult a, Monoid_mult a, Dvd a) => Comm_monoid_mult a where {
};

class (Comm_monoid_mult a, Comm_semiring_0 a,
        Semiring_1 a) => Comm_semiring_1 a where {
};

class (Comm_semiring_0_cancel a, Comm_semiring_1 a,
        Semiring_1_cancel a) => Comm_semiring_1_cancel a where {
};

class (Comm_semiring_1_cancel a,
        Semiring_1_no_zero_divisors a) => Semidom a where {
};

instance Ab_semigroup_add Int where {
};

instance Monoid_add Int where {
};

instance Comm_monoid_add Int where {
};

instance Mult_zero Int where {
};

instance Semigroup_mult Int where {
};

instance Semiring Int where {
};

instance Semiring_0 Int where {
};

instance Semiring_no_zero_divisors Int where {
};

instance Monoid_mult Int where {
};

instance Semiring_numeral Int where {
};

instance Zero_neq_one Int where {
};

instance Semiring_1 Int where {
};

instance Semiring_1_no_zero_divisors Int where {
};

instance Cancel_semigroup_add Int where {
};

instance Cancel_ab_semigroup_add Int where {
};

instance Cancel_comm_monoid_add Int where {
};

instance Semiring_0_cancel Int where {
};

instance Ab_semigroup_mult Int where {
};

instance Comm_semiring Int where {
};

instance Comm_semiring_0 Int where {
};

instance Comm_semiring_0_cancel Int where {
};

instance Semiring_1_cancel Int where {
};

instance Comm_monoid_mult Int where {
};

instance Comm_semiring_1 Int where {
};

instance Comm_semiring_1_cancel Int where {
};

instance Semidom Int where {
};

class (One a, Zero a, Divide a) => Divide_trivial a where {
};

instance Divide_trivial Int where {
};

class (Semiring_no_zero_divisors a) => Semiring_no_zero_divisors_cancel a where {
};

class (Divide_trivial a, Semidom a,
        Semiring_no_zero_divisors_cancel a) => Semidom_divide a where {
};

instance Semiring_no_zero_divisors_cancel Int where {
};

instance Semidom_divide Int where {
};

class (Comm_semiring_1_cancel a, Modulo a) => Semiring_modulo a where {
};

class (Divide_trivial a, Semiring_modulo a) => Semiring_modulo_trivial a where {
};

class (Semidom_divide a) => Algebraic_semidom a where {
};

class (Algebraic_semidom a,
        Semiring_modulo_trivial a) => Semidom_modulo a where {
};

instance Semiring_modulo Int where {
};

instance Semiring_modulo_trivial Int where {
};

instance Algebraic_semidom Int where {
};

instance Semidom_modulo Int where {
};

uminus_int :: Int -> Int;
uminus_int k = Int_of_integer (negate (integer_of_int k));

less_int :: Int -> Int -> Bool;
less_int k l = integer_of_int k < integer_of_int l;

abs_int :: Int -> Int;
abs_int i = (if less_int i zero_int then uminus_int i else i);

class Ord a where {
  less_eq :: a -> a -> Bool;
  less :: a -> a -> Bool;
};

max :: forall a. (Ord a) => a -> a -> a;
max a b = (if less_eq a b then b else a);

newtype Nat = Nat Integer;

instance Ord Integer where {
  less_eq = (\ a b -> a <= b);
  less = (\ a b -> a < b);
};

nat_of_integer :: Integer -> Nat;
nat_of_integer k = Nat (max (0 :: Integer) k);

nat :: Int -> Nat;
nat = nat_of_integer . integer_of_int;

euclidean_size_int :: Int -> Nat;
euclidean_size_int = nat . abs_int;

class (Semidom_modulo a) => Euclidean_semiring a where {
  euclidean_size :: a -> Nat;
};

instance Euclidean_semiring Int where {
  euclidean_size = euclidean_size_int;
};

class (Euclidean_semiring a) => Euclidean_semiring_cancel a where {
};

instance Euclidean_semiring_cancel Int where {
};

integer_of_nat :: Nat -> Integer;
integer_of_nat (Nat x) = x;

equal_nat :: Nat -> Nat -> Bool;
equal_nat m n = integer_of_nat m == integer_of_nat n;

instance Eq Nat where {
  a == b = equal_nat a b;
};

times_nat :: Nat -> Nat -> Nat;
times_nat m n = Nat (integer_of_nat m * integer_of_nat n);

instance Times Nat where {
  times = times_nat;
};

instance Dvd Nat where {
};

one_nat :: Nat;
one_nat = Nat (1 :: Integer);

instance One Nat where {
  one = one_nat;
};

plus_nat :: Nat -> Nat -> Nat;
plus_nat m n = Nat (integer_of_nat m + integer_of_nat n);

instance Plus Nat where {
  plus = plus_nat;
};

zero_nat :: Nat;
zero_nat = Nat (0 :: Integer);

instance Zero Nat where {
  zero = zero_nat;
};

instance Semigroup_add Nat where {
};

instance Numeral Nat where {
};

instance Power Nat where {
};

minus_nat :: Nat -> Nat -> Nat;
minus_nat m n = Nat (max (0 :: Integer) (integer_of_nat m - integer_of_nat n));

instance Minus Nat where {
  minus = minus_nat;
};

divide_nat :: Nat -> Nat -> Nat;
divide_nat m n = Nat (divide_integer (integer_of_nat m) (integer_of_nat n));

instance Divide Nat where {
  divide = divide_nat;
};

modulo_nat :: Nat -> Nat -> Nat;
modulo_nat m n = Nat (modulo_integer (integer_of_nat m) (integer_of_nat n));

instance Modulo Nat where {
  modulo = modulo_nat;
};

less_eq_nat :: Nat -> Nat -> Bool;
less_eq_nat m n = integer_of_nat m <= integer_of_nat n;

less_nat :: Nat -> Nat -> Bool;
less_nat m n = integer_of_nat m < integer_of_nat n;

instance Ord Nat where {
  less_eq = less_eq_nat;
  less = less_nat;
};

instance Ab_semigroup_add Nat where {
};

instance Monoid_add Nat where {
};

instance Comm_monoid_add Nat where {
};

instance Mult_zero Nat where {
};

instance Semigroup_mult Nat where {
};

instance Semiring Nat where {
};

instance Semiring_0 Nat where {
};

instance Semiring_no_zero_divisors Nat where {
};

instance Monoid_mult Nat where {
};

instance Semiring_numeral Nat where {
};

instance Zero_neq_one Nat where {
};

instance Semiring_1 Nat where {
};

instance Semiring_1_no_zero_divisors Nat where {
};

instance Cancel_semigroup_add Nat where {
};

instance Cancel_ab_semigroup_add Nat where {
};

instance Cancel_comm_monoid_add Nat where {
};

instance Semiring_0_cancel Nat where {
};

instance Ab_semigroup_mult Nat where {
};

instance Comm_semiring Nat where {
};

instance Comm_semiring_0 Nat where {
};

instance Comm_semiring_0_cancel Nat where {
};

instance Semiring_1_cancel Nat where {
};

instance Comm_monoid_mult Nat where {
};

instance Comm_semiring_1 Nat where {
};

instance Comm_semiring_1_cancel Nat where {
};

instance Semidom Nat where {
};

instance Divide_trivial Nat where {
};

instance Semiring_no_zero_divisors_cancel Nat where {
};

instance Semidom_divide Nat where {
};

instance Semiring_modulo Nat where {
};

instance Semiring_modulo_trivial Nat where {
};

instance Algebraic_semidom Nat where {
};

instance Semidom_modulo Nat where {
};

data Set a = Set [a] | Coset [a];

data Dil_pk_ext a = Dil_pk_ext [Int] [[Int]] a;

data Dil_sk_ext a = Dil_sk_ext [Int] [Int] [Int] [[Int]] [[Int]] [[Int]] a;

data Dil_signature_ext a = Dil_signature_ext [Int] [[Int]] [[Nat]] a;

data Dil_sign_state_ext a =
  Dil_sign_state_ext [[Int]] [[Int]] [Int] [[Int]] [[Int]] [[Int]] [[Nat]] a;

data Dilithium_params_ext a =
  Dilithium_params_ext Nat Int Nat Nat Nat Nat Nat Int Int Nat Nat a;

suc :: Nat -> Nat;
suc n = plus_nat n one_nat;

nth :: forall a. [a] -> Nat -> a;
nth (x : xs) n =
  (if equal_nat n zero_nat then x else nth xs (minus_nat n one_nat));

upt :: Nat -> Nat -> [Nat];
upt i j = (if less_nat i j then i : upt (suc i) j else []);

foldr :: forall a b. (a -> b -> b) -> [a] -> b -> b;
foldr f [] = id;
foldr f (x : xs) = f x . foldr f xs;

removeAll :: forall a. (Eq a) => a -> [a] -> [a];
removeAll x [] = [];
removeAll x (y : xs) = (if x == y then removeAll x xs else y : removeAll x xs);

membera :: forall a. (Eq a) => [a] -> a -> Bool;
membera [] y = False;
membera (x : xs) y = x == y || membera xs y;

inserta :: forall a. (Eq a) => a -> [a] -> [a];
inserta x xs = (if membera xs x then xs else x : xs);

insert :: forall a. (Eq a) => a -> Set a -> Set a;
insert x (Set xs) = Set (inserta x xs);
insert x (Coset xs) = Coset (removeAll x xs);

member :: forall a. (Eq a) => a -> Set a -> Bool;
member x (Set xs) = membera xs x;
member x (Coset xs) = not (membera xs x);

dvd :: forall a. (Eq a, Semidom_modulo a) => a -> a -> Bool;
dvd a b = modulo b a == zero;

mod_exp_aux ::
  forall a. (Euclidean_semiring_cancel a) => a -> a -> a -> Nat -> a;
mod_exp_aux m y x n =
  (if equal_nat n zero_nat then y
    else (if equal_nat n one_nat then modulo (times x y) m
           else (if dvd (nat_of_integer (2 :: Integer)) n
                  then mod_exp_aux m y (modulo (times x x) m)
                         (divide_nat n (nat_of_integer (2 :: Integer)))
                  else mod_exp_aux m (modulo (times x y) m)
                         (modulo (times x x) m)
                         (divide_nat n (nat_of_integer (2 :: Integer))))));

mod_exp :: forall a. (Euclidean_semiring_cancel a) => a -> Nat -> a -> a;
mod_exp b e m = modulo (mod_exp_aux m one b e) m;

power_mod :: Int -> Nat -> Int -> Int;
power_mod base e m = mod_exp base e m;

twiddle :: Int -> Nat -> Int -> Int;
twiddle omega k q = power_mod omega k q;

poly_mod :: [Int] -> Int -> [Int];
poly_mod p q = map (\ a -> modulo_int a q) p;

list_update :: forall a. [a] -> Nat -> a -> [a];
list_update [] i y = [];
list_update (x : xs) i y =
  (if equal_nat i zero_nat then y : xs
    else x : list_update xs (minus_nat i one_nat) y);

butterfly :: Int -> Int -> Int -> Int -> (Int, Int);
butterfly a b tw q =
  let {
    t = modulo_int (times_int b tw) q;
  } in (modulo_int (plus_int a t) q, modulo_int (plus_int (minus_int a t) q) q);

ntt_layer :: [Int] -> Int -> Int -> Nat -> Nat -> Nat -> [Int];
ntt_layer a omega q n len start =
  (if equal_nat len zero_nat || less_nat n (plus_nat start len) then a
    else let {
           tw = twiddle omega
                  (times_nat
                    (divide_nat n
                      (times_nat (nat_of_integer (2 :: Integer)) len))
                    start)
                  q;
         } in (case butterfly (nth a start)
                      (nth a
                        (plus_nat start
                          (divide_nat len (nat_of_integer (2 :: Integer)))))
                      tw q
                of {
                (x, y) ->
                  let {
                    aa = list_update (list_update a start x)
                           (plus_nat start
                             (divide_nat len (nat_of_integer (2 :: Integer))))
                           y;
                  } in ntt_layer aa omega q n len (plus_nat start len);
              }));

ntt_iter_aux :: [Int] -> Int -> Int -> Nat -> Nat -> [Int];
ntt_iter_aux a omega q n len =
  (if less_nat len (nat_of_integer (2 :: Integer)) then a
    else let {
           aa = ntt_layer a omega q n len zero_nat;
         } in ntt_iter_aux aa omega q n
                (divide_nat len (nat_of_integer (2 :: Integer))));

ntt_fast :: [Int] -> Int -> Int -> Nat -> [Int];
ntt_fast a omega q n = ntt_iter_aux (poly_mod a q) omega q n n;

int_of_nat :: Nat -> Int;
int_of_nat n = Int_of_integer (integer_of_nat n);

mod_inverse :: Int -> Int -> Int;
mod_inverse a q =
  (if less_int one_int q
    then mod_exp a (nat (minus_int q (Int_of_integer (2 :: Integer)))) q
    else zero_int);

intt_fast :: [Int] -> Int -> Int -> Nat -> [Int];
intt_fast a_hat omega q n =
  let {
    omega_inv = mod_inverse omega q;
    n_inv = mod_inverse (int_of_nat n) q;
    a = ntt_iter_aux (poly_mod a_hat q) omega_inv q n n;
  } in map (\ x -> modulo_int (times_int x n_inv) q) a;

replicate :: forall a. Nat -> a -> [a];
replicate n x =
  (if equal_nat n zero_nat then [] else x : replicate (minus_nat n one_nat) x);

length_tailrec :: forall a. [a] -> Nat -> Nat;
length_tailrec [] n = n;
length_tailrec (x : xs) n = length_tailrec xs (suc n);

size_list :: forall a. [a] -> Nat;
size_list xs = length_tailrec xs zero_nat;

poly_coeff :: [Int] -> Nat -> Int;
poly_coeff p i = (if less_nat i (size_list p) then nth p i else zero_int);

poly_add :: [Int] -> [Int] -> [Int];
poly_add p q =
  let {
    n = max (size_list p) (size_list q);
  } in map (\ i -> plus_int (poly_coeff p i) (poly_coeff q i)) (upt zero_nat n);

poly_neg :: [Int] -> [Int];
poly_neg p = map uminus_int p;

poly_sub :: [Int] -> [Int] -> [Int];
poly_sub p q = poly_add p (poly_neg q);

dil_ntt_omega :: Int;
dil_ntt_omega = Int_of_integer (1753 :: Integer);

dil_ntt_q :: Int;
dil_ntt_q = Int_of_integer (8380417 :: Integer);

dil_ntt :: [Int] -> [Int];
dil_ntt a =
  ntt_fast a dil_ntt_omega dil_ntt_q (nat_of_integer (256 :: Integer));

dil_intt :: [Int] -> [Int];
dil_intt a_hat =
  intt_fast a_hat dil_ntt_omega dil_ntt_q (nat_of_integer (256 :: Integer));

st_z :: forall a. Dil_sign_state_ext a -> [[Int]];
st_z (Dil_sign_state_ext st_w st_w1 st_c st_z st_r0 st_ct0 st_h more) = st_z;

st_h :: forall a. Dil_sign_state_ext a -> [[Nat]];
st_h (Dil_sign_state_ext st_w st_w1 st_c st_z st_r0 st_ct0 st_h more) = st_h;

dil_gamma2 :: forall a. Dilithium_params_ext a -> Int;
dil_gamma2
  (Dilithium_params_ext dil_n dil_q dil_k dil_l dil_eta dil_tau dil_beta
    dil_gamma1 dil_gamma2 dil_d dil_omega more)
  = dil_gamma2;

ntt_pointwise_mult :: [Int] -> [Int] -> Int -> [Int];
ntt_pointwise_mult a_hat b_hat q =
  map (\ (x, y) -> modulo_int (times_int x y) q) (zip a_hat b_hat);

dil_poly_mult_ntt :: [Int] -> [Int] -> [Int];
dil_poly_mult_ntt a_hat b_hat = ntt_pointwise_mult a_hat b_hat dil_ntt_q;

dil_poly_add :: [Int] -> [Int] -> [Int];
dil_poly_add a b = poly_mod (poly_add a b) dil_ntt_q;

dil_inner_prod_ntt :: [[Int]] -> [[Int]] -> [Int];
dil_inner_prod_ntt [] w = replicate (nat_of_integer (256 :: Integer)) zero_int;
dil_inner_prod_ntt (p : ps) w =
  (case w of {
    [] -> replicate (nat_of_integer (256 :: Integer)) zero_int;
    r : rs -> dil_poly_add (dil_poly_mult_ntt p r) (dil_inner_prod_ntt ps rs);
  });

dil_mat_vec_mult_ntt :: [[[Int]]] -> [[Int]] -> [[Int]];
dil_mat_vec_mult_ntt a v = map (\ row -> dil_inner_prod_ntt row v) a;

challenge_vec_mult :: [Int] -> [[Int]] -> [[Int]];
challenge_vec_mult c v =
  let {
    c_hat = dil_ntt c;
  } in map (\ p -> dil_intt (dil_poly_mult_ntt c_hat (dil_ntt p))) v;

mod_centered :: Int -> Int -> Int;
mod_centered x q =
  let {
    r = modulo_int x q;
  } in (if less_int (divide_int q (Int_of_integer (2 :: Integer))) r
         then minus_int r q else r);

decompose_coeff :: Int -> Int -> (Int, Int);
decompose_coeff r alpha =
  let {
    r0 = mod_centered r alpha;
    r1 = divide_int (minus_int r r0) alpha;
  } in (if equal_int (minus_int r r0) (minus_int dil_ntt_q one_int)
         then (zero_int, minus_int r0 one_int) else (r1, r0));

highbits_coeff :: Int -> Int -> Int;
highbits_coeff r alpha = fst (decompose_coeff r alpha);

makehint_coeff :: Int -> Int -> Int -> Nat;
makehint_coeff z r alpha =
  (if not (equal_int (highbits_coeff r alpha)
            (highbits_coeff (plus_int r z) alpha))
    then one_nat else zero_nat);

makehint_poly :: [Int] -> [Int] -> Int -> [Nat];
makehint_poly z r alpha = map (\ (x, y) -> makehint_coeff x y alpha) (zip z r);

makehint_vec :: [[Int]] -> [[Int]] -> Int -> [[Nat]];
makehint_vec z_vec r_vec alpha =
  map (\ (x, y) -> makehint_poly x y alpha) (zip z_vec r_vec);

highbits_poly :: [Int] -> Int -> [Int];
highbits_poly p alpha = map (\ c -> highbits_coeff c alpha) p;

highbits_vec :: [[Int]] -> Int -> [[Int]];
highbits_vec v alpha = map (\ p -> highbits_poly p alpha) v;

dil_vec_intt :: [[Int]] -> [[Int]];
dil_vec_intt v = map dil_intt v;

sk_t0 :: forall a. Dil_sk_ext a -> [[Int]];
sk_t0 (Dil_sk_ext sk_rho sk_K sk_tr sk_s1 sk_s2 sk_t0 more) = sk_t0;

sk_s2 :: forall a. Dil_sk_ext a -> [[Int]];
sk_s2 (Dil_sk_ext sk_rho sk_K sk_tr sk_s1 sk_s2 sk_t0 more) = sk_s2;

sk_s1 :: forall a. Dil_sk_ext a -> [[Int]];
sk_s1 (Dil_sk_ext sk_rho sk_K sk_tr sk_s1 sk_s2 sk_t0 more) = sk_s1;

lowbits_coeff :: Int -> Int -> Int;
lowbits_coeff r alpha = snd (decompose_coeff r alpha);

lowbits_poly :: [Int] -> Int -> [Int];
lowbits_poly p alpha = map (\ c -> lowbits_coeff c alpha) p;

lowbits_vec :: [[Int]] -> Int -> [[Int]];
lowbits_vec v alpha = map (\ p -> lowbits_poly p alpha) v;

dil_poly_sub :: [Int] -> [Int] -> [Int];
dil_poly_sub a b = poly_mod (poly_sub a b) dil_ntt_q;

dil_vec_sub :: [[Int]] -> [[Int]] -> [[Int]];
dil_vec_sub v w = map (\ (a, b) -> dil_poly_sub a b) (zip v w);

dil_vec_ntt :: [[Int]] -> [[Int]];
dil_vec_ntt v = map dil_ntt v;

dil_vec_add :: [[Int]] -> [[Int]] -> [[Int]];
dil_vec_add v w = map (\ (a, b) -> dil_poly_add a b) (zip v w);

dil_sign_compute ::
  Dilithium_params_ext () ->
    [[[Int]]] -> Dil_sk_ext () -> [[Int]] -> [Int] -> Dil_sign_state_ext ();
dil_sign_compute params a sk y c =
  let {
    alpha = times_int (Int_of_integer (2 :: Integer)) (dil_gamma2 params);
    s1 = sk_s1 sk;
    s2 = sk_s2 sk;
    t0 = sk_t0 sk;
    y_hat = dil_vec_ntt y;
    ay_hat = dil_mat_vec_mult_ntt a y_hat;
    w = dil_vec_intt ay_hat;
    w1 = highbits_vec w alpha;
    cs1 = challenge_vec_mult c s1;
    z = dil_vec_add y cs1;
    cs2 = challenge_vec_mult c s2;
    w_minus_cs2 = dil_vec_sub w cs2;
    r0 = lowbits_vec w_minus_cs2 alpha;
    ct0 = challenge_vec_mult c t0;
    neg_ct0 = map (map uminus_int) ct0;
    w_cs2_ct0 = dil_vec_add w_minus_cs2 ct0;
    h = makehint_vec neg_ct0 w_cs2_ct0 alpha;
  } in Dil_sign_state_ext w w1 c z r0 ct0 h ();

dil_omega :: forall a. Dilithium_params_ext a -> Nat;
dil_omega
  (Dilithium_params_ext dil_n dil_q dil_k dil_l dil_eta dil_tau dil_beta
    dil_gamma1 dil_gamma2 dil_d dil_omega more)
  = dil_omega;

st_ct0 :: forall a. Dil_sign_state_ext a -> [[Int]];
st_ct0 (Dil_sign_state_ext st_w st_w1 st_c st_z st_r0 st_ct0 st_h more) =
  st_ct0;

st_r0 :: forall a. Dil_sign_state_ext a -> [[Int]];
st_r0 (Dil_sign_state_ext st_w st_w1 st_c st_z st_r0 st_ct0 st_h more) = st_r0;

dil_beta :: forall a. Dilithium_params_ext a -> Nat;
dil_beta
  (Dilithium_params_ext dil_n dil_q dil_k dil_l dil_eta dil_tau dil_beta
    dil_gamma1 dil_gamma2 dil_d dil_omega more)
  = dil_beta;

coeff_in_range :: Int -> Int -> Bool;
coeff_in_range c bnd = less_int (abs_int c) bnd;

poly_linf_bound :: [Int] -> Int -> Bool;
poly_linf_bound p bnd = all (\ c -> coeff_in_range c bnd) p;

vec_linf_bound :: [[Int]] -> Int -> Bool;
vec_linf_bound v bnd = all (\ p -> poly_linf_bound p bnd) v;

check_lowbits_bound :: Dilithium_params_ext () -> [[Int]] -> Bool;
check_lowbits_bound params r0 =
  vec_linf_bound r0
    (minus_int (dil_gamma2 params) (int_of_nat (dil_beta params)));

check_ct0_bound :: Dilithium_params_ext () -> [[Int]] -> Bool;
check_ct0_bound params ct0 = vec_linf_bound ct0 (dil_gamma2 params);

dil_gamma1 :: forall a. Dilithium_params_ext a -> Int;
dil_gamma1
  (Dilithium_params_ext dil_n dil_q dil_k dil_l dil_eta dil_tau dil_beta
    dil_gamma1 dil_gamma2 dil_d dil_omega more)
  = dil_gamma1;

check_z_bound :: Dilithium_params_ext () -> [[Int]] -> Bool;
check_z_bound params z =
  vec_linf_bound z
    (minus_int (dil_gamma1 params) (int_of_nat (dil_beta params)));

sum_list :: forall a. (Monoid_add a) => [a] -> a;
sum_list xs = foldr plus xs zero;

hint_weight :: [[Nat]] -> Nat;
hint_weight h = sum_list (map sum_list h);

dil_sign_accept :: Dilithium_params_ext () -> Dil_sign_state_ext () -> Bool;
dil_sign_accept params st =
  check_z_bound params (st_z st) &&
    check_lowbits_bound params (st_r0 st) &&
      check_ct0_bound params (st_ct0 st) &&
        less_eq_nat (hint_weight (st_h st)) (dil_omega params);

dil_sign ::
  Dilithium_params_ext () ->
    [[[Int]]] ->
      Dil_sk_ext () ->
        [Int] -> [[Int]] -> [Int] -> Maybe (Dil_signature_ext ());
dil_sign params a sk msg y c =
  let {
    st = dil_sign_compute params a sk y c;
  } in (if dil_sign_accept params st
         then Just (Dil_signature_ext msg (st_z st) (st_h st) ()) else Nothing);

dil_d :: forall a. Dilithium_params_ext a -> Nat;
dil_d (Dilithium_params_ext dil_n dil_q dil_k dil_l dil_eta dil_tau dil_beta
        dil_gamma1 dil_gamma2 dil_d dil_omega more)
  = dil_d;

power :: forall a. (Power a) => a -> Nat -> a;
power a n =
  (if equal_nat n zero_nat then one
    else times a (power a (minus_nat n one_nat)));

power2round_coeff :: Int -> Nat -> (Int, Int);
power2round_coeff r d = let {
                          two_d = power (Int_of_integer (2 :: Integer)) d;
                          r0 = mod_centered r two_d;
                          r1 = divide_int (minus_int r r0) two_d;
                        } in (r1, r0);

power2round_poly :: [Int] -> Nat -> ([Int], [Int]);
power2round_poly p d = let {
                         pairs = map (\ c -> power2round_coeff c d) p;
                       } in (map fst pairs, map snd pairs);

power2round_vec :: [[Int]] -> Nat -> ([[Int]], [[Int]]);
power2round_vec v d = let {
                        pairs = map (\ p -> power2round_poly p d) v;
                      } in (map fst pairs, map snd pairs);

dil_keygen ::
  Dilithium_params_ext () ->
    [Int] ->
      [Int] ->
        [[[Int]]] -> [[Int]] -> [[Int]] -> (Dil_pk_ext (), Dil_sk_ext ());
dil_keygen params rho k a s1 s2 =
  let {
    s1_hat = dil_vec_ntt s1;
    as1_hat = dil_mat_vec_mult_ntt a s1_hat;
    as1 = dil_vec_intt as1_hat;
    t = dil_vec_add as1 s2;
  } in (case power2round_vec t (dil_d params) of {
         (t1, t0) -> let {
                       tr = rho;
                       pk = Dil_pk_ext rho t1 ();
                       aa = Dil_sk_ext rho k tr s1 s2 t0 ();
                     } in (pk, aa);
       });

sig_z :: forall a. Dil_signature_ext a -> [[Int]];
sig_z (Dil_signature_ext sig_c_tilde sig_z sig_h more) = sig_z;

sig_h :: forall a. Dil_signature_ext a -> [[Nat]];
sig_h (Dil_signature_ext sig_c_tilde sig_z sig_h more) = sig_h;

pk_t1 :: forall a. Dil_pk_ext a -> [[Int]];
pk_t1 (Dil_pk_ext pk_rho pk_t1 more) = pk_t1;

usehint_coeff :: Nat -> Int -> Int -> Int;
usehint_coeff h r alpha =
  (case decompose_coeff r alpha of {
    (r1, r0) ->
      let {
        m = divide_int (minus_int dil_ntt_q one_int) alpha;
      } in (if equal_nat h zero_nat then r1
             else (if less_int zero_int r0
                    then modulo_int (plus_int r1 one_int) (plus_int m one_int)
                    else modulo_int
                           (plus_int (plus_int (minus_int r1 one_int) m)
                             one_int)
                           (plus_int m one_int)));
  });

usehint_poly :: [Nat] -> [Int] -> Int -> [Int];
usehint_poly h r alpha = map (\ (x, y) -> usehint_coeff x y alpha) (zip h r);

usehint_vec :: [[Nat]] -> [[Int]] -> Int -> [[Int]];
usehint_vec h_vec r_vec alpha =
  map (\ (x, y) -> usehint_poly x y alpha) (zip h_vec r_vec);

dil_verify ::
  Dilithium_params_ext () ->
    [[[Int]]] ->
      Dil_pk_ext () -> [Int] -> Dil_signature_ext () -> [Int] -> Bool;
dil_verify params a pk msg sig c =
  let {
    alpha = times_int (Int_of_integer (2 :: Integer)) (dil_gamma2 params);
    z = sig_z sig;
    h = sig_h sig;
    t1 = pk_t1 pk;
    z_ok = check_z_bound params z;
    z_hat = dil_vec_ntt z;
    az_hat = dil_mat_vec_mult_ntt a z_hat;
    az = dil_vec_intt az_hat;
    ct1 = challenge_vec_mult c t1;
    two_d = power (Int_of_integer (2 :: Integer)) (dil_d params);
    ct1_scaled =
      map (map (\ x -> modulo_int (times_int x two_d) dil_ntt_q)) ct1;
    w_approx = dil_vec_sub az ct1_scaled;
    _ = usehint_vec h w_approx alpha;
    aa = less_eq_nat (hint_weight h) (dil_omega params);
  } in z_ok && aa;

make :: [Int] -> [[Int]] -> Dil_pk_ext ();
make pk_rho pk_t1 = Dil_pk_ext pk_rho pk_t1 ();

makea ::
  [Int] -> [Int] -> [Int] -> [[Int]] -> [[Int]] -> [[Int]] -> Dil_sk_ext ();
makea sk_rho sk_K sk_tr sk_s1 sk_s2 sk_t0 =
  Dil_sk_ext sk_rho sk_K sk_tr sk_s1 sk_s2 sk_t0 ();

sk_K :: forall a. Dil_sk_ext a -> [Int];
sk_K (Dil_sk_ext sk_rho sk_K sk_tr sk_s1 sk_s2 sk_t0 more) = sk_K;

sk_tr :: forall a. Dil_sk_ext a -> [Int];
sk_tr (Dil_sk_ext sk_rho sk_K sk_tr sk_s1 sk_s2 sk_t0 more) = sk_tr;

pk_rho :: forall a. Dil_pk_ext a -> [Int];
pk_rho (Dil_pk_ext pk_rho pk_t1 more) = pk_rho;

sk_rho :: forall a. Dil_sk_ext a -> [Int];
sk_rho (Dil_sk_ext sk_rho sk_K sk_tr sk_s1 sk_s2 sk_t0 more) = sk_rho;

mldsa44_params :: Dilithium_params_ext ();
mldsa44_params =
  Dilithium_params_ext (nat_of_integer (256 :: Integer))
    (Int_of_integer (8380417 :: Integer)) (nat_of_integer (4 :: Integer))
    (nat_of_integer (4 :: Integer)) (nat_of_integer (2 :: Integer))
    (nat_of_integer (39 :: Integer)) (nat_of_integer (78 :: Integer))
    (Int_of_integer (131072 :: Integer)) (Int_of_integer (95232 :: Integer))
    (nat_of_integer (13 :: Integer)) (nat_of_integer (80 :: Integer)) ();

mldsa65_params :: Dilithium_params_ext ();
mldsa65_params =
  Dilithium_params_ext (nat_of_integer (256 :: Integer))
    (Int_of_integer (8380417 :: Integer)) (nat_of_integer (6 :: Integer))
    (nat_of_integer (5 :: Integer)) (nat_of_integer (4 :: Integer))
    (nat_of_integer (49 :: Integer)) (nat_of_integer (196 :: Integer))
    (Int_of_integer (524288 :: Integer)) (Int_of_integer (261888 :: Integer))
    (nat_of_integer (13 :: Integer)) (nat_of_integer (55 :: Integer)) ();

mldsa87_params :: Dilithium_params_ext ();
mldsa87_params =
  Dilithium_params_ext (nat_of_integer (256 :: Integer))
    (Int_of_integer (8380417 :: Integer)) (nat_of_integer (8 :: Integer))
    (nat_of_integer (7 :: Integer)) (nat_of_integer (2 :: Integer))
    (nat_of_integer (60 :: Integer)) (nat_of_integer (120 :: Integer))
    (Int_of_integer (524288 :: Integer)) (Int_of_integer (261888 :: Integer))
    (nat_of_integer (13 :: Integer)) (nat_of_integer (75 :: Integer)) ();

bot_set :: forall a. Set a;
bot_set = Set [];

valid_challenge :: [Int] -> Nat -> Bool;
valid_challenge c tau =
  equal_nat (size_list c) (nat_of_integer (256 :: Integer)) &&
    all (\ coeff ->
          member coeff
            (insert (uminus_int one_int)
              (insert zero_int (insert one_int bot_set))))
      c &&
      equal_nat (size_list (filter (\ x -> not (equal_int x zero_int)) c)) tau;

challenge_weight :: [Int] -> Nat;
challenge_weight c = size_list (filter (\ x -> not (equal_int x zero_int)) c);

makeb :: [Int] -> [[Int]] -> [[Nat]] -> Dil_signature_ext ();
makeb sig_c_tilde sig_z sig_h = Dil_signature_ext sig_c_tilde sig_z sig_h ();

makec ::
  Nat ->
    Int ->
      Nat ->
        Nat ->
          Nat ->
            Nat -> Nat -> Int -> Int -> Nat -> Nat -> Dilithium_params_ext ();
makec dil_n dil_q dil_k dil_l dil_eta dil_tau dil_beta dil_gamma1 dil_gamma2
  dil_d dil_omega =
  Dilithium_params_ext dil_n dil_q dil_k dil_l dil_eta dil_tau dil_beta
    dil_gamma1 dil_gamma2 dil_d dil_omega ();

dil_k :: forall a. Dilithium_params_ext a -> Nat;
dil_k (Dilithium_params_ext dil_n dil_q dil_k dil_l dil_eta dil_tau dil_beta
        dil_gamma1 dil_gamma2 dil_d dil_omega more)
  = dil_k;

dil_l :: forall a. Dilithium_params_ext a -> Nat;
dil_l (Dilithium_params_ext dil_n dil_q dil_k dil_l dil_eta dil_tau dil_beta
        dil_gamma1 dil_gamma2 dil_d dil_omega more)
  = dil_l;

dil_n :: forall a. Dilithium_params_ext a -> Nat;
dil_n (Dilithium_params_ext dil_n dil_q dil_k dil_l dil_eta dil_tau dil_beta
        dil_gamma1 dil_gamma2 dil_d dil_omega more)
  = dil_n;

dil_q :: forall a. Dilithium_params_ext a -> Int;
dil_q (Dilithium_params_ext dil_n dil_q dil_k dil_l dil_eta dil_tau dil_beta
        dil_gamma1 dil_gamma2 dil_d dil_omega more)
  = dil_q;

dil_tau :: forall a. Dilithium_params_ext a -> Nat;
dil_tau
  (Dilithium_params_ext dil_n dil_q dil_k dil_l dil_eta dil_tau dil_beta
    dil_gamma1 dil_gamma2 dil_d dil_omega more)
  = dil_tau;

dil_eta :: forall a. Dilithium_params_ext a -> Nat;
dil_eta
  (Dilithium_params_ext dil_n dil_q dil_k dil_l dil_eta dil_tau dil_beta
    dil_gamma1 dil_gamma2 dil_d dil_omega more)
  = dil_eta;

valid_dilithium_params :: Dilithium_params_ext () -> Bool;
valid_dilithium_params p =
  equal_nat (dil_n p) (nat_of_integer (256 :: Integer)) &&
    equal_int (dil_q p) (Int_of_integer (8380417 :: Integer)) &&
      less_nat zero_nat (dil_k p) &&
        less_eq_nat (dil_k p) (nat_of_integer (8 :: Integer)) &&
          less_nat zero_nat (dil_l p) &&
            less_eq_nat (dil_l p) (nat_of_integer (7 :: Integer)) &&
              less_nat zero_nat (dil_eta p) &&
                less_nat zero_nat (dil_tau p) &&
                  equal_nat (dil_beta p) (times_nat (dil_tau p) (dil_eta p)) &&
                    less_int zero_int (dil_gamma1 p) &&
                      less_int zero_int (dil_gamma2 p) &&
                        less_nat zero_nat (dil_d p) &&
                          less_eq_nat (dil_d p)
                            (nat_of_integer (13 :: Integer)) &&
                            less_nat zero_nat (dil_omega p);

sig_c_tilde :: forall a. Dil_signature_ext a -> [Int];
sig_c_tilde (Dil_signature_ext sig_c_tilde sig_z sig_h more) = sig_c_tilde;

}
