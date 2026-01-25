{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

-- | Polynomial ring arithmetic over Z_q[X]/(f(X))
-- Generated from Canon/Rings/PolyMod.thy
module Canon.Rings.PolyMod (
    -- * Polynomial Type
    Poly,
    -- * Basic operations
    zero_poly, const_poly, poly_degree, poly_coeff,
    -- * Arithmetic
    poly_add, poly_neg, poly_sub,
    poly_scale, poly_mult, poly_mult_coeff,
    -- * Modular reduction
    poly_mod, ring_mod, ring_mod_coeff,
    -- * Ring operations (mod X^n + 1)
    ring_mult, ring_add, ring_sub,
    -- * Ring parameters
    RingParams(..), makeRingParams, validRingParams, validRingElem,
    ring_n, ring_q
) where

import Prelude ((+), (-), (*), div, mod, (==), (/=), (>), (>=), (<), (<=), (&&), (||),
                Bool(..), Int, map, length, replicate, take, drop, (++), ($),
                otherwise, max, null, sum, zipWith)
import qualified Prelude

-- | Polynomial as list of coefficients [a_0, a_1, ..., a_{n-1}]
type Poly = [Int]

-- | Zero polynomial
zero_poly :: Poly
zero_poly = []

-- | Constant polynomial
const_poly :: Int -> Poly
const_poly c = if c == 0 then [] else [c]

-- | Polynomial degree (0 for empty)
poly_degree :: Poly -> Int
poly_degree p = if null p then 0 else length p - 1

-- | Get coefficient (0 for out-of-bounds)
poly_coeff :: Poly -> Int -> Int
poly_coeff p i = if i < length p then p Prelude.!! i else 0

-- | Polynomial addition
poly_add :: Poly -> Poly -> Poly
poly_add p q =
    let n = max (length p) (length q)
    in map (\i -> poly_coeff p i + poly_coeff q i) [0..n-1]

-- | Polynomial negation
poly_neg :: Poly -> Poly
poly_neg = map Prelude.negate

-- | Polynomial subtraction
poly_sub :: Poly -> Poly -> Poly
poly_sub p q = poly_add p (poly_neg q)

-- | Scalar multiplication
poly_scale :: Int -> Poly -> Poly
poly_scale c = map (* c)

-- | Coefficient of polynomial product at position k
poly_mult_coeff :: Poly -> Poly -> Int -> Int
poly_mult_coeff p q k = sum [poly_coeff p j * poly_coeff q (k - j) | j <- [0..k]]

-- | Polynomial multiplication
poly_mult :: Poly -> Poly -> Poly
poly_mult p q
    | null p || null q = []
    | otherwise = map (poly_mult_coeff p q) [0..length p + length q - 2]

-- | Reduce polynomial mod X^n + 1 (cyclotomic)
-- Coefficients at position n+i are subtracted from position i
poly_mod :: Poly -> Int -> Poly
poly_mod p n
    | length p <= n = p ++ replicate (n - length p) 0
    | otherwise =
        let (lo, hi) = Prelude.splitAt n p
            negHi = map Prelude.negate hi
        in poly_mod (poly_add lo (negHi ++ replicate (n - length negHi) 0)) n

-- | Reduce coefficients mod q
ring_mod_coeff :: Poly -> Int -> Poly
ring_mod_coeff p q = map (`mod` q) p

-- | Full ring reduction: mod X^n + 1 then mod q
ring_mod :: Poly -> Int -> Int -> Poly
ring_mod p n q = ring_mod_coeff (poly_mod p n) q

-- | Ring multiplication in Z_q[X]/(X^n + 1)
ring_mult :: Poly -> Poly -> Int -> Int -> Poly
ring_mult p q n modQ = ring_mod (poly_mult p q) n modQ

-- | Ring addition in Z_q[X]/(X^n + 1)
ring_add :: Poly -> Poly -> Int -> Int -> Poly
ring_add p q n modQ = ring_mod (poly_add p q) n modQ

-- | Ring subtraction in Z_q[X]/(X^n + 1)
ring_sub :: Poly -> Poly -> Int -> Int -> Poly
ring_sub p q n modQ = ring_mod (poly_sub p q) n modQ

-- | Ring parameters
data RingParams = RingParams {
    ring_n :: Int,  -- ^ Polynomial degree
    ring_q :: Int   -- ^ Coefficient modulus
} deriving (Prelude.Show, Prelude.Eq)

-- | Create ring parameters
makeRingParams :: Int -> Int -> RingParams
makeRingParams = RingParams

-- | Validate ring parameters
validRingParams :: RingParams -> Bool
validRingParams p = ring_n p > 0 && ring_q p > 1

-- | Validate ring element
validRingElem :: RingParams -> Poly -> Bool
validRingElem params p =
    length p == ring_n params &&
    Prelude.all (\c -> c >= 0 && c < ring_q params) p
