{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

-- | Modular arithmetic for Z_q
--
-- This module provides operations for working with integers modulo q,
-- with a focus on centered representation used in lattice cryptography.
--
-- Generated from @Canon/Algebra/Zq.thy@
module Canon.Algebra.Zq (
    -- * Centered modular reduction
    mod_centered,

    -- * Vector modular operations
    vec_mod,
    vec_mod_centered,

    -- * Distance from zero
    dist0,

    -- * Bit encoding/decoding for LWE
    encode_bit,
    decode_bit,

    -- * Matrix operations
    mat_vec_mult_mod
) where

import Prelude ((+), (-), (*), div, mod, abs, (>), Bool(..), Int, map)
import qualified Prelude

-- | Centered modular reduction: maps x to the range (-q\/2, q\/2]
--
-- This is the standard representation for LWE error terms, as it
-- minimizes the absolute value of the representative.
--
-- Properties (proven in Isabelle):
--
-- * @mod_centered x q `mod` q == x `mod` q@
-- * @abs (mod_centered x q) <= q `div` 2@
-- * @mod_centered 0 q == 0@ (for q > 0)
--
-- ==== __Examples__
--
-- >>> mod_centered 7 5
-- 2
-- >>> mod_centered 8 5
-- -2
-- >>> mod_centered 3 5
-- 3
mod_centered :: Int -> Int -> Int
mod_centered x q =
    let r = x `mod` q
    in if r > q `div` 2 then r - q else r

-- | Apply standard modular reduction to each element of a vector
--
-- >>> vec_mod [7, 13, -2] 5
-- [2, 3, 3]
vec_mod :: [Int] -> Int -> [Int]
vec_mod v q = map (\x -> x `mod` q) v

-- | Apply centered modular reduction to each element of a vector
--
-- >>> vec_mod_centered [7, 13, -2] 5
-- [2, -2, -2]
vec_mod_centered :: [Int] -> Int -> [Int]
vec_mod_centered v q = map (\x -> mod_centered x q) v

-- | Distance from zero in Z_q
--
-- Computes the absolute value of the centered representative.
-- This is used to determine how "close" a value is to zero
-- in the ring Z_q, which is critical for LWE decryption.
--
-- Properties (proven in Isabelle):
--
-- * @dist0 q x >= 0@
-- * @dist0 q x <= q `div` 2@
-- * @dist0 q 0 == 0@ (for q > 0)
-- * @dist0 q (x `mod` q) == dist0 q x@
--
-- >>> dist0 256 5
-- 5
-- >>> dist0 256 250
-- 6
dist0 :: Int -> Int -> Int
dist0 q x = abs (mod_centered x q)

-- | Encode a boolean as an element of Z_q
--
-- * False encodes to 0
-- * True encodes to q\/2
--
-- This encoding is used in LWE-based encryption where the
-- message bit determines whether the ciphertext is close
-- to 0 or close to q\/2.
--
-- >>> encode_bit 256 False
-- 0
-- >>> encode_bit 256 True
-- 128
encode_bit :: Int -> Bool -> Int
encode_bit q b = if b then q `div` 2 else 0

-- | Decode an element of Z_q to a boolean
--
-- Returns True if the distance from zero exceeds q\/4,
-- indicating the value is closer to q\/2 than to 0.
--
-- Properties (proven in Isabelle):
--
-- * @decode_bit q (encode_bit q b) == b@ (for q > 2)
-- * If @abs x < q `div` 4@ then @decode_bit q x == False@
-- * If @q `mod` 4 == 0@ and @abs x < q `div` 4@
--   then @decode_bit q (x + q `div` 2) == True@
--
-- >>> decode_bit 256 5
-- False
-- >>> decode_bit 256 130
-- True
decode_bit :: Int -> Int -> Bool
decode_bit q x = dist0 q x > q `div` 4

-- | Matrix-vector multiplication modulo q
--
-- Computes @A * v mod q@ where A is a matrix and v is a vector.
--
-- >>> mat_vec_mult_mod [[1,2],[3,4]] [5,6] 10
-- [7, 9]
mat_vec_mult_mod :: [[Int]] -> [Int] -> Int -> [Int]
mat_vec_mult_mod a v q = vec_mod (mat_vec_mult a v) q

-- Helper for matrix-vector multiplication
mat_vec_mult :: [[Int]] -> [Int] -> [Int]
mat_vec_mult a v = map (inner_prod v) a

inner_prod :: [Int] -> [Int] -> Int
inner_prod xs ys = Prelude.sum (Prelude.zipWith (*) xs ys)
