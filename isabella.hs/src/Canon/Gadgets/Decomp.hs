{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

-- | Gadget decomposition for lattice cryptography
-- Generated from Canon/Gadgets/Decomp.thy
--
-- Base-B decomposition is used in key switching and bootstrapping.
module Canon.Gadgets.Decomp (
    -- * Single digit extraction
    digit,
    -- * Full decomposition
    decomp_base, recompose,
    -- * Gadget vector
    gadget_vec,
    -- * Signed decomposition
    digit_signed, decomp_signed
) where

import Prelude ((+), (-), (*), div, mod, (==), (>), (<=), (&&),
                Bool(..), Int, map, length, (^))
import qualified Prelude

-- | Extract i-th digit in base B representation
-- digit B i x = (x div B^i) mod B
digit :: Int -> Int -> Int -> Int
digit b i x = (x `div` (b ^ i)) `mod` b

-- | Decompose x into k digits in base B
-- Returns [d_0, d_1, ..., d_{k-1}] where x = sum(d_i * B^i) mod B^k
decomp_base :: Int -> Int -> Int -> [Int]
decomp_base _ 0 _ = []
decomp_base b k x = (x `mod` b) : decomp_base b (k - 1) (x `div` b)

-- | Recompose digits back to integer
-- recompose B [d_0, d_1, ...] = d_0 + d_1*B + d_2*B^2 + ...
recompose :: Int -> [Int] -> Int
recompose _ [] = 0
recompose b (d:ds) = d + b * recompose b ds

-- | Gadget vector: [1, B, B^2, ..., B^{k-1}]
gadget_vec :: Int -> Int -> [Int]
gadget_vec b k = map (\i -> b ^ i) [0..k-1]

-- | Signed digit: centered in (-B/2, B/2]
digit_signed :: Int -> Int -> Int -> Int
digit_signed b i x =
    let d = digit b i x
    in if 2 * d > b then d - b else d

-- | Signed decomposition: digits in (-B/2, B/2]
decomp_signed :: Int -> Int -> Int -> [Int]
decomp_signed b k x = map (\i -> digit_signed b i x) [0..k-1]
