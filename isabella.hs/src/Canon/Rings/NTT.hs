{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

-- | Number Theoretic Transform (NTT)
-- Generated from Canon/Rings/NTT.thy
--
-- Provides O(n log n) NTT operations for polynomial multiplication
-- in lattice cryptography (Kyber, Dilithium).
module Canon.Rings.NTT (
    -- * NTT Parameters
    NTTParams(..), makeNTTParams, validNTTParams,
    ntt_n, ntt_q, ntt_omega,
    kyberNTTParams, dilithiumNTTParams,
    -- * Primitive operations
    power_mod, mod_inverse, is_primitive_root,
    -- * Twiddle factors
    twiddle, twiddle_factors,
    -- * Naive NTT (O(n^2))
    ntt_naive, intt_naive, ntt_coeff, intt_coeff,
    -- * Fast NTT (O(n log n) Cooley-Tukey)
    butterfly, ntt_fast, intt_fast,
    -- * Pointwise operations
    ntt_pointwise_mult
) where

import Prelude ((+), (-), (*), div, mod, (==), (/=), (>), (>=), (<), (<=), (&&), (||),
                Bool(..), Int, Integer, map, foldl, zipWith, zipWith3, zip, length, replicate,
                take, drop, (++), ($), otherwise, abs, even, fromIntegral)
import qualified Prelude
import Data.Bits (shiftR, testBit, setBit)

-- | NTT parameters record
data NTTParams = NTTParams {
    ntt_n :: Int,      -- ^ Polynomial degree (power of 2)
    ntt_q :: Int,      -- ^ Modulus
    ntt_omega :: Int   -- ^ Primitive n-th root of unity mod q
} deriving (Prelude.Show, Prelude.Eq)

-- | Create NTT parameters
makeNTTParams :: Int -> Int -> Int -> NTTParams
makeNTTParams = NTTParams

-- | Modular exponentiation: a^k mod m
power_mod :: Int -> Int -> Int -> Int
power_mod a 0 m = 1 `mod` m
power_mod a k m
    | even k    = power_mod ((a * a) `mod` m) (k `div` 2) m
    | otherwise = (a * power_mod a (k - 1) m) `mod` m

-- | Extended Euclidean algorithm for modular inverse
extendedGcd :: Int -> Int -> (Int, Int, Int)
extendedGcd a 0 = (a, 1, 0)
extendedGcd a b =
    let (g, x, y) = extendedGcd b (a `mod` b)
    in (g, y, x - (a `div` b) * y)

-- | Modular multiplicative inverse
mod_inverse :: Int -> Int -> Int
mod_inverse a m =
    let (_, x, _) = extendedGcd a m
    in ((x `mod` m) + m) `mod` m

-- | Check if omega is a primitive n-th root of unity mod q
is_primitive_root :: Int -> Int -> Int -> Bool
is_primitive_root omega n q =
    power_mod omega n q == 1 &&
    Prelude.all (\k -> power_mod omega k q /= 1) [1..n-1]

-- | Validate NTT parameters
validNTTParams :: NTTParams -> Bool
validNTTParams params =
    ntt_n params > 0 &&
    ntt_q params > 1 &&
    is_primitive_root (ntt_omega params) (ntt_n params) (ntt_q params)

-- | Twiddle factor: omega^k mod q
twiddle :: Int -> Int -> Int -> Int
twiddle omega k q = power_mod omega k q

-- | Precompute all twiddle factors
twiddle_factors :: Int -> Int -> Int -> [Int]
twiddle_factors omega n q = [twiddle omega k q | k <- [0..n-1]]

-- | Single NTT coefficient (for naive implementation)
ntt_coeff :: [Int] -> Int -> Int -> Int -> Int
ntt_coeff a omega q k =
    let n = length a
        terms = zipWith (\ai i -> (ai * twiddle omega (k * i) q) `mod` q) a [0..]
    in foldl (\acc x -> (acc + x) `mod` q) 0 terms

-- | Naive NTT: O(n^2) direct computation
ntt_naive :: [Int] -> Int -> Int -> [Int]
ntt_naive a omega q = [ntt_coeff a omega q k | k <- [0..length a - 1]]

-- | Single INTT coefficient
intt_coeff :: [Int] -> Int -> Int -> Int -> Int
intt_coeff a_hat omega q k =
    let n = length a_hat
        omega_inv = mod_inverse omega q
        terms = zipWith (\ai i -> (ai * twiddle omega_inv (k * i) q) `mod` q) a_hat [0..]
        sum_val = foldl (\acc x -> (acc + x) `mod` q) 0 terms
        n_inv = mod_inverse n q
    in (sum_val * n_inv) `mod` q

-- | Naive inverse NTT: O(n^2)
intt_naive :: [Int] -> Int -> Int -> [Int]
intt_naive a_hat omega q = [intt_coeff a_hat omega q k | k <- [0..length a_hat - 1]]

-- | Butterfly operation for Cooley-Tukey NTT
butterfly :: Int -> Int -> Int -> Int -> (Int, Int)
butterfly u v tw q =
    let t = (v * tw) `mod` q
        u' = (u + t) `mod` q
        v' = ((u - t) `mod` q + q) `mod` q
    in (u', v')

-- | NTT layer: process one level of the butterfly network
ntt_layer :: [Int] -> Int -> Int -> Int -> Int -> [Int]
ntt_layer [] _ _ _ _ = []
ntt_layer a omega q n len
    | len > n `div` 2 = a
    | otherwise =
        let half = len
            go [] _ result = Prelude.reverse result
            go xs start result
                | length xs < 2 * half = Prelude.reverse result ++ xs
                | otherwise =
                    let (block, rest) = Prelude.splitAt (2 * half) xs
                        (lo, hi) = Prelude.splitAt half block
                        tw_start = (n `div` (2 * half)) * start
                        twiddles = [twiddle omega (tw_start + k * (n `div` (2 * half))) q | k <- [0..half-1]]
                        butterflies = zipWith3 (\u v tw -> butterfly u v tw q) lo hi twiddles
                        lo' = map Prelude.fst butterflies
                        hi' = map Prelude.snd butterflies
                    in go rest (start + 1) (Prelude.reverse (lo' ++ hi') ++ result)
        in go a 0 []

-- | Iterative NTT using Cooley-Tukey
ntt_iter :: [Int] -> Int -> Int -> Int -> [Int]
ntt_iter a omega q n = go a 1
  where
    go a' len
        | len > n `div` 2 = a'
        | otherwise = go (ntt_layer_ct a' omega q n len) (len * 2)

-- | Cooley-Tukey NTT layer
ntt_layer_ct :: [Int] -> Int -> Int -> Int -> Int -> [Int]
ntt_layer_ct a omega q n len =
    let numBlocks = n `div` (2 * len)
        processBlock blockIdx =
            let start = blockIdx * 2 * len
                tw_base = blockIdx
                pairs = [(i, i + len) | i <- [0..len-1]]
            in Prelude.concatMap (\(i, j) ->
                let idx_lo = start + i
                    idx_hi = start + j
                    u = a Prelude.!! idx_lo
                    v = a Prelude.!! idx_hi
                    tw = twiddle omega (tw_base * (n `div` (2 * len))) q
                    (u', v') = butterfly u v tw q
                in [(idx_lo, u'), (idx_hi, v')]
                ) pairs
        updates = Prelude.concatMap processBlock [0..numBlocks-1]
    in applyUpdates a updates

applyUpdates :: [Int] -> [(Int, Int)] -> [Int]
applyUpdates a updates =
    let indexed = zip [0..] a
        updateMap = Prelude.foldr (\(i, v) m -> insertAt i v m) indexed updates
    in map Prelude.snd updateMap
  where
    insertAt idx val lst = map (\(i, v) -> if i == idx then (i, val) else (i, v)) lst

-- | Fast NTT using Cooley-Tukey: O(n log n)
-- Computes NTT using iterative butterfly operations
ntt_fast :: [Int] -> Int -> Int -> Int -> [Int]
ntt_fast a omega q n
    | length a /= n = Prelude.error "ntt_fast: input length must equal n"
    | otherwise = ntt_fast_impl a omega q n

ntt_fast_impl :: [Int] -> Int -> Int -> Int -> [Int]
ntt_fast_impl a omega q n = go (bit_reverse_copy a n) 1
  where
    go a' len
        | len >= n = a'
        | otherwise =
            let wlen = power_mod omega (n `div` (2 * len)) q
                a'' = process_stage a' len wlen
            in go a'' (len * 2)

    process_stage arr len wlen =
        let numGroups = n `div` (2 * len)
        in foldl (process_group len wlen) arr [0..numGroups-1]

    process_group len wlen arr groupIdx =
        let start = groupIdx * 2 * len
        in foldl (process_butterfly start len wlen) arr [0..len-1]

    process_butterfly start len wlen arr j =
        let w = power_mod wlen j q
            idx_u = start + j
            idx_v = start + j + len
            u = arr Prelude.!! idx_u
            v = arr Prelude.!! idx_v
            t = (v * w) `mod` q
            u' = (u + t) `mod` q
            v' = ((u - t) `mod` q + q) `mod` q
        in replaceAt idx_u u' (replaceAt idx_v v' arr)

-- | Fast inverse NTT: O(n log n)
intt_fast :: [Int] -> Int -> Int -> Int -> [Int]
intt_fast a_hat omega q n =
    let omega_inv = mod_inverse omega q
        n_inv = mod_inverse n q
        result = ntt_fast_impl a_hat omega_inv q n
    in map (\x -> (x * n_inv) `mod` q) result

-- | Bit-reversal permutation
bit_reverse_copy :: [Int] -> Int -> [Int]
bit_reverse_copy a n =
    let log_n = Prelude.floor (Prelude.logBase 2 (fromIntegral n :: Prelude.Double))
        bit_rev i = foldl (\acc b -> if testBit i b then setBit acc (log_n - 1 - b) else acc) 0 [0..log_n-1]
    in [a Prelude.!! bit_rev i | i <- [0..n-1]]

-- | Replace element at index
replaceAt :: Int -> a -> [a] -> [a]
replaceAt idx val lst = take idx lst ++ [val] ++ drop (idx + 1) lst

-- | Pointwise multiplication in NTT domain
ntt_pointwise_mult :: [Int] -> [Int] -> Int -> [Int]
ntt_pointwise_mult a_hat b_hat q = zipWith (\x y -> (x * y) `mod` q) a_hat b_hat

-- | Kyber NTT parameters: n=256, q=3329, omega=17
kyberNTTParams :: NTTParams
kyberNTTParams = NTTParams 256 3329 17

-- | Dilithium NTT parameters: n=256, q=8380417, omega=1753
dilithiumNTTParams :: NTTParams
dilithiumNTTParams = NTTParams 256 8380417 1753
