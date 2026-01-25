{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

-- | Module-LWE and Module-SIS definitions
-- Generated from Canon/Rings/ModuleLWE.thy
module Canon.Rings.ModuleLWE (
    -- * Module element validation
    valid_mod_elem, valid_mod_matrix,
    -- * Module operations
    mod_inner_prod, mod_mat_vec_mult, mod_add, mod_sub,
    -- * M-LWE Parameters
    MLWEParams(..), makeMLWEParams, validMLWEParams,
    mlwe_n, mlwe_k, mlwe_kp, mlwe_q, mlwe_eta,
    -- * M-LWE Instance
    MLWEInstance(..), validMLWEInstance, mlwe_sample,
    mlwe_A, mlwe_b,
    -- * Secret/Error validation
    poly_coeffs_bounded, mod_elem_small,
    valid_mlwe_secret, valid_mlwe_error,
    mlwe_witness_valid,
    -- * M-SIS Parameters
    MSISParams(..), makeMSISParams, validMSISParams,
    msis_n, msis_k, msis_m, msis_q, msis_beta,
    -- * M-SIS Instance
    MSISInstance(..), validMSISInstance,
    msis_A,
    is_zero_mod_elem, is_msis_solution
) where

import Prelude ((+), (-), (*), mod, (==), (>), (>=), (&&), not,
                Bool(..), Int, map, length, zipWith, all, foldl, replicate)
import qualified Prelude
import Canon.Rings.PolyMod (Poly, ring_mult, ring_add, ring_sub, ring_mod)
import Canon.Analysis.Norms (all_bounded)

-- | Module element (vector of polynomials)
type ModElem = [Poly]

-- | Module matrix (matrix of polynomials)
type ModMatrix = [[Poly]]

-- | Validate module element: k polynomials each of degree n
valid_mod_elem :: Int -> Int -> ModElem -> Bool
valid_mod_elem k n v = length v == k && all (\p -> length p == n) v

-- | Validate module matrix: k x k' matrix of polynomials
valid_mod_matrix :: Int -> Int -> Int -> ModMatrix -> Bool
valid_mod_matrix k kp n m =
    length m == k &&
    all (\row -> length row == kp && all (\p -> length p == n) row) m

-- | Module inner product: sum of ring products
mod_inner_prod :: ModElem -> ModElem -> Int -> Int -> Poly
mod_inner_prod u v n q =
    let products = zipWith (\a b -> ring_mult a b n q) u v
        zero = replicate n 0
    in foldl (\acc p -> ring_add acc p n q) zero products

-- | Module matrix-vector multiplication
mod_mat_vec_mult :: ModMatrix -> ModElem -> Int -> Int -> ModElem
mod_mat_vec_mult m v n q = map (\row -> mod_inner_prod row v n q) m

-- | Module element addition
mod_add :: ModElem -> ModElem -> Int -> Int -> ModElem
mod_add u v n q = zipWith (\a b -> ring_add a b n q) u v

-- | Module element subtraction
mod_sub :: ModElem -> ModElem -> Int -> Int -> ModElem
mod_sub u v n q = zipWith (\a b -> ring_sub a b n q) u v

-- | M-LWE parameters
data MLWEParams = MLWEParams {
    mlwe_n :: Int,    -- ^ Polynomial degree
    mlwe_k :: Int,    -- ^ Module dimension
    mlwe_kp :: Int,   -- ^ Number of samples
    mlwe_q :: Int,    -- ^ Modulus
    mlwe_eta :: Int   -- ^ Noise bound
} deriving (Prelude.Show, Prelude.Eq)

-- | Create M-LWE parameters
makeMLWEParams :: Int -> Int -> Int -> Int -> Int -> MLWEParams
makeMLWEParams = MLWEParams

-- | Validate M-LWE parameters
validMLWEParams :: MLWEParams -> Bool
validMLWEParams p =
    mlwe_n p > 0 &&
    mlwe_k p > 0 &&
    mlwe_kp p > 0 &&
    mlwe_q p > 1 &&
    mlwe_eta p >= 0

-- | M-LWE instance
data MLWEInstance = MLWEInstance {
    mlwe_A :: ModMatrix,  -- ^ Public matrix
    mlwe_b :: ModElem     -- ^ Public vector b = As + e
} deriving (Prelude.Show, Prelude.Eq)

-- | Validate M-LWE instance
validMLWEInstance :: MLWEParams -> MLWEInstance -> Bool
validMLWEInstance p inst =
    valid_mod_matrix (mlwe_kp p) (mlwe_k p) (mlwe_n p) (mlwe_A inst) &&
    valid_mod_elem (mlwe_kp p) (mlwe_n p) (mlwe_b inst)

-- | Generate M-LWE sample: b = As + e
mlwe_sample :: ModMatrix -> ModElem -> ModElem -> Int -> Int -> ModElem
mlwe_sample a s e n q = mod_add (mod_mat_vec_mult a s n q) e n q

-- | Check if polynomial coefficients are bounded
poly_coeffs_bounded :: Poly -> Int -> Bool
poly_coeffs_bounded p eta = all_bounded p eta

-- | Check if module element is small
mod_elem_small :: ModElem -> Int -> Bool
mod_elem_small v eta = all (\p -> poly_coeffs_bounded p eta) v

-- | Validate M-LWE secret
valid_mlwe_secret :: MLWEParams -> ModElem -> Bool
valid_mlwe_secret p s =
    valid_mod_elem (mlwe_k p) (mlwe_n p) s &&
    mod_elem_small s (mlwe_eta p)

-- | Validate M-LWE error
valid_mlwe_error :: MLWEParams -> ModElem -> Bool
valid_mlwe_error p e =
    valid_mod_elem (mlwe_kp p) (mlwe_n p) e &&
    mod_elem_small e (mlwe_eta p)

-- | Validate M-LWE witness
mlwe_witness_valid :: MLWEParams -> MLWEInstance -> ModElem -> ModElem -> Bool
mlwe_witness_valid p inst s e =
    valid_mlwe_secret p s &&
    valid_mlwe_error p e &&
    mlwe_b inst == mlwe_sample (mlwe_A inst) s e (mlwe_n p) (mlwe_q p)

-- | M-SIS parameters
data MSISParams = MSISParams {
    msis_n :: Int,     -- ^ Polynomial degree
    msis_k :: Int,     -- ^ Number of rows
    msis_m :: Int,     -- ^ Number of columns
    msis_q :: Int,     -- ^ Modulus
    msis_beta :: Int   -- ^ Solution bound
} deriving (Prelude.Show, Prelude.Eq)

-- | Create M-SIS parameters
makeMSISParams :: Int -> Int -> Int -> Int -> Int -> MSISParams
makeMSISParams = MSISParams

-- | Validate M-SIS parameters
validMSISParams :: MSISParams -> Bool
validMSISParams p =
    msis_n p > 0 &&
    msis_k p > 0 &&
    msis_m p > 0 &&
    msis_q p > 1 &&
    msis_beta p > 0

-- | M-SIS instance
data MSISInstance = MSISInstance {
    msis_A :: ModMatrix  -- ^ Public matrix
} deriving (Prelude.Show, Prelude.Eq)

-- | Validate M-SIS instance
validMSISInstance :: MSISParams -> MSISInstance -> Bool
validMSISInstance p inst =
    valid_mod_matrix (msis_k p) (msis_m p) (msis_n p) (msis_A inst)

-- | Check if module element is zero
is_zero_mod_elem :: ModElem -> Bool
is_zero_mod_elem v = all (all (== 0)) v

-- | Check if z is M-SIS solution
is_msis_solution :: MSISParams -> MSISInstance -> ModElem -> Bool
is_msis_solution p inst z =
    valid_mod_elem (msis_m p) (msis_n p) z &&
    not (is_zero_mod_elem z) &&
    mod_elem_small z (msis_beta p) &&
    is_zero_mod_elem (mod_mat_vec_mult (msis_A inst) z (msis_n p) (msis_q p))
