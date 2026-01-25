{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

-- | Learning With Errors (LWE) problem definition
-- Generated from Canon/Hardness/LWE_Def.thy
module Canon.Hardness.LWE_Def (
    -- * LWE Parameters
    LWEParams(..), makeLWEParams, validLWEParams,
    lwe_n, lwe_m, lwe_q, lwe_Bs, lwe_Be,
    -- * LWE Instance
    LWEInstance(..), validLWEInstance,
    lwe_A, lwe_b,
    -- * LWE Operations
    lwe_sample, makeLWEInstance,
    -- * Secret/Error validation
    valid_secret, valid_error,
    -- * LWE Witness
    lwe_residual, lwe_witness_valid
) where

import Prelude ((+), (-), (*), mod, (==), (>), (>=), (&&),
                Bool(..), Int, map, length, zipWith, min)
import qualified Prelude
import Canon.Linear.ListVec (Int_vec, Int_matrix, valid_vec, valid_matrix,
                              mat_vec_mult, vec_add, vec_sub, inner_prod)
import Canon.Algebra.Zq (vec_mod, vec_mod_centered)
import Canon.Analysis.Norms (all_bounded)

-- | LWE parameters
data LWEParams = LWEParams {
    lwe_n :: Int,   -- ^ Dimension of secret
    lwe_m :: Int,   -- ^ Number of samples (rows of A)
    lwe_q :: Int,   -- ^ Modulus
    lwe_Bs :: Int,  -- ^ Bound on secret coefficients
    lwe_Be :: Int   -- ^ Bound on error coefficients
} deriving (Prelude.Show, Prelude.Eq)

-- | Create LWE parameters
makeLWEParams :: Int -> Int -> Int -> Int -> Int -> LWEParams
makeLWEParams = LWEParams

-- | Validate LWE parameters
validLWEParams :: LWEParams -> Bool
validLWEParams p =
    lwe_n p > 0 &&
    lwe_m p > 0 &&
    lwe_q p > 1 &&
    lwe_Bs p >= 0 &&
    lwe_Be p >= 0

-- | LWE instance: matrix A and vector b
data LWEInstance = LWEInstance {
    lwe_A :: Int_matrix,  -- ^ Public matrix A (m x n)
    lwe_b :: Int_vec      -- ^ Public vector b = As + e mod q
} deriving (Prelude.Show, Prelude.Eq)

-- | Validate LWE instance dimensions
validLWEInstance :: LWEParams -> LWEInstance -> Bool
validLWEInstance p inst =
    valid_matrix (lwe_m p) (lwe_n p) (lwe_A inst) &&
    valid_vec (lwe_m p) (lwe_b inst)

-- | Generate LWE sample: b = A*s + e mod q
lwe_sample :: Int_matrix -> Int_vec -> Int_vec -> Int -> Int_vec
lwe_sample a s e q = vec_mod (vec_add (mat_vec_mult a s) e) q

-- | Create LWE instance from A, s, e
makeLWEInstance :: Int_matrix -> Int_vec -> Int_vec -> Int -> LWEInstance
makeLWEInstance a s e q = LWEInstance a (lwe_sample a s e q)

-- | Validate secret vector
valid_secret :: LWEParams -> Int_vec -> Bool
valid_secret p s =
    valid_vec (lwe_n p) s &&
    all_bounded s (lwe_Bs p)

-- | Validate error vector
valid_error :: LWEParams -> Int_vec -> Bool
valid_error p e =
    valid_vec (lwe_m p) e &&
    all_bounded e (lwe_Be p)

-- | LWE residual: b - A*s mod q
lwe_residual :: LWEInstance -> Int_vec -> Int -> Int_vec
lwe_residual inst s q = vec_mod (vec_sub (lwe_b inst) (mat_vec_mult (lwe_A inst) s)) q

-- | Validate LWE witness (s, e)
lwe_witness_valid :: LWEParams -> LWEInstance -> Int_vec -> Int_vec -> Bool
lwe_witness_valid p inst s e =
    valid_secret p s &&
    valid_error p e &&
    lwe_b inst == lwe_sample (lwe_A inst) s e (lwe_q p)
