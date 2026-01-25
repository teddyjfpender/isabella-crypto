{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

-- | Short Integer Solution (SIS) problem definition
-- Generated from Canon/Hardness/SIS_Def.thy
module Canon.Hardness.SIS_Def (
    -- * SIS Parameters
    SISParams(..), makeSISParams, validSISParams,
    sis_n, sis_m, sis_q, sis_beta,
    -- * SIS Instance
    SISInstance(..), validSISInstance,
    sis_A,
    -- * SIS Solution
    is_zero_vec, is_sis_solution, in_kernel_mod,
    -- * ISIS (Inhomogeneous SIS)
    ISISInstance(..), validISISInstance, is_isis_solution,
    isis_t
) where

import Prelude ((==), (>), (/=), (&&), not, mod, all,
                Bool(..), Int, length)
import qualified Prelude
import Canon.Linear.ListVec (Int_vec, Int_matrix, valid_vec, valid_matrix,
                              mat_vec_mult)
import Canon.Algebra.Zq (vec_mod)
import Canon.Analysis.Norms (all_bounded)

-- | SIS parameters
data SISParams = SISParams {
    sis_n :: Int,      -- ^ Number of columns (dimension of solution)
    sis_m :: Int,      -- ^ Number of rows (number of equations)
    sis_q :: Int,      -- ^ Modulus
    sis_beta :: Int    -- ^ L-infinity bound on solution
} deriving (Prelude.Show, Prelude.Eq)

-- | Create SIS parameters
makeSISParams :: Int -> Int -> Int -> Int -> SISParams
makeSISParams = SISParams

-- | Validate SIS parameters
validSISParams :: SISParams -> Bool
validSISParams p =
    sis_n p > 0 &&
    sis_m p > 0 &&
    sis_q p > 1 &&
    sis_beta p > 0

-- | SIS instance: just a matrix A
data SISInstance = SISInstance {
    sis_A :: Int_matrix  -- ^ Public matrix A (m x n)
} deriving (Prelude.Show, Prelude.Eq)

-- | Validate SIS instance dimensions
validSISInstance :: SISParams -> SISInstance -> Bool
validSISInstance p inst = valid_matrix (sis_m p) (sis_n p) (sis_A inst)

-- | Check if vector is all zeros
is_zero_vec :: Int_vec -> Bool
is_zero_vec v = all (== 0) v

-- | Check if z is a valid SIS solution: A*z = 0 mod q, z short, z nonzero
is_sis_solution :: SISParams -> SISInstance -> Int_vec -> Bool
is_sis_solution p inst z =
    valid_vec (sis_n p) z &&
    not (is_zero_vec z) &&
    all_bounded z (sis_beta p) &&
    is_zero_vec (vec_mod (mat_vec_mult (sis_A inst) z) (sis_q p))

-- | Check if z is in kernel of A mod q
in_kernel_mod :: Int_matrix -> Int_vec -> Int -> Bool
in_kernel_mod a z q = is_zero_vec (vec_mod (mat_vec_mult a z) q)

-- | ISIS (Inhomogeneous SIS) instance
data ISISInstance = ISISInstance {
    isis_sis :: SISInstance,  -- ^ Underlying SIS instance
    isis_t :: Int_vec         -- ^ Target vector t
} deriving (Prelude.Show, Prelude.Eq)

-- | Validate ISIS instance
validISISInstance :: SISParams -> ISISInstance -> Bool
validISISInstance p inst =
    validSISInstance p (isis_sis inst) &&
    valid_vec (sis_m p) (isis_t inst)

-- | Check if z is ISIS solution: A*z = t mod q, z short
is_isis_solution :: SISParams -> ISISInstance -> Int_vec -> Bool
is_isis_solution p inst z =
    valid_vec (sis_n p) z &&
    all_bounded z (sis_beta p) &&
    vec_mod (mat_vec_mult (sis_A (isis_sis inst)) z) (sis_q p) == vec_mod (isis_t inst) (sis_q p)
