{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

-- | SIS-based commitment scheme
-- Generated from Canon/Crypto/Commit_SIS.thy
module Canon.Crypto.Commit_SIS (
    -- * Commitment Parameters
    CommitParams(..), makeCommitParams, validCommitParams, commit_total_dim,
    cp_n1, cp_n2, cp_m, cp_q, cp_beta,
    -- * Commitment Key
    valid_commit_key,
    -- * Opening
    CommitOpening(..), makeOpening, validOpening, opening_vec,
    open_msg, open_rand,
    -- * Core Operations
    commit, verify_opening,
    -- * Security Reduction
    is_binding_break, binding_to_sis_witness
) where

import Prelude ((+), (-), (*), mod, (==), (/=), (>), (>=), (&&), not,
                Bool(..), Int, length, (++), take, drop)
import qualified Prelude
import Canon.Linear.ListVec (Int_vec, Int_matrix, valid_vec, valid_matrix,
                              mat_vec_mult, vec_sub)
import Canon.Algebra.Zq (vec_mod)
import Canon.Analysis.Norms (all_bounded)
import Canon.Hardness.SIS_Def (is_zero_vec)

-- | Commitment parameters
data CommitParams = CommitParams {
    cp_n1 :: Int,    -- ^ Message dimension
    cp_n2 :: Int,    -- ^ Randomness dimension
    cp_m :: Int,     -- ^ Output dimension (rows of key matrix)
    cp_q :: Int,     -- ^ Modulus
    cp_beta :: Int   -- ^ Bound on opening vector
} deriving (Prelude.Show, Prelude.Eq)

-- | Create commitment parameters
makeCommitParams :: Int -> Int -> Int -> Int -> Int -> CommitParams
makeCommitParams = CommitParams

-- | Validate commitment parameters
validCommitParams :: CommitParams -> Bool
validCommitParams p =
    cp_n1 p > 0 &&
    cp_n2 p > 0 &&
    cp_m p > 0 &&
    cp_q p > 1 &&
    cp_beta p > 0

-- | Total dimension of opening vector
commit_total_dim :: CommitParams -> Int
commit_total_dim p = cp_n1 p + cp_n2 p

-- | Validate commitment key (matrix A of size m x (n1 + n2))
valid_commit_key :: CommitParams -> Int_matrix -> Bool
valid_commit_key p a = valid_matrix (cp_m p) (commit_total_dim p) a

-- | Commitment opening (message, randomness)
data CommitOpening = CommitOpening {
    open_msg :: Int_vec,   -- ^ Message part
    open_rand :: Int_vec   -- ^ Randomness part
} deriving (Prelude.Show, Prelude.Eq)

-- | Create opening
makeOpening :: Int_vec -> Int_vec -> CommitOpening
makeOpening = CommitOpening

-- | Validate opening
validOpening :: CommitParams -> CommitOpening -> Bool
validOpening p op =
    valid_vec (cp_n1 p) (open_msg op) &&
    valid_vec (cp_n2 p) (open_rand op) &&
    all_bounded (opening_vec op) (cp_beta p)

-- | Full opening vector: message || randomness
opening_vec :: CommitOpening -> Int_vec
opening_vec op = open_msg op ++ open_rand op

-- | Compute commitment: c = A * (m || r) mod q
commit :: Int_matrix -> CommitOpening -> Int -> Int_vec
commit a op q = vec_mod (mat_vec_mult a (opening_vec op)) q

-- | Verify opening: check that c = A * (m || r) mod q
verify_opening :: Int_matrix -> CommitOpening -> Int_vec -> Int -> Bool
verify_opening a op c q = commit a op q == c

-- | Check if two openings constitute a binding break
-- (different openings to same commitment)
is_binding_break :: Int_matrix -> CommitOpening -> CommitOpening -> Int_vec -> Int -> Bool
is_binding_break a op1 op2 c q =
    verify_opening a op1 c q &&
    verify_opening a op2 c q &&
    opening_vec op1 /= opening_vec op2

-- | Extract SIS witness from binding break
-- If A*(m1||r1) = A*(m2||r2) mod q with different openings,
-- then z = (m1||r1) - (m2||r2) is a SIS solution
binding_to_sis_witness :: CommitOpening -> CommitOpening -> Int_vec
binding_to_sis_witness op1 op2 = vec_sub (opening_vec op1) (opening_vec op2)
