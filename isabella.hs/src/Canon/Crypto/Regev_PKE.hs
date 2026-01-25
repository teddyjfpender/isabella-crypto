{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

-- | Regev public-key encryption scheme
-- Generated from Canon/Crypto/Regev_PKE.thy
module Canon.Crypto.Regev_PKE (
    -- * Regev Parameters
    RegevParams(..), makeRegevParams, validRegevParams,
    regev_Br,
    -- * Key/Ciphertext Types
    RegevPK, RegevSK, RegevCT,
    valid_pk, valid_sk, valid_ct, valid_randomness,
    -- * Core Operations
    regev_keygen, regev_encrypt, regev_decrypt,
    decrypt_payload
) where

import Prelude ((+), (-), (*), mod, div, (==), (>), (>=), (&&),
                Bool(..), Int, length, fst, snd)
import qualified Prelude
import Canon.Linear.ListVec (Int_vec, Int_matrix, valid_vec, valid_matrix,
                              mat_vec_mult, inner_prod, transpose)
import Canon.Algebra.Zq (vec_mod, encode_bit, decode_bit)
import Canon.Analysis.Norms (all_bounded)
import Canon.Hardness.LWE_Def (LWEParams(..), lwe_sample, valid_secret, valid_error)

-- | Regev parameters extend LWE parameters with randomness bound
data RegevParams = RegevParams {
    regev_lwe :: LWEParams,  -- ^ Underlying LWE parameters
    regev_Br :: Int          -- ^ Bound on randomness coefficients
} deriving (Prelude.Show, Prelude.Eq)

-- | Create Regev parameters
makeRegevParams :: Int -> Int -> Int -> Int -> Int -> Int -> RegevParams
makeRegevParams n m q bs be br = RegevParams (LWEParams n m q bs be) br

-- | Validate Regev parameters
validRegevParams :: RegevParams -> Bool
validRegevParams p =
    lwe_n (regev_lwe p) > 0 &&
    lwe_m (regev_lwe p) > 0 &&
    lwe_q (regev_lwe p) > 1 &&
    lwe_Bs (regev_lwe p) >= 0 &&
    lwe_Be (regev_lwe p) >= 0 &&
    regev_Br p >= 0

-- | Public key: (A, b) where b = As + e mod q
type RegevPK = (Int_matrix, Int_vec)

-- | Secret key: s
type RegevSK = Int_vec

-- | Ciphertext: (c1, c2)
type RegevCT = (Int_vec, Int)

-- | Validate public key
valid_pk :: RegevParams -> RegevPK -> Bool
valid_pk p pk =
    valid_matrix (lwe_m (regev_lwe p)) (lwe_n (regev_lwe p)) (fst pk) &&
    valid_vec (lwe_m (regev_lwe p)) (snd pk)

-- | Validate secret key
valid_sk :: RegevParams -> RegevSK -> Bool
valid_sk p sk = valid_vec (lwe_n (regev_lwe p)) sk

-- | Validate ciphertext
valid_ct :: RegevParams -> RegevCT -> Bool
valid_ct p ct = valid_vec (lwe_n (regev_lwe p)) (fst ct)

-- | Validate randomness
valid_randomness :: RegevParams -> Int_vec -> Bool
valid_randomness p r =
    valid_vec (lwe_m (regev_lwe p)) r &&
    all_bounded r (regev_Br p)

-- | Key generation: returns (pk, sk) = ((A, b), s)
regev_keygen :: Int_matrix -> Int_vec -> Int_vec -> Int -> (RegevPK, RegevSK)
regev_keygen a s e q = ((a, lwe_sample a s e q), s)

-- | Encryption: pk, randomness r, message bit -> ciphertext
-- c1 = A^T r mod q
-- c2 = <b, r> + encode(m) mod q
regev_encrypt :: RegevPK -> Int_vec -> Bool -> Int -> RegevCT
regev_encrypt pk r m q =
    let a = fst pk
        b = snd pk
        c1 = vec_mod (mat_vec_mult (transpose a) r) q
        c2 = (inner_prod b r + encode_bit q m) `mod` q
    in (c1, c2)

-- | Decrypt payload: c2 - <s, c1> mod q
decrypt_payload :: RegevSK -> RegevCT -> Int -> Int
decrypt_payload s ct q =
    let c1 = fst ct
        c2 = snd ct
    in ((c2 - inner_prod s c1) `mod` q + q) `mod` q

-- | Decryption: sk, ciphertext -> message bit
regev_decrypt :: RegevSK -> RegevCT -> Int -> Bool
regev_decrypt s ct q = decode_bit q (decrypt_payload s ct q)
