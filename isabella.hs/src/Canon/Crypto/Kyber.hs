{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

-- | CRYSTALS-Kyber (ML-KEM) Key Encapsulation Mechanism
-- Generated from Canon/Crypto/Kyber.thy
--
-- FIPS 203 standardized lattice-based KEM for post-quantum security.
-- Uses Module-LWE hardness and O(n log n) NTT for efficiency.
module Canon.Crypto.Kyber (
    -- * Kyber Parameters
    KyberParams(..), makeKyberParams, validKyberParams,
    kyber_n, kyber_q, kyber_k, kyber_eta1, kyber_eta2, kyber_du, kyber_dv,
    kyber512Params, kyber768Params, kyber1024Params,
    -- * Key Types
    KyberPublicKey(..), KyberSecretKey(..), KyberCiphertext(..),
    pk_A, pk_t, sk_s, sk_pk, ct_u, ct_v,
    -- * Polynomial Types
    KyberPoly, KyberVec, KyberMatrix,
    -- * NTT Operations
    kyber_ntt, kyber_intt,
    -- * Polynomial Arithmetic
    kyber_poly_mult_ntt, kyber_poly_add, kyber_poly_sub,
    -- * Vector Operations
    kyber_vec_add, kyber_vec_ntt, kyber_vec_intt,
    kyber_inner_prod_ntt,
    -- * Matrix Operations
    kyber_mat_vec_mult_ntt, kyber_transpose,
    -- * Message Encoding
    kyber_encode_msg, kyber_decode_msg,
    -- * Core PKE Operations
    kyber_keygen, kyber_encrypt, kyber_decrypt,
    -- * KEM Operations
    kyber_encaps_simple, kyber_decaps_simple
) where

import Prelude ((+), (-), (*), div, mod, (==), (/=), (>), (>=), (<), (<=), (&&), (||),
                Bool(..), Int, map, foldl, zipWith, length, replicate,
                take, drop, (++), ($), otherwise, abs)
import qualified Prelude
import Canon.Rings.NTT (ntt_fast, intt_fast, ntt_pointwise_mult)

-- | Kyber polynomial: 256 coefficients mod q
type KyberPoly = [Int]

-- | Kyber vector: k polynomials
type KyberVec = [KyberPoly]

-- | Kyber matrix: k x k polynomials
type KyberMatrix = [[KyberPoly]]

-- | Kyber parameters
data KyberParams = KyberParams {
    kyber_n :: Int,      -- ^ Polynomial degree (always 256)
    kyber_q :: Int,      -- ^ Modulus (always 3329)
    kyber_k :: Int,      -- ^ Module dimension (2, 3, or 4)
    kyber_eta1 :: Int,   -- ^ Noise parameter for keygen
    kyber_eta2 :: Int,   -- ^ Noise parameter for encryption
    kyber_du :: Int,     -- ^ Compression parameter for u
    kyber_dv :: Int      -- ^ Compression parameter for v
} deriving (Prelude.Show, Prelude.Eq)

-- | Create Kyber parameters
makeKyberParams :: Int -> Int -> Int -> Int -> Int -> Int -> Int -> KyberParams
makeKyberParams = KyberParams

-- | Validate Kyber parameters
validKyberParams :: KyberParams -> Bool
validKyberParams p =
    kyber_n p == 256 &&
    kyber_q p == 3329 &&
    kyber_k p `Prelude.elem` [2, 3, 4] &&
    kyber_eta1 p > 0 &&
    kyber_eta2 p > 0 &&
    kyber_du p > 0 && kyber_du p <= 12 &&
    kyber_dv p > 0 && kyber_dv p <= 12

-- | Kyber-512 parameters (NIST Level 1)
kyber512Params :: KyberParams
kyber512Params = KyberParams 256 3329 2 3 2 10 4

-- | Kyber-768 parameters (NIST Level 3)
kyber768Params :: KyberParams
kyber768Params = KyberParams 256 3329 3 2 2 10 4

-- | Kyber-1024 parameters (NIST Level 5)
kyber1024Params :: KyberParams
kyber1024Params = KyberParams 256 3329 4 2 2 11 5

-- | Kyber public key: matrix A and vector t = As + e
data KyberPublicKey = KyberPublicKey {
    pk_A :: KyberMatrix,  -- ^ Public matrix A
    pk_t :: KyberVec      -- ^ Public vector t = As + e
} deriving (Prelude.Show, Prelude.Eq)

-- | Kyber secret key: secret vector s and cached public key
data KyberSecretKey = KyberSecretKey {
    sk_s :: KyberVec,            -- ^ Secret vector s
    sk_pk :: KyberPublicKey      -- ^ Cached public key
} deriving (Prelude.Show, Prelude.Eq)

-- | Kyber ciphertext: compressed vectors u and v
data KyberCiphertext = KyberCiphertext {
    ct_u :: KyberVec,   -- ^ Encrypted vector u
    ct_v :: KyberPoly   -- ^ Encrypted polynomial v
} deriving (Prelude.Show, Prelude.Eq)

-- Constants for Kyber
kyberQ :: Int
kyberQ = 3329

kyberN :: Int
kyberN = 256

kyberOmega :: Int
kyberOmega = 17

-- | Forward NTT for Kyber polynomial
kyber_ntt :: KyberPoly -> KyberPoly
kyber_ntt a = ntt_fast a kyberOmega kyberQ kyberN

-- | Inverse NTT for Kyber polynomial
kyber_intt :: KyberPoly -> KyberPoly
kyber_intt a_hat = intt_fast a_hat kyberOmega kyberQ kyberN

-- | Polynomial multiplication via NTT
-- c = INTT(NTT(a) * NTT(b))
kyber_poly_mult_ntt :: KyberPoly -> KyberPoly -> KyberPoly
kyber_poly_mult_ntt a b =
    let a_hat = kyber_ntt a
        b_hat = kyber_ntt b
        c_hat = ntt_pointwise_mult a_hat b_hat kyberQ
    in kyber_intt c_hat

-- | Polynomial addition mod q
kyber_poly_add :: KyberPoly -> KyberPoly -> KyberPoly
kyber_poly_add a b = zipWith (\x y -> (x + y) `mod` kyberQ) a b

-- | Polynomial subtraction mod q
kyber_poly_sub :: KyberPoly -> KyberPoly -> KyberPoly
kyber_poly_sub a b = zipWith (\x y -> ((x - y) `mod` kyberQ + kyberQ) `mod` kyberQ) a b

-- | Vector addition
kyber_vec_add :: KyberVec -> KyberVec -> KyberVec
kyber_vec_add = zipWith kyber_poly_add

-- | Apply NTT to each polynomial in vector
kyber_vec_ntt :: KyberVec -> KyberVec
kyber_vec_ntt = map kyber_ntt

-- | Apply inverse NTT to each polynomial in vector
kyber_vec_intt :: KyberVec -> KyberVec
kyber_vec_intt = map kyber_intt

-- | Inner product of two vectors in NTT domain
kyber_inner_prod_ntt :: KyberVec -> KyberVec -> KyberPoly
kyber_inner_prod_ntt u v =
    let products = zipWith (\a b -> ntt_pointwise_mult a b kyberQ) u v
        zero = replicate kyberN 0
    in foldl kyber_poly_add zero products

-- | Matrix-vector multiplication in NTT domain
kyber_mat_vec_mult_ntt :: KyberMatrix -> KyberVec -> KyberVec
kyber_mat_vec_mult_ntt a_hat s_hat =
    map (\row -> kyber_inner_prod_ntt row s_hat) a_hat

-- | Matrix transpose
kyber_transpose :: KyberMatrix -> KyberMatrix
kyber_transpose [] = []
kyber_transpose ([]:_) = []
kyber_transpose rows = map Prelude.head rows : kyber_transpose (map Prelude.tail rows)

-- | Encode message bits as polynomial
-- Each bit b is encoded as b * round(q/2)
kyber_encode_msg :: [Int] -> KyberPoly
kyber_encode_msg msg =
    let halfQ = (kyberQ + 1) `div` 2
    in map (\b -> if b == 1 then halfQ else 0) (take kyberN msg)

-- | Decode polynomial to message bits
-- Decode by checking if coefficient is closer to 0 or q/2
kyber_decode_msg :: KyberPoly -> [Int]
kyber_decode_msg v =
    let halfQ = (kyberQ + 1) `div` 2
        quarterQ = (kyberQ + 2) `div` 4
        centered x = let r = x `mod` kyberQ in if r > kyberQ `div` 2 then r - kyberQ else r
        decode c = if abs (centered c) > quarterQ then 1 else 0
    in map decode v

-- | Key generation
-- Returns (public key, secret key)
kyber_keygen :: KyberMatrix -> KyberVec -> KyberVec -> (KyberPublicKey, KyberSecretKey)
kyber_keygen a s e =
    let a_hat = map (map kyber_ntt) a
        s_hat = kyber_vec_ntt s
        e_hat = kyber_vec_ntt e
        t_hat = kyber_vec_add (kyber_mat_vec_mult_ntt a_hat s_hat) e_hat
        t = kyber_vec_intt t_hat
        pk = KyberPublicKey a t
        sk = KyberSecretKey s pk
    in (pk, sk)

-- | Encryption
-- Takes public key, message, randomness (r, e1, e2)
kyber_encrypt :: KyberPublicKey -> [Int] -> KyberVec -> KyberVec -> KyberPoly -> KyberCiphertext
kyber_encrypt pk msg r e1 e2 =
    let a_hat = map (map kyber_ntt) (pk_A pk)
        t_hat = kyber_vec_ntt (pk_t pk)
        r_hat = kyber_vec_ntt r
        -- u = A^T * r + e1
        at_hat = kyber_transpose a_hat
        u_hat = kyber_mat_vec_mult_ntt at_hat r_hat
        u = kyber_vec_add (kyber_vec_intt u_hat) e1
        -- v = t^T * r + e2 + encode(msg)
        v_hat = kyber_inner_prod_ntt t_hat r_hat
        v_base = kyber_poly_add (kyber_intt v_hat) e2
        v = kyber_poly_add v_base (kyber_encode_msg msg)
    in KyberCiphertext u v

-- | Decryption
-- Takes secret key and ciphertext, returns message
kyber_decrypt :: KyberSecretKey -> KyberCiphertext -> [Int]
kyber_decrypt sk ct =
    let s_hat = kyber_vec_ntt (sk_s sk)
        u_hat = kyber_vec_ntt (ct_u ct)
        -- v - s^T * u
        inner_hat = kyber_inner_prod_ntt s_hat u_hat
        inner = kyber_intt inner_hat
        m_poly = kyber_poly_sub (ct_v ct) inner
    in kyber_decode_msg m_poly

-- | Simple KEM encapsulation (for demonstration)
-- In practice, uses hashing for CCA security
kyber_encaps_simple :: KyberPublicKey -> [Int] -> KyberVec -> KyberVec -> KyberPoly -> ([Int], KyberCiphertext)
kyber_encaps_simple pk msg r e1 e2 =
    let ct = kyber_encrypt pk msg r e1 e2
    in (msg, ct)  -- In real Kyber, shared secret is derived via hash

-- | Simple KEM decapsulation
kyber_decaps_simple :: KyberSecretKey -> KyberCiphertext -> [Int]
kyber_decaps_simple = kyber_decrypt
