-- | Canon.Dilithium: namespace-safe alias plus native Haskell wrappers for
-- the shared ML-DSA helper surface.
--
-- The generated module exports Isabelle-specific integer types. This facade
-- keeps those raw definitions available while also providing standard Haskell
-- 'Int'-based helpers for the cross-SDK API surface. Nat-valued wrapper
-- inputs are normalized with 'max 0' before calling the generated code, which
-- matches Isabelle's 'nat_of_integer' conversion.
module Canon.Dilithium
  ( module Canon.Crypto.Dilithium
  , DilithiumVariant(..)
  , DilithiumParams(..)
  , params
  , paramsByName
  , mldsa44Params
  , mldsa65Params
  , mldsa87Params
  , modCentered
  , power2Round
  , decompose
  , highBits
  , lowBits
  , makeHint
  , useHint
  , checkBound
  , hintWeight
  ) where

import Canon.Crypto.Dilithium
import qualified Canon.Crypto.Dilithium as Raw
import Data.Char (toLower)
import Prelude hiding (Int)
import qualified Prelude as Hs

data DilithiumVariant
  = MLDSA44
  | MLDSA65
  | MLDSA87
  deriving (Eq, Show)

data DilithiumParams = DilithiumParams
  { dilN :: Hs.Int
  , dilQ :: Hs.Int
  , dilK :: Hs.Int
  , dilL :: Hs.Int
  , dilEta :: Hs.Int
  , dilTau :: Hs.Int
  , dilBeta :: Hs.Int
  , dilGamma1 :: Hs.Int
  , dilGamma2 :: Hs.Int
  , dilD :: Hs.Int
  , dilOmega :: Hs.Int
  }
  deriving (Eq, Show)

toRawInt :: Hs.Int -> Raw.Int
toRawInt = Raw.Int_of_integer . Hs.toInteger

fromRawInt :: Raw.Int -> Hs.Int
fromRawInt = Hs.fromInteger . Raw.integer_of_int

toRawNat :: Hs.Int -> Raw.Nat
toRawNat = Raw.nat_of_integer . Hs.toInteger . Hs.max 0

fromRawNat :: Raw.Nat -> Hs.Int
fromRawNat = Hs.fromInteger . Raw.integer_of_nat

fromRawParams :: Raw.Dilithium_params_ext () -> DilithiumParams
fromRawParams raw =
  DilithiumParams
    { dilN = fromRawNat (Raw.dil_n raw)
    , dilQ = fromRawInt (Raw.dil_q raw)
    , dilK = fromRawNat (Raw.dil_k raw)
    , dilL = fromRawNat (Raw.dil_l raw)
    , dilEta = fromRawNat (Raw.dil_eta raw)
    , dilTau = fromRawNat (Raw.dil_tau raw)
    , dilBeta = fromRawNat (Raw.dil_beta raw)
    , dilGamma1 = fromRawInt (Raw.dil_gamma1 raw)
    , dilGamma2 = fromRawInt (Raw.dil_gamma2 raw)
    , dilD = fromRawNat (Raw.dil_d raw)
    , dilOmega = fromRawNat (Raw.dil_omega raw)
    }

params :: DilithiumVariant -> DilithiumParams
params MLDSA44 = mldsa44Params
params MLDSA65 = mldsa65Params
params MLDSA87 = mldsa87Params

paramsByName :: Hs.String -> Hs.Maybe DilithiumParams
paramsByName name =
  case Hs.map toLower name of
    "44" -> Hs.Just mldsa44Params
    "mldsa44" -> Hs.Just mldsa44Params
    "ml-dsa-44" -> Hs.Just mldsa44Params
    "65" -> Hs.Just mldsa65Params
    "mldsa65" -> Hs.Just mldsa65Params
    "ml-dsa-65" -> Hs.Just mldsa65Params
    "87" -> Hs.Just mldsa87Params
    "mldsa87" -> Hs.Just mldsa87Params
    "ml-dsa-87" -> Hs.Just mldsa87Params
    _ -> Hs.Nothing

mldsa44Params :: DilithiumParams
mldsa44Params = fromRawParams Raw.mldsa44_params

mldsa65Params :: DilithiumParams
mldsa65Params = fromRawParams Raw.mldsa65_params

mldsa87Params :: DilithiumParams
mldsa87Params = fromRawParams Raw.mldsa87_params

modCentered :: Hs.Int -> Hs.Int -> Hs.Int
modCentered r m = fromRawInt (Raw.mod_centered (toRawInt r) (toRawInt m))

power2Round :: Hs.Int -> Hs.Int -> (Hs.Int, Hs.Int)
power2Round r d =
  case Raw.power2round_coeff (toRawInt r) (toRawNat d) of
    (r1, r0) -> (fromRawInt r1, fromRawInt r0)

decompose :: Hs.Int -> Hs.Int -> (Hs.Int, Hs.Int)
decompose r alpha =
  case Raw.decompose_coeff (toRawInt r) (toRawInt alpha) of
    (r1, r0) -> (fromRawInt r1, fromRawInt r0)

highBits :: Hs.Int -> Hs.Int -> Hs.Int
highBits r alpha = fromRawInt (Raw.highbits_coeff (toRawInt r) (toRawInt alpha))

lowBits :: Hs.Int -> Hs.Int -> Hs.Int
lowBits r alpha = fromRawInt (Raw.lowbits_coeff (toRawInt r) (toRawInt alpha))

makeHint :: Hs.Int -> Hs.Int -> Hs.Int -> Hs.Int
makeHint z r alpha =
  fromRawNat (Raw.makehint_coeff (toRawInt z) (toRawInt r) (toRawInt alpha))

useHint :: Hs.Int -> Hs.Int -> Hs.Int -> Hs.Int
useHint h r alpha =
  fromRawInt (Raw.usehint_coeff (toRawNat h) (toRawInt r) (toRawInt alpha))

checkBound :: Hs.Int -> Hs.Int -> Hs.Bool
checkBound value bound = Raw.coeff_in_range (toRawInt value) (toRawInt bound)

hintWeight :: [[Hs.Int]] -> Hs.Int
hintWeight hints = fromRawNat (Raw.hint_weight (Hs.map (Hs.map toRawNat) hints))
