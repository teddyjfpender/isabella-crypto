{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

-- | Vector norms and bounds
-- Generated from Canon/Analysis/Norms.thy
module Canon.Analysis.Norms (
    -- * L-infinity norm
    linf_norm,
    -- * Boundedness predicates
    all_bounded
) where

import Prelude ((+), (-), (*), (==), (<=), (>=), (&&), Bool(..), Int,
                map, maximum, abs, all, length, null)
import qualified Prelude

-- | L-infinity norm: maximum absolute value of elements
linf_norm :: [Int] -> Int
linf_norm v = if null v then 0 else maximum (map abs v)

-- | Check if all elements are bounded by B in absolute value
all_bounded :: [Int] -> Int -> Bool
all_bounded v b = all (\x -> abs x <= b) v
