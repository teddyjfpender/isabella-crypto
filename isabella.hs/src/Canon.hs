{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

-- | Canon: Formally verified lattice cryptography from Isabelle/HOL
--
-- This module re-exports all functionality from the Canon library.
-- All code is extracted from proven-correct Isabelle specifications.
--
-- = Overview
--
-- The Canon library provides the foundational building blocks for
-- lattice-based cryptography:
--
-- * "Canon.Algebra.Zq" - Modular arithmetic over Z_q
-- * "Canon.Linear.ListVec" - Vector and matrix operations
--
-- = Example Usage
--
-- @
-- import Canon
--
-- -- Centered modular reduction
-- x = mod_centered 7 5  -- Result: 2 (since 7 mod 5 = 2, and 2 <= 5/2)
--
-- -- Vector operations
-- v1 = [1, 2, 3]
-- v2 = [4, 5, 6]
-- dot = inner_prod v1 v2  -- Result: 32
--
-- -- Bit encoding for LWE
-- encoded = encode_bit 256 True   -- Result: 128 (q/2)
-- decoded = decode_bit 256 130    -- Result: True (close to q/2)
-- @
module Canon (
    -- * Re-exports
    module Canon.Algebra.Zq,
    module Canon.Linear.ListVec
) where

import Canon.Algebra.Zq
import Canon.Linear.ListVec
