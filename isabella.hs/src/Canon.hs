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
-- == Algebra and Analysis
-- * "Canon.Algebra.Zq" - Modular arithmetic over Z_q
-- * "Canon.Linear.ListVec" - Vector and matrix operations
-- * "Canon.Analysis.Norms" - Vector norms and bounds
--
-- == Gadgets
-- * "Canon.Gadgets.Decomp" - Base-B gadget decomposition
--
-- == Hardness Assumptions
-- * "Canon.Hardness.LWE_Def" - Learning With Errors problem
-- * "Canon.Hardness.SIS_Def" - Short Integer Solution problem
--
-- == Polynomial Rings
-- * "Canon.Rings.PolyMod" - Polynomial ring arithmetic Z_q[X]/(X^n + 1)
-- * "Canon.Rings.ModuleLWE" - Module-LWE and Module-SIS
-- * "Canon.Rings.NTT" - Number Theoretic Transform (O(n log n) Cooley-Tukey)
--
-- == Cryptographic Schemes
-- * "Canon.Crypto.Regev_PKE" - Regev public-key encryption
-- * "Canon.Crypto.Commit_SIS" - SIS-based commitment scheme
-- * "Canon.Crypto.Kyber" - CRYSTALS-Kyber (ML-KEM) key encapsulation
--
-- = Example Usage
--
-- @
-- import Canon
--
-- -- Centered modular reduction
-- x = mod_centered 7 5  -- Result: 2
--
-- -- Vector operations
-- dot = inner_prod [1,2,3] [4,5,6]  -- Result: 32
--
-- -- Gadget decomposition
-- digits = decomp_base 2 8 42  -- Binary decomposition
--
-- -- Kyber KEM
-- import Canon.Crypto.Kyber (kyber768Params, kyber_keygen)
-- @
module Canon (
    -- * Algebra
    module Canon.Algebra.Zq,
    -- * Linear algebra
    module Canon.Linear.ListVec,
    -- * Analysis
    module Canon.Analysis.Norms,
    -- * Gadgets
    module Canon.Gadgets.Decomp,
    -- * Hardness
    module Canon.Hardness.LWE_Def,
    module Canon.Hardness.SIS_Def,
    -- * Polynomial rings
    module Canon.Rings.PolyMod,
    module Canon.Rings.ModuleLWE,
    module Canon.Rings.NTT,
    -- * Cryptographic schemes
    module Canon.Crypto.Regev_PKE,
    module Canon.Crypto.Commit_SIS,
    module Canon.Crypto.Kyber
) where

import Canon.Algebra.Zq
import Canon.Linear.ListVec
import Canon.Analysis.Norms
import Canon.Gadgets.Decomp
import Canon.Hardness.LWE_Def
import Canon.Hardness.SIS_Def
import Canon.Rings.PolyMod
import Canon.Rings.ModuleLWE
import Canon.Rings.NTT
import Canon.Crypto.Regev_PKE
import Canon.Crypto.Commit_SIS
import Canon.Crypto.Kyber
