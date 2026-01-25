-- |
-- Module      : Lattice
-- Description : Formally verified lattice cryptography
-- License     : MIT
--
-- This module provides access to lattice cryptographic primitives that have been
-- formally verified in Isabelle/HOL and extracted to Haskell.
--
-- All code in this library is generated from proven-correct specifications.
-- The proofs guarantee correctness properties such as:
--
-- * Decryption correctly recovers the plaintext when noise is bounded
-- * Encoding and decoding are inverses
-- * Matrix/vector operations satisfy expected algebraic properties
--
-- == Usage
--
-- Import the specific module you need:
--
-- @
-- import qualified Lattice.LWE as LWE
-- import qualified Lattice.LWE_Regev as Regev
-- @
--
-- Or import everything qualified:
--
-- @
-- import qualified Lattice.LWE
-- import qualified Lattice.LWE_Regev
-- @

module Lattice
    ( -- * Available Modules
      --
      -- | This library provides the following verified implementations:
      --
      -- * "Lattice.LWE" - Basic LWE encryption scheme
      -- * "Lattice.LWE_Regev" - Regev's LWE public-key encryption
      --
      -- Import them directly as they have overlapping definitions.
    ) where

-- Note: The modules are not re-exported here because they have
-- overlapping definitions (Int, lwe_encrypt, etc.).
-- Import them directly:
--   import qualified Lattice.LWE as LWE
--   import qualified Lattice.LWE_Regev as Regev
