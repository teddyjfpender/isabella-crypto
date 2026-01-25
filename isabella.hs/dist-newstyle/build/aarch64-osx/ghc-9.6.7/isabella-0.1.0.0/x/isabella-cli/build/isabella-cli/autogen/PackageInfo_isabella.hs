{-# LANGUAGE NoRebindableSyntax #-}
{-# OPTIONS_GHC -fno-warn-missing-import-lists #-}
{-# OPTIONS_GHC -w #-}
module PackageInfo_isabella (
    name,
    version,
    synopsis,
    copyright,
    homepage,
  ) where

import Data.Version (Version(..))
import Prelude

name :: String
name = "isabella"
version :: Version
version = Version [0,1,0,0] []

synopsis :: String
synopsis = "Formally verified lattice cryptography from Isabelle/HOL"
copyright :: String
copyright = ""
homepage :: String
homepage = ""
