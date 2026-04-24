{-# LANGUAGE NoRebindableSyntax #-}
{-# OPTIONS_GHC -fno-warn-missing-import-lists #-}
{-# OPTIONS_GHC -w #-}
module PackageInfo_Practica04 (
    name,
    version,
    synopsis,
    copyright,
    homepage,
  ) where

import Data.Version (Version(..))
import Prelude

name :: String
name = "Practica04"
version :: Version
version = Version [0,1,0,0] []

synopsis :: String
synopsis = "Practica 4: Algoritmo DPLL"
copyright :: String
copyright = ""
homepage :: String
homepage = ""
