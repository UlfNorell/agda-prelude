-- Mapping of Haskell types to Agda Types
module Foreign.Haskell.Types where

open import Prelude
open import Builtin.Float

{-# IMPORT GHC.Float #-}
{-# IMPORT Data.Text #-}

HSUnit = ⊤
HSBool = Bool
HSInteger = Int

HSList = List

HSChar = Char
HSString = HSList HSChar
HSText = String

postulate
  HSFloat : Set
  HSFloat=>Float : HSFloat → Float
  lossyFloat=>HSFloat : Float → HSFloat

  HSInt : Set
  HSInt=>Int : HSInt → Int
  lossyInt=>HSInt : Int → HSInt

{-# COMPILED_TYPE HSFloat Float #-}
{-# COMPILED HSFloat=>Float GHC.Float.float2Double #-}
{-# COMPILED lossyFloat=>HSFloat GHC.Float.double2Float #-}
{-# COMPILED_TYPE HSInt Int #-}
{-# COMPILED HSInt=>Int toInteger #-}
{-# COMPILED lossyInt=>HSInt fromInteger #-}

{-# HASKELL type AgdaTuple a b c d = (c, d) #-}

data HSTuple {a b} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  _,_ : A → B → HSTuple A B
{-# COMPILED_DATA HSTuple MAlonzo.Code.Foreign.Haskell.Types.AgdaTuple (,) #-}
