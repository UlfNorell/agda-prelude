-- Mapping of Haskell types to Agda Types
module Foreign.Haskell.Types where

open import Prelude
open import Builtin.Float

{-# FOREIGN GHC import qualified GHC.Float #-}
{-# FOREIGN GHC import qualified Data.Text #-}

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

{-# COMPILE GHC HSFloat = type Float #-}
{-# COMPILE GHC HSFloat=>Float = GHC.Float.float2Double #-}
{-# COMPILE GHC lossyFloat=>HSFloat = GHC.Float.double2Float #-}
{-# COMPILE GHC HSInt = type Int #-}
{-# COMPILE GHC HSInt=>Int = toInteger #-}
{-# COMPILE GHC lossyInt=>HSInt = fromInteger #-}

{-# FOREIGN GHC type AgdaTuple a b c d = (c, d) #-}

data HSTuple {a b} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  _,_ : A → B → HSTuple A B
{-# COMPILE GHC HSTuple = data MAlonzo.Code.Foreign.Haskell.Types.AgdaTuple ((,)) #-}
