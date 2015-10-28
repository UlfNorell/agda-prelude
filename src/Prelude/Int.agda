
module Prelude.Int where

open import Prelude.Unit
open import Prelude.Nat
open import Prelude.Number
open import Prelude.String
open import Prelude.Show

data Int : Set where
  pos    : Nat → Int
  negsuc : Nat → Int

{-# BUILTIN INTEGER       Int    #-}
{-# BUILTIN INTEGERPOS    pos    #-}
{-# BUILTIN INTEGERNEGSUC negsuc #-}

neg : Nat → Int
neg zero    = pos zero
neg (suc n) = negsuc n

instance
  NumInt : Number Int
  Number.Constraint NumInt _ = ⊤
  Number.fromNat    NumInt n = pos n

  NegInt : Negative Int
  Negative.Constraint NegInt _ = ⊤
  Negative.fromNeg    NegInt n = neg n

private
 primitive
  primShowInteger : Int → String

instance
  ShowInt : Show Int
  ShowInt = simpleShowInstance primShowInteger
