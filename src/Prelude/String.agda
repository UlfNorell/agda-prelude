
module Prelude.String where

open import Prelude.Char
open import Prelude.Bool
open import Prelude.List
open import Prelude.Equality
open import Prelude.Equality.Unsafe
open import Prelude.Decidable
open import Prelude.Ord

postulate
  String : Set

{-# BUILTIN STRING String #-}
{-# COMPILED_TYPE String String #-}

--- Primitive operations ---

primitive
  primStringToList   : String → List Char
  primStringFromList : List Char → String
  primStringAppend   : String → String → String
  primStringEquality : String → String → Bool

unpackString = primStringToList
packString   = primStringFromList

unpackString-inj : ∀ {x y} → unpackString x ≡ unpackString y → x ≡ y
unpackString-inj {x} p with unpackString x
unpackString-inj refl | ._ = unsafeEqual

infixr 5 _&_
_&_ = primStringAppend

private
  eqString = primStringEquality

  decEqString : (x y : String) → Dec (x ≡ y)
  decEqString x y with eqString x y
  ... | true  = yes unsafeEqual
  ... | false = no  unsafeNotEqual

EqString : Eq String
EqString = record { _==_ = decEqString }

-- Ord --

OrdString : Ord String
OrdString = OrdBy unpackString-inj
  where O : Ord (List Char)
        O = OrdList
