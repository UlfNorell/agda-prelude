
module Prelude.String where

open import Agda.Primitive
open import Prelude.Unit
open import Prelude.Char
open import Prelude.Bool
open import Prelude.Nat
open import Prelude.List
open import Prelude.Maybe
open import Prelude.Equality
open import Prelude.Equality.Unsafe
open import Prelude.Decidable
open import Prelude.Ord
open import Prelude.Function
open import Prelude.Monad
open import Prelude.Semiring

open import Agda.Builtin.String public
open import Agda.Builtin.FromString public

unpackString = primStringToList
packString   = primStringFromList

unpackString-inj : ∀ {x y} → unpackString x ≡ unpackString y → x ≡ y
unpackString-inj {x} p with unpackString x
unpackString-inj refl | ._ = unsafeEqual

infixr 5 _&_
_&_ = primStringAppend

parseNat : String → Maybe Nat
parseNat = parseNat′ ∘ unpackString
  where
    pDigit : Char → Maybe Nat
    pDigit c =
      if isDigit c then just (charToNat c - charToNat '0')
                   else nothing

    pNat : Nat → List Char → Maybe Nat
    pNat n [] = just n
    pNat n (c ∷ s) = pDigit c >>= λ d → pNat (n * 10 + d) s

    parseNat′ : List Char → Maybe Nat
    parseNat′ [] = nothing
    parseNat′ (c ∷ s) = pDigit c >>= λ d → pNat d s

-- Eq --

private
  eqString = primStringEquality

  decEqString : (x y : String) → Dec (x ≡ y)
  decEqString x y with eqString x y
  ... | true  = yes unsafeEqual
  ... | false = no  unsafeNotEqual

instance
  EqString : Eq String
  EqString = record { _==_ = decEqString }

-- Ord --

instance
  OrdString : Ord String
  OrdString = OrdBy unpackString-inj

-- Overloaded literals --

instance
  StringIsString : IsString String
  IsString.Constraint StringIsString _ = ⊤
  IsString.fromString StringIsString s = s

  ListIsString : IsString (List Char)
  IsString.Constraint ListIsString _ = ⊤
  IsString.fromString ListIsString s = unpackString s
