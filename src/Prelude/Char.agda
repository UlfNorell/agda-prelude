
module Prelude.Char where

open import Prelude.Nat
open import Prelude.Bool
open import Prelude.Equality
open import Prelude.Equality.Unsafe
open import Prelude.Decidable
open import Prelude.Function
open import Prelude.Ord

postulate Char : Set

{-# BUILTIN CHAR Char #-}
{-# COMPILED_TYPE Char Char #-}

--- Primitive operations ---

private
 primitive
  primIsLower primIsDigit primIsAlpha primIsSpace primIsAscii primIsLatin1 primIsPrint primIsHexDigit : Char → Bool
  primToUpper primToLower : Char → Char
  primCharToNat : Char → Nat
  primNatToChar : Nat → Char

isLower    = primIsLower
isDigit    = primIsDigit
isSpace    = primIsSpace
isAscii    = primIsAscii
isLatin1   = primIsLatin1
isPrint    = primIsPrint
isHexDigit = primIsHexDigit
isAlpha    = primIsAlpha

toUpper    = primToUpper
toLower    = primToLower

isAlphaNum : Char → Bool
isAlphaNum c = isAlpha c || isDigit c

charToNat  = primCharToNat
natToChar  = primNatToChar

charToNat-inj : ∀ {x y} → charToNat x ≡ charToNat y → x ≡ y
charToNat-inj {x} p with charToNat x
charToNat-inj refl | ._ = unsafeEqual  -- need to be strict in the proof!

--- Equality --

eqChar : Char → Char → Bool
eqChar = eqNat on charToNat

decEqChar : (x y : Char) → Dec (x ≡ y)
decEqChar x y with eqChar x y
... | false = no  unsafeNotEqual
... | true  = yes unsafeEqual

instance
  EqChar : Eq Char
  EqChar = record { _==_ = decEqChar }

-- Missing primitive isUpper
isUpper : Char → Bool
isUpper c = isNo (toLower c == c)

--- Ord ---

instance
  OrdChar : Ord Char
  OrdChar = OrdBy charToNat-inj
