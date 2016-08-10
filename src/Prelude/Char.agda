
module Prelude.Char where

open import Prelude.Bool
open import Prelude.Nat
open import Prelude.Equality
open import Prelude.Equality.Unsafe
open import Prelude.Decidable
open import Prelude.Function
open import Prelude.Ord

open import Agda.Builtin.Char
open Agda.Builtin.Char public using (Char)

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

instance
  EqChar : Eq Char
  _==_ {{EqChar}} x y with eqChar x y
  ... | false = no  unsafeNotEqual
  ... | true  = yes unsafeEqual

-- Missing primitive isUpper
isUpper : Char → Bool
isUpper c = isNo (toLower c == c)

--- Ord ---

instance
  OrdChar : Ord Char
  OrdChar = OrdBy charToNat-inj
