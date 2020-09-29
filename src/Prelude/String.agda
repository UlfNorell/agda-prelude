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

-- Eq --

instance
  EqString : Eq String
  _==_ {{EqString}} x y with primStringEquality x y
  ... | true  = yes unsafeEqual
  ... | false = no  unsafeNotEqual

-- Ord --

instance
  OrdString : Ord String
  OrdString = OrdBy unpackString-inj

  OrdLawsString : Ord/Laws String
  OrdLawsString = OrdLawsBy unpackString-inj

-- Overloaded literals --

instance
  StringIsString : IsString String
  IsString.Constraint StringIsString _ = ⊤
  IsString.fromString StringIsString s = s

  ListIsString : IsString (List Char)
  IsString.Constraint ListIsString _ = ⊤
  IsString.fromString ListIsString s = unpackString s

-- Monoid --

instance
  open import Prelude.Monoid
  SemigroupString : Semigroup String
  _<>_   {{SemigroupString}} = primStringAppend

  MonoidString : Monoid String
  Monoid.super MonoidString = it
  mempty {{MonoidString}} = ""


-- More functions --

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

onChars : (List Char → List Char) → String → String
onChars f = packString ∘ f ∘ unpackString

words : String → List String
words = map packString ∘ wordsBy isSpace ∘ unpackString

ltrim : String → String
ltrim = onChars (dropWhile isSpace)

rtrim : String → String
rtrim = onChars (reverse ∘ dropWhile isSpace ∘ reverse)

trim : String → String
trim = rtrim ∘ ltrim

strTake : Nat → String → String
strTake n = onChars (take n)

strDrop : Nat → String → String
strDrop n = onChars (drop n)

strLength : String → Nat
strLength = length ∘ unpackString

strIsPrefixOf? : String → String → Bool
strIsPrefixOf? = isPrefixOf? on unpackString

strCommonPrefix : String → String → String
strCommonPrefix s₁ s₂ = packString $ (commonPrefix! on unpackString) s₁ s₂
