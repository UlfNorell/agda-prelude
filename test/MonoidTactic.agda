
module MonoidTactic where

open import Prelude
open import Data.Traversable
open import Data.Monoid.Laws
open import Tactic.Monoid
open import Tactic.Reflection

MonoidAnd : Monoid Bool
mempty {{MonoidAnd}} = true
_<>_   {{MonoidAnd}} = _&&_

MonoidLawsAnd : MonoidLaws Bool {{MonoidAnd}}
idLeft  {{MonoidLawsAnd}} x = refl
idRight {{MonoidLawsAnd}} false = refl
idRight {{MonoidLawsAnd}} true  = refl
<>assoc {{MonoidLawsAnd}} true  y z = refl
<>assoc {{MonoidLawsAnd}} false y z = refl

test₁ : (a b : Bool) → (a && (b && a && true)) ≡ ((a && b) && a)
test₁ a b = auto-monoid {{Laws = MonoidLawsAnd}}

test₂ : ∀ {a} {A : Set a} {{Mon : Monoid A}} {{Laws : MonoidLaws A}} →
          (x y : A) → x <> (y <> x <> mempty) ≡ (x <> y) <> x
test₂ x y = auto-monoid

test₃ : ∀ {a} {A : Set a} (xs ys zs : List A) → xs ++ ys ++ zs ≡ (xs ++ []) ++ (ys ++ []) ++ zs
test₃ xs ys zs = runT monoidTactic
