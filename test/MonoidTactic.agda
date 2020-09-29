module MonoidTactic where

open import Prelude
open import Container.Traversable
open import Tactic.Monoid
open import Tactic.Reflection

SemigroupAnd : Semigroup Bool
_<>_   {{SemigroupAnd}} = _&&_

MonoidAnd : Monoid Bool
Monoid.super MonoidAnd = SemigroupAnd
mempty {{MonoidAnd}} = true


Monoid/LawsAnd : Monoid/Laws Bool
Monoid/Laws.super Monoid/LawsAnd = MonoidAnd
left-identity {{Monoid/LawsAnd}} x = refl
right-identity {{Monoid/LawsAnd}} true = refl
right-identity {{Monoid/LawsAnd}} false = refl
monoid-assoc {{Monoid/LawsAnd}} true y z = refl
monoid-assoc {{Monoid/LawsAnd}} false y z = refl


test₁ : (a b : Bool) → (a && (b && a && true)) ≡ ((a && b) && a)
test₁ a b = auto-monoid {{Laws = Monoid/LawsAnd}}

test₂ : ∀ {a} {A : Set a} {{Laws : Monoid/Laws A}} →
          (x y : A) → x <> (y <> x <> mempty) ≡ (x <> y) <> x
test₂ x y = auto-monoid

test₃ : ∀ {a} {A : Set a} (xs ys zs : List A) → xs ++ ys ++ zs ≡ (xs ++ []) ++ (ys ++ []) ++ zs
test₃ xs ys zs = runT monoidTactic
