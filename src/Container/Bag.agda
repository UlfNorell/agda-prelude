
module Container.Bag where

open import Prelude

Bag : Set → Set
Bag A = List (Nat × A)

FunctorBag : Functor Bag
fmap {{FunctorBag}} f b = map (second f) b

union : {A : Set} {{OrdA : Ord A}} → Bag A → Bag A → Bag A
union a [] = a
union [] b = b
union ((i , x) ∷ a) ((j , y) ∷ b) =
  case-cmp compare x y
    less    _ => (i , x) ∷ union a ((j , y) ∷ b)
    equal   _ => (i + j , x) ∷ union a b
    greater _ => (j , y) ∷ union ((i , x) ∷ a) b
