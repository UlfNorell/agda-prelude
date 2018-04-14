
module Container.List.Permutation where

open import Prelude
open import Container.List

data Permutation {a} {A : Set a} : List A → List A → Set a where
  []  : Permutation [] []
  _∷_ : ∀ {x xs ys} (i : x ∈ ys) → Permutation xs (deleteIx ys i) →
          Permutation (x ∷ xs) ys
