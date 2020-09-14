module Prelude.List.Sorting.InsertionSort where

open import Prelude.Bool
open import Prelude.List.Base
open import Prelude.Ord
open import Prelude.Variables


insertBy : (_≤_ : A → A → Bool) → A → List A → List A
insertBy _ a [] = [ a ]
insertBy _≤?_ a (x ∷ xs) =
  if a ≤? x then a ∷ x ∷ xs else x ∷ insertBy _≤?_ a xs


insert : {{_ : Ord A}} → A → List A → List A
insert = insertBy _≤?_

insertionSortBy : (A → A → Bool) → List A → List A
insertionSortBy _ [] = []
insertionSortBy _≤_ (x ∷ xs) = insertBy _≤_ x (insertionSortBy' _≤_ xs)
