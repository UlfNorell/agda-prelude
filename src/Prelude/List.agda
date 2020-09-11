module Prelude.List where

open import Prelude.List.Base public
open import Prelude.List.Properties using (MonoidLawsList) public

open import Prelude.List.MergeSort using (mergeSortBy ; mergeSort)
open import Prelude.Ord
open import Prelude.Variables

sortBy : {{_ : Ord B}} → (A → B) → List A → List A
sortBy proj = mergeSortBy (λ a b → proj a ≤? proj b)

sort : {{ Ord A}} → List A → List A
sort = mergeSort
