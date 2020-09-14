module Prelude.List.Sorting.InsertionSort.Properties where

open import Prelude.Equality
open import Prelude.Equality.Inspect
open import Prelude.Bool

open import Prelude.Function

open import Prelude.Product
open import Prelude.List.Base
open import Prelude.Ord
open import Prelude.Ord.Properties
open import Prelude.List.Sorting.InsertionSort

open import Prelude.List.Relations.Sorted
open import Prelude.List.Relations.Linked
open import Prelude.List.Relations.Any
open import Prelude.List.Relations.Permutation using (Permutation ; [] ; _∷_)
import Prelude.List.Relations.Permutation as Perm

open import Prelude.Variables

insertBy-SortedBy : (proj : A → B)
               → {{_ : Ord/Laws B}} → (x : A) → {xs : List A}
               → OrderedBy (λ a b → proj a ≤ proj b) xs
               → SortedBy (λ a b → proj a ≤ proj b)
                          (insertBy (λ a b → proj a ≤? proj b) x xs)
                          (x ∷ xs)
insertBy-SortedBy proj x [] = [-] , (zero refl ∷ [])
insertBy-SortedBy proj x ([-] {x = x₁})
  with inspect (proj x ≤? proj x₁)
...| true with≡ x≤?x₁ rewrite x≤?x₁ =
  (≤?⇒≤ x≤?x₁) ∷ [-] , (zero! ∷ (zero! ∷ []))
...| false with≡ x≰?x₁ rewrite x≰?x₁ =
  (≰?⇒≥ x≰?x₁ ∷ [-]) , (suc zero! ∷ (zero! ∷ []))
insertBy-SortedBy proj x {xs = x₁ ∷ x₂ ∷ xs} (_∷_  x₁≤x₂ ord[xs])
    with inspect (proj x ≤? proj x₁)
...| true with≡ x≤?x₁ rewrite x≤?x₁ =
  ((≤?⇒≤ x≤?x₁) ∷ x₁≤x₂ ∷ ord[xs])
  , zero! ∷ (zero! ∷ (zero! ∷ Perm.refl _))
...| false with≡ x≰?x₁ rewrite x≰?x₁
  with inspect (proj x ≤? proj x₂)
...| true with≡ x≤?x₂ rewrite x≤?x₂ =
  let (ord[rec] , perm[rec]) = insertBy-SortedBy proj x ord[xs]
  in (≰?⇒≥ x≰?x₁) ∷ ≤?⇒≤ x≤?x₂ ∷ ord[xs]
    , Perm.swap-cons-right (Perm.refl _)
...| false with≡ x≰?x₂
  with insertBy-SortedBy proj x ord[xs]
...| (ord[rec] , perm[rec]) rewrite x≰?x₂ =
  x₁≤x₂ ∷ ord[rec]
  , Perm.swap-cons-left (Perm.cons x₁ perm[rec])


insertionSortBy-SortedBy :
  {{_ : Ord/Laws B}}
  → (proj : A → B)
  → (xs : List A)
  → SortedBy (λ a b → proj a ≤ proj b)
             (insertionSortBy (λ a b → proj a ≤? proj b) xs)
             xs
insertionSortBy-SortedBy proj [] = [] , []
insertionSortBy-SortedBy proj (x ∷ xs)
  with insertionSortBy-SortedBy proj xs
...| ord[rec] , perm[rec] =
  let (ord[insertBy] , perm[insertBy] ) = insertBy-SortedBy proj x ord[rec]
  in ord[insertBy] , Perm.trans (Perm.cons x perm[rec]) perm[insertBy]

insertionSort-SortedBy :
  {{_ : Ord/Laws A}}
  → (xs : List A)
  → SortedBy _≤_ (insertionSortBy _≤?_ xs) xs
insertionSort-SortedBy = insertionSortBy-SortedBy id
