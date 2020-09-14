module Prelude.List.Sorting.MergeSort.Merge where


open import Prelude.Bool
open import Prelude.Nat
open import Prelude.Nat.Properties

open import Prelude.Product

open import Prelude.List.Base

open import Prelude.Equality
open import Prelude.Ord
open import Control.WellFounded

open import Prelude.Variables

open import Prelude.List.Sorting.MergeSort.Divide

mergeBy : (A → A → Bool) → List A → List A → List A
mergeBy rel [] l₂ = l₂
mergeBy rel l₁@(_ ∷ _) [] = l₁
mergeBy rel (x ∷ xs) (y ∷ ys) =
  if rel x y
  then x ∷ mergeBy rel xs (y ∷ ys)
  else y ∷ mergeBy rel (x ∷ xs) ys


module WellFounded where
  mergeSortBy' : (A → A → Bool) → (l : List A)
               → (@0 acc : Acc _<_ (length l))
               → List A
  mergeSortBy' _≤?_ [] _ = []
  mergeSortBy' _≤?_ (x ∷ []) _ = x ∷ []
  mergeSortBy' _≤?_ l@(_ ∷ _ ∷ xs) (acc getLt) =
    let (l₁ , l₂) = divide l
    in mergeBy _≤?_ (mergeSortBy'
                      _≤?_ l₁
                      (getLt (length l₁) (divide-fst-lt-tot
                                    l (diff (length xs)
                                            (cong suc (add-commute 1 _))))))
                    (mergeSortBy'
                      _≤?_ l₂
                      (getLt (length l₂) (divide-snd-lt-tot
                                    l (diff (length xs)
                                            (cong suc (add-commute 1 _))))))

  wfList : (l : List A) → Acc _<_ (length l)
  wfList [] = acc (λ { arr (diff _ ())})
  wfList l₂@(x ∷ xs) = wfNat (length l₂)

open WellFounded

mergeSortBy : (A → A → Bool) → (l : List A) → List A
mergeSortBy _≤?_ l = mergeSortBy' _≤?_ l (wfList l)

mergeSort : {{_ : Ord A}} → (xs : List A) → List A
mergeSort = mergeSortBy _≤?_
