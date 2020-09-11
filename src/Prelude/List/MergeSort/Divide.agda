module Prelude.List.MergeSort.Divide where

open import Prelude.Equality
open import Prelude.Semiring
open import Prelude.Product
open import Prelude.Bool
open import Prelude.Nat
open import Prelude.Ord
open import Prelude.List.Base

open import Prelude.Monoid
open import Prelude.List.Properties

open import Control.WellFounded
open import Prelude.List.Relations.Linked
open import Prelude.List.Relations.Any
open import Prelude.List.Relations.Permutation using (Permutation ; [] ; _∷_)
import Prelude.List.Relations.Permutation as Perm

open import Prelude.Nat.Properties

open import Prelude.Variables


-- Division mechanism, this version should, be faster since it does not require
-- memory of the recursion. It will reverse the list, but that doesn't
-- matter for merge sort
divideAccum : {A : Set ℓ} → List A → List A × List A → List A × List A
divideAccum [] (l₁ , l₂) = (l₁ , l₂)
divideAccum (x ∷ []) (l₁ , l₂) = ((x ∷ l₁) , l₂)
divideAccum (x₁ ∷ x₂ ∷ xs) (l₁ , l₂) =
  divideAccum xs ((x₁ ∷ l₁) , (x₂ ∷ l₂))

-- Actual list division function
divide : {A : Set ℓ} → List A → List A × List A
divide l = divideAccum l ([] , [])

-- Inverse of divide, used for proof
undivide : {A : Set ℓ}  → List A × List A → List A
undivide ([] , []) = []
undivide (xs@(_ ∷ _) , []) = xs
undivide ([] , ys@(_ ∷ _)) = ys
undivide (x ∷ xs ,  y ∷ ys) =
  x ∷ y ∷ undivide (xs , ys)


module Properties where

  divideAccum-length-sum :
    (l : List A)
    → (acc : List A × List A)
    → (length (fst (divideAccum l acc)) + length (snd (divideAccum l acc)))
      ≡ length l + length (fst acc) + length (snd acc)
  divideAccum-length-sum [] (l₁ , l₂) = refl
  divideAccum-length-sum (x ∷ []) (l₁ , l₂)  = refl
  divideAccum-length-sum l@(x₁ ∷ x₂ ∷ xs) acc@(l₁ , l₂) =
    divideAccum-length-sum xs (x₁ ∷ l₁ , x₂ ∷ l₂)
    ⟨≡⟩ add-suc-r _ _
    ⟨≡⟩ cong (λ z → suc (z + length l₂)) (add-suc-r (length xs) (length l₁))
    where
      open import Prelude.Nat.Properties

  divide-length-sum :
    (l : List A)
    → length (fst (divide l)) + length (snd (divide l))
      ≡ length l
  divide-length-sum l =
    divideAccum-length-sum l ([] , [])
    ⟨≡⟩ add-zero-r _ ⟨≡⟩ add-zero-r _
    where
      open import Prelude.Nat.Properties

  divideAccum-length-fst-l₁-suc :
    {A : Set ℓ} → {l₁ l₂ : List A} → (x₁ : A) → (xs : List A)
    → length (fst (divideAccum xs (x₁ ∷ l₁ , l₂)))
      ≡  suc (length (fst (divideAccum xs (l₁ , l₂))))
  divideAccum-length-fst-l₁-suc _ [] = refl
  divideAccum-length-fst-l₁-suc _ (_ ∷ []) = refl
  divideAccum-length-fst-l₁-suc {l₁ = l₁} {l₂ = l₂} x (y₁ ∷ y₂ ∷ ys) =
    divideAccum-length-fst-l₁-suc y₁ ys
    ⟨≡⟩ cong suc (divideAccum-length-fst-l₁-suc x ys)
    ⟨≡⟩ cong suc (sym (divideAccum-length-fst-l₁-suc y₁ ys))

  divideAccum-length-fst-l₂-head-indep :
      {A : Set ℓ} → {l₁ l₂ : List A} → (x : A) → (xs : List A)
      → length (fst (divideAccum xs (l₁ , x ∷ l₂)))
        ≡ length (fst (divideAccum xs (l₁ , l₂)))
  divideAccum-length-fst-l₂-head-indep _ [] = refl
  divideAccum-length-fst-l₂-head-indep _ (_ ∷ []) = refl
  divideAccum-length-fst-l₂-head-indep {l₁ = l₁} {l₂ = l₂} x (y₁ ∷ y₂ ∷ ys) =
      divideAccum-length-fst-l₂-head-indep y₂ ys
    ⟨≡⟩ divideAccum-length-fst-l₂-head-indep x ys
    ⟨≡⟩ sym (divideAccum-length-fst-l₂-head-indep y₂ ys)

  divideAccum-length-fst-suc :
    {A : Set ℓ} → {l₁ l₂ : List A} → (x₁ x₂ : A) → (xs : List A)
    → length (fst (divideAccum (x₁ ∷ x₂ ∷ xs) (l₁ , l₂)))
      ≡  suc (length (fst (divideAccum xs (l₁ , l₂))))
  divideAccum-length-fst-suc x₁ x₂ xs =
    divideAccum-length-fst-l₁-suc x₁ xs
    ⟨≡⟩ cong suc (divideAccum-length-fst-l₂-head-indep x₂ xs)

  divideAccum-length-snd-l₂-suc :
    {A : Set ℓ} → {l₁ l₂ : List A} → (x : A) → (xs : List A)
    → length (snd (divideAccum xs (l₁ , x ∷ l₂)))
      ≡ suc (length (snd (divideAccum xs (l₁ , l₂))))
  divideAccum-length-snd-l₂-suc _ [] = refl
  divideAccum-length-snd-l₂-suc _ (_ ∷ []) = refl
  divideAccum-length-snd-l₂-suc {l₁ = l₁} {l₂ = l₂} x (y₁ ∷ y₂ ∷ ys) =
        divideAccum-length-snd-l₂-suc y₂ ys
    ⟨≡⟩ cong suc (divideAccum-length-snd-l₂-suc x ys)
    ⟨≡⟩ cong suc (sym (divideAccum-length-snd-l₂-suc y₂ ys))

  divideAccum-length-snd-l₁-head-indep :
      {A : Set ℓ} → {l₁ l₂ : List A} → (x : A) → (xs : List A)
      → length (snd (divideAccum xs (x ∷ l₁ , l₂)))
        ≡ length (snd (divideAccum xs (l₁ , l₂)))
  divideAccum-length-snd-l₁-head-indep _ [] = refl
  divideAccum-length-snd-l₁-head-indep _ (_ ∷ []) = refl
  divideAccum-length-snd-l₁-head-indep {l₁ = l₁} {l₂ = l₂} x (y₁ ∷ y₂ ∷ ys) =
      divideAccum-length-snd-l₁-head-indep y₁ ys
    ⟨≡⟩ divideAccum-length-snd-l₁-head-indep x ys
    ⟨≡⟩ sym (divideAccum-length-snd-l₁-head-indep y₁ ys)

  divideAccum-length-snd-suc :
    {A : Set ℓ} → {l₁ l₂ : List A} → (x₁ x₂ : A) → (xs : List A)
    → length (snd (divideAccum (x₁ ∷ x₂ ∷ xs) (l₁ , l₂)))
      ≡  suc (length (snd (divideAccum xs (l₁ , l₂))))
  divideAccum-length-snd-suc x₁ x₂ xs =
    divideAccum-length-snd-l₂-suc x₂ xs
    ⟨≡⟩ cong suc (divideAccum-length-snd-l₁-head-indep x₁ xs)

  divide-fst-lt-tot :
    (xs : List A) → length xs > 1 → length (fst (divide xs)) < length xs
  divide-fst-lt-tot [] (diff _ ())
  divide-fst-lt-tot (_ ∷ []) (diff k eq) = diff k eq
  divide-fst-lt-tot {ℓ} {A} l@(x₁ ∷ x₂ ∷ xs) (diff k eq)
    rewrite sym (divide-length-sum {ℓ} {A} xs)
    rewrite sym (add-commute (length (snd (divide xs)))
                             (length (fst (divide xs)))) =

    diff (length (snd (divide l)) - 1)
         (sym ( cong₂ (λ z₁ z₂ → suc (z₁ - 1 + z₂))
                      (divideAccum-length-snd-suc x₁ x₂ xs)
                      (divideAccum-length-fst-suc x₁ x₂ xs)
                ⟨≡⟩ cong suc (add-suc-r _ _ )
              ))

  divide-snd-lt-tot :
    (xs : List A) → length xs > 1 → length (snd (divide xs)) < length xs
  divide-snd-lt-tot [] (diff _ ())
  divide-snd-lt-tot (_ ∷ []) (diff k eq) = diff 0 refl
  divide-snd-lt-tot {ℓ} {A} l@(x₁ ∷ x₂ ∷ xs) (diff k eq)
    rewrite sym (divide-length-sum {ℓ} {A} xs) =
    diff (length (fst (divide l)) - 1)
         (sym (trans (cong₂ (λ z₁ z₂ → suc (z₁ - 1 + z₂))
                      (divideAccum-length-fst-suc x₁ x₂ xs)
                      (divideAccum-length-snd-suc x₁ x₂ xs))
                      (cong suc (add-suc-r _ _ ))
              ))

  divideAccum-perm :
    (xs ys zs : List A)
    → Permutation (xs ++ ys ++ zs)
                  (fst (divideAccum xs (ys , zs)) ++ snd (divideAccum xs (ys , zs)))
  divideAccum-perm [] ys zs = Perm.refl _
  divideAccum-perm [ x ] ys zs = zero! ∷ (Perm.refl _)
  divideAccum-perm (x ∷ x₁ ∷ xs) ys zs =
    Perm.trans (Perm.cons-++ x (x₁ ∷ xs) (ys ++ zs))
   (Perm.trans (Perm.from-≡ (sym (monoid-assoc (x₁ ∷ xs) (x ∷ ys) zs)))
   (Perm.trans (Perm.cons-++ x₁ (xs ++ x ∷ ys) zs)
   (Perm.trans (Perm.from-≡ (monoid-assoc xs (x ∷ ys) (x₁ ∷ zs)))
               (divideAccum-perm xs (x ∷ ys) (x₁ ∷ zs)))))

  divide-perm :
    Permutation xs (fst (divide xs) ++ (snd (divide xs)))
  divide-perm {xs = xs} =
    Perm.trans (Perm.from-≡ (sym (right-identity xs)))
               (divideAccum-perm xs [] [])
