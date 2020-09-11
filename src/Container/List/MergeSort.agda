-- Contains the definition and main properties of MergeSort
-- the actual sorting function is |mergeSortBy|
module Container.List.MergeSort where

open import Prelude.Function
open import Prelude.Equality.Inspect
open import Prelude.Equality
open import Prelude.Semiring
open import Prelude.Product
open import Prelude.Bool
open import Prelude.Nat
open import Prelude.Ord
open import Prelude.Ord.Properties
open import Prelude.List.Base
open import Prelude.List.Properties

open import Prelude.Monoid

open import Control.WellFounded
open import Container.List.Linked
open import Container.List.Sorted
open import Container.List.Any

open import Prelude.Nat.Properties

open import Prelude.Variables

open import Container.List.MergeSort.Divide renaming (module Properties to DivideProperies)
open import Container.List.Permutation using (Permutation ; [] ; _∷_ )
import Container.List.Permutation as Perm

mergeBy : (A → A → Bool) → List A → List A → List A
mergeBy rel [] l₂ = l₂
mergeBy rel l₁@(_ ∷ _) [] = l₁
mergeBy rel (x ∷ xs) (y ∷ ys) =
  if rel x y
  then x ∷ mergeBy rel xs (y ∷ ys)
  else y ∷ mergeBy rel (x ∷ xs) ys

private
  mergeSortBy' : (A → A → Bool) → (l : List A)
               → (@0 acc : Acc _<_ (length l))
               → List A
  mergeSortBy' _≤?_ [] _ = []
  mergeSortBy' _≤?_ (x ∷ []) _ = x ∷ []
  mergeSortBy' _≤?_ l@(_ ∷ _ ∷ xs) (acc getLt) =
    let (l₁ , l₂) = divide l
    in mergeBy _≤?_ (mergeSortBy'
                      _≤?_ l₁
                      (getLt (length l₁) (DivideProperies.divide-fst-lt-tot
                                    l (diff (length xs)
                                            (cong suc (add-commute 1 _))))))
                    (mergeSortBy'
                      _≤?_ l₂
                      (getLt (length l₂) (DivideProperies.divide-snd-lt-tot
                                    l (diff (length xs)
                                            (cong suc (add-commute 1 _))))))

  wfList : (l : List A) → Acc _<_ (length l)
  wfList [] = acc (λ { arr (diff _ ())})
  wfList l₂@(x ∷ xs) = wfNat (length l₂)

mergeSortBy : (A → A → Bool) → (l : List A) → List A
mergeSortBy _≤?_ l = mergeSortBy' _≤?_ l (wfList l)

mergeSort : {{_ : Ord A}} → (xs : List A) → List A
mergeSort = mergeSortBy _≤?_

module Properties where

  -- Covers the tricky part of the mergeBy proof
  mergeBy-heads-sortedBy :
      (proj : A → B)
    → {{OrdB : Ord/Laws B}}
    → (h x y : A)
    → (proj h ≤ proj x) → (proj h ≤ proj y)
    → {xs : List A} → (OrderedBy (λ a b → (proj a) ≤ (proj b)) (x ∷ xs))
    → {ys : List A} → (OrderedBy (λ a b → (proj a) ≤ (proj b)) (y ∷ ys))
    → Acc _<_ (length (x ∷ xs) + length (y ∷ ys))
    → SortedBy (λ a b → (proj a) ≤ (proj b))
               (h ∷ (mergeBy (λ a b → (proj a) ≤? (proj b)) (x ∷ xs) (y ∷ ys)))
               (h ∷ (x ∷ xs) ++ (y ∷ ys))
  mergeBy-heads-sortedBy proj h x y h≤x h≤y [-] [-] _
    with inspect (proj x ≤? proj y)
  ...| true with≡ x≤?y rewrite x≤?y =
    (h≤x ∷ (≤?⇒≤ x≤?y)  ∷ [-])
    , zero! ∷ (zero! ∷ (zero! ∷ []))
  ...| false with≡ x≰?y rewrite x≰?y =
    (h≤y ∷ (≰?⇒≥ x≰?y) ∷ [-])
    , zero! ∷ ((suc zero!) ∷ (zero! ∷ []))
  mergeBy-heads-sortedBy
    proj h x y h≤x h≤y
    {xs = xs} [-]
    {ys = y₁ ∷ ys} (y≤y₁ ∷ ordered[ys])
    (acc next-acc)
    with inspect (proj x ≤? proj y)
  ...| true with≡ x≤?y rewrite x≤?y =
    (h≤x ∷ (≤?⇒≤ x≤?y) ∷ (y≤y₁ ∷ ordered[ys]))
    , zero! ∷ (Perm.refl _)
  ...| false with≡ x≰?y rewrite x≰?y
    with inspect (proj x ≤? proj y₁)
  ... | true with≡ x≤?y₁ rewrite x≤?y₁ =
    (h≤y ∷ (≰?⇒≥ x≰?y) ∷ (≤?⇒≤ x≤?y₁) ∷ ordered[ys])
    , zero! ∷ ((suc zero!) ∷ (Perm.refl _))
  ... | false with≡ x≰?y₁ rewrite x≰?y =
    let (sorted[tail] , permut[tail]) =
          mergeBy-heads-sortedBy
            proj y x _ (≰?⇒≥ x≰?y) y≤y₁ [-] ordered[ys]
            (next-acc (suc (length xs + suc (length ys)))
                      (diff zero refl))
    in (h≤y ∷ sorted[tail])
       , (zero refl ∷ Perm.swap-cons-left permut[tail])
  mergeBy-heads-sortedBy
    proj h x y h≤x h≤y
    {xs = x₁ ∷ xs} (x≤y₁ ∷ ordered[xs])
    {ys = ys} [-]
    (acc next-acc)
      with inspect (proj x ≤? proj y)
  ...| true with≡ x≤?y rewrite x≤?y =
    let (sorted[tail] , permut[tail]) =
          mergeBy-heads-sortedBy
            proj x _ y x≤y₁ (≤?⇒≤ x≤?y) ordered[xs] [-]
            (next-acc (suc (length xs + suc (length ys)))
                      (diff zero refl))
    in (h≤x ∷ sorted[tail])
      , (zero refl ∷ permut[tail])
  ...| false with≡ x≰?y rewrite x≰?y =
    (h≤y ∷ ((≰?⇒≥ x≰?y) ∷ (x≤y₁ ∷ ordered[xs])))
    , zero! ∷ ((suc zero!) ∷ ((suc zero!)
      ∷ Perm.flip-++-right _ [ y ] (Perm.refl (_ ++ [ y ]))))
  mergeBy-heads-sortedBy
    proj h x y h≤x h≤y
    {xs = x₁ ∷ xs} (x≤x₁ ∷ ordered[xs])
    {ys = y₁ ∷ ys} (y≤y₁ ∷ ordered[ys])
    (acc next-acc)
      with inspect (proj x ≤? proj y)
  ...| true with≡ x≤?y rewrite x≤?y =
    let (sorted[tail] , permut[tail]) =
          mergeBy-heads-sortedBy
            proj x x₁ y x≤x₁ (≤?⇒≤ x≤?y) ordered[xs] (y≤y₁ ∷ ordered[ys])
            (next-acc (suc (length xs + suc (suc (length ys))))
                      (diff zero refl))
    in (h≤x ∷ sorted[tail]) , (zero refl ∷ permut[tail])
  ...| false with≡ x≰?y rewrite x≰?y =
    let (sorted[tail] , permut[tail]) =
          mergeBy-heads-sortedBy
            proj y x y₁ (≰?⇒≥ x≰?y)  y≤y₁ (x≤x₁ ∷ ordered[xs]) ordered[ys]
            (next-acc (suc (suc (length xs + suc (length ys))))
                      (diff zero
                            (cong (λ z → suc (suc z))
                                  (add-suc-r (length xs) (suc (length ys))))))
    in h≤y ∷ sorted[tail]
       , zero refl ∷ (Perm.trans (Perm.sym (Perm.cons-++ y (x ∷ x₁ ∷ xs) (y₁ ∷ ys)))
                                 permut[tail])


  mergeBy-SortedBy :
    (proj : A → B)
    → {{OrdB : Ord/Laws B}}
    → {xs : List A} → (OrderedBy (λ a b → (proj a) ≤ (proj b)) xs )
    → {ys : List A} → (OrderedBy (λ a b → (proj a) ≤ (proj b)) ys)
    → SortedBy (λ a b → (proj a) ≤ (proj b))
               (mergeBy (λ a b → (proj a) ≤? (proj b)) xs ys)
               (xs ++ ys)
  mergeBy-SortedBy proj [] [] = [] , []
  mergeBy-SortedBy proj [] [-] = [-] , (zero! ∷ [])
  mergeBy-SortedBy proj [] (x ∷ ord[ys]) =
    (x ∷ ord[ys]) , (zero! ∷ (zero! ∷ Perm.refl _))
  mergeBy-SortedBy proj [-] [] = [-] , (zero! ∷ [])
  mergeBy-SortedBy proj ([-] {x = x}) ([-] {x = y})
    with inspect (proj x ≤? proj y)
  ...| true with≡ x≤?y rewrite x≤?y =
    (≤?⇒≤ x≤?y ∷ [-]) , zero! ∷ (zero! ∷ [])
  ...| false with≡ x≰?y rewrite x≰?y =
    (≰?⇒≥ x≰?y ∷ [-]) , ((suc zero!) ∷ (zero! ∷ []))
  mergeBy-SortedBy proj ord[xs]@([-] {x = x}) ord[ys]@(_∷_ {x = y} {xs = ys} y≤y₁ ord[ys'])
    with inspect (proj x ≤? proj y)
  ...| true with≡ x≤?y rewrite x≤?y =
    (≤?⇒≤ x≤?y ∷ y≤y₁ ∷ ord[ys']) , zero! ∷ (zero! ∷ Perm.refl _)
  ...| false with≡ x≰?y rewrite x≰?y =
    let (ord[tail] , perm[tail]) =
          mergeBy-heads-sortedBy proj y _ _ (≰?⇒≥ x≰?y) y≤y₁ ord[xs] ord[ys'] (wfNat _)
    in ord[tail] , (Perm.swap-cons-left perm[tail])
  mergeBy-SortedBy proj {xs = xs} (x ∷ ord[xs]) [] rewrite right-identity xs =
    (x ∷ ord[xs]) , (zero! ∷ (zero! ∷ Perm.refl _))
  mergeBy-SortedBy proj ord[xs]@(_∷_ {x = x} x≤x₁ ord[xs']) ord[ys]@([-] {x = y})
    with inspect (proj x ≤? proj y)
  ...| true with≡ x≤?y rewrite x≤?y =
    mergeBy-heads-sortedBy proj x _ _ x≤x₁ (≤?⇒≤ x≤?y)  ord[xs'] ord[ys] (wfNat _)
  ...| false with≡ x≰?y rewrite x≰?y =
    (≰?⇒≥ x≰?y ∷ x≤x₁ ∷ ord[xs'])
    , (suc zero!) ∷ (suc zero!)
      ∷ (Perm.trans (Perm.sym (Perm.cons-++ y _ []))
                     (Perm.from-≡ (right-identity _)))
  mergeBy-SortedBy proj {xs = x ∷ x₁ ∷ xs} (x≤x₁ ∷ ord[xs])
                      {ys = y ∷ y₁ ∷ ys} (y≤y₁ ∷ ord[ys])
    with inspect (proj x ≤? proj y)
  ...| true with≡ x≤?y rewrite x≤?y =
    mergeBy-heads-sortedBy proj x _ _ x≤x₁ (≤?⇒≤ x≤?y)  ord[xs] (y≤y₁ ∷ ord[ys]) (wfNat _)
  ...| false with≡ x≰?y rewrite x≰?y =
    let (foo , bar) = mergeBy-heads-sortedBy proj y _ _ (≰?⇒≥ x≰?y) y≤y₁  (x≤x₁ ∷ ord[xs]) ord[ys] (wfNat _)
    in foo , (Perm.trans (Perm.sym (Perm.cons-++ y (x ∷ x₁ ∷ xs) _))
                         bar)


  mergeSortBy'-sortedBy :
    (proj : A → B)
    → {{OrdB : Ord/Laws B}}
    → (xs : List A)
    → (acc : Acc _<_ (length xs))
    → SortedBy (λ a b → (proj a) ≤ (proj b))
               (mergeSortBy' (λ a b → (proj a) ≤? (proj b)) xs acc)
               xs
  mergeSortBy'-sortedBy proj [] (acc new-acc) =
    [] , []
  mergeSortBy'-sortedBy proj [ x ] (acc new-acc) =
    [-] , (zero! ∷ [])
  mergeSortBy'-sortedBy proj (x ∷ x₁ ∷ xs) (acc new-acc) =
    let (ord[left] , perm[left]) = mergeSortBy'-sortedBy
                     proj (fst (divide (x ∷ x₁ ∷ xs)))
                     (new-acc _
                              (DivideProperies.divide-fst-lt-tot
                                (x ∷ x₁ ∷ xs) (diff (length xs)
                                                 (cong suc (sym (add-one-r _))))))
        (ord[right] , perm[right]) = mergeSortBy'-sortedBy
                      proj (snd (divide (x ∷ x₁ ∷ xs)))
                      (new-acc _
                              (DivideProperies.divide-snd-lt-tot
                                (x ∷ x₁ ∷ xs) (diff (length xs)
                                                 (cong suc (sym (add-one-r _))))))
        (ord[merge] , perm[merge]) = mergeBy-SortedBy proj ord[left] ord[right]
    in ord[merge] ,  Perm.trans DivideProperies.divide-perm
                     (Perm.trans (Perm.permuation-++ perm[left] perm[right])
                                 perm[merge])


  mergeSortBy-sortedBy :
    (proj : A → B)
    → {{OrdB : Ord/Laws B}}
    → (xs : List A)
    → SortedBy (λ a b → (proj a) ≤ (proj b))
               (mergeSortBy (λ a b → (proj a) ≤? (proj b)) xs)
               xs
  mergeSortBy-sortedBy proj xs =
    mergeSortBy'-sortedBy proj xs (wfList xs)

  mergeSort-sortedBy :
    {{_ : Ord/Laws A}}
    → (xs : List A)
    → SortedBy _≤_ (mergeSort xs) xs
  mergeSort-sortedBy = mergeSortBy-sortedBy id
