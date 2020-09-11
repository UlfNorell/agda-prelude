module Prelude.List.Relations.Sorted where

open import Prelude.Equality
open import Prelude.Variables

open import Prelude.Product
open import Prelude.Decidable

open import Prelude.List.Base
open import Prelude.List.Relations.Permutation using (Permutation ; [] ; _∷_)
open import Prelude.List.Relations.Linked
open import Prelude.List.Relations.Any



OrderedBy : ∀ {ℓ₁} {A : Set ℓ} → (A → A → Set ℓ₁) → List A → Set (ℓ ⊔ ℓ₁)
OrderedBy = Linked

orderedBy : {R : A → A → Set ℓ₁}
          → (dec-rel : (a b : A) → Dec (R a b))
          → (list : List A) → Dec (OrderedBy R list)
orderedBy dec-rel [] = yes Linked.[]
orderedBy dec-rel (x₁ ∷ []) = yes Linked.[-]
orderedBy dec-rel (x₁ ∷ x₂ ∷ xs)
  with dec-rel x₁ x₂ | orderedBy dec-rel (x₂ ∷ xs)
...| yes rel | yes tail-SortedBy =
  yes (rel ∷ tail-SortedBy)
...| yes x₁≤x₂ | no ¬tail-SortedBy =
  no λ { (_ ∷ tail-SortedBy) → ¬tail-SortedBy tail-SortedBy }
...| no ¬x₁≤x₂ | _ =
  no λ {  (x₁≤x₂ ∷ _) → ¬x₁≤x₂ x₁≤x₂}

SortedBy :  ∀ {ℓ₁} {A : Set ℓ} → (A → A → Set ℓ₁) → List A → List A → Set (ℓ ⊔ ℓ₁)
SortedBy R sorted orig =
  OrderedBy R sorted × Permutation orig sorted

singeleton-sortedBy : (R : (A → A → Set ℓ₁)) → (x : A) → SortedBy R [ x ] [ x ]
singeleton-sortedBy r x = [-] , (zero refl ∷ [])
