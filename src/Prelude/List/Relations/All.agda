module Prelude.List.Relations.All where

open import Prelude.Equality
open import Prelude.Nat
open import Prelude.Empty
open import Prelude.Unit
open import Prelude.Product
open import Prelude.Number
open import Prelude.List.Base

open import Prelude.Applicative

open import Agda.Primitive

infixr 5 _∷_
data All {a b} {A : Set a} (P : A → Set b) : List A → Set (a ⊔ b) where
  []  : All P []
  _∷_ : ∀ {x xs} (p : P x) (ps : All P xs) → All P (x ∷ xs)
