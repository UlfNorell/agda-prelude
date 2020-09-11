module Prelude.List.Relations.Linked where

open import Prelude.List.Base
open import Agda.Primitive      public

-- Addaption of the agda-prelude library
data Linked {a b} {A : Set a} (R : A → A → Set b) : List A → Set (a ⊔ b) where
  [] : Linked R []
  [-] : ∀ {x} → Linked R (x ∷ [])
  _∷_ : ∀ {x y xs} → R x y → Linked R (y ∷ xs) → Linked R (x ∷ y ∷ xs)
