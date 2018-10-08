
module Control.Monad.Transformer where

open import Prelude

record Transformer {a b} (T : (Set a → Set b) → (Set a → Set b)) : Set (lsuc a ⊔ lsuc b) where
  field
    lift : {M : Set a → Set b} {{_ : Monad M}} {A : Set a} → M A → T M A

open Transformer {{...}} public
