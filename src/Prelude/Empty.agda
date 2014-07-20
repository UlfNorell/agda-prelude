
module Prelude.Empty where

data ⊥ : Set where

⊥-elim : ∀ {a} {A : Set a} → ⊥ → A
⊥-elim ()

infix 4 ¬_
¬_ : ∀ {a} (A : Set a) → Set a
¬ A = A → ⊥

data ⊥′ {a} : Set a where

⊥′-elim : ∀ {a b} {A : Set a} → ⊥′ {b} → A
⊥′-elim ()
