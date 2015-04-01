
module Prelude.Empty where

data ⊥ : Set where

⊥-elim : ∀ {a} {A : Set a} → ⊥ → A
⊥-elim ()

private postulate unsafeBottom : ⊥

erase-⊥ : ⊥ → ⊥
erase-⊥ _ = unsafeBottom

infix 4 ¬_
¬_ : ∀ {a} (A : Set a) → Set a
¬ A = A → ⊥

eraseNegation : ∀ {a} {A : Set a} → ¬ A → ¬ A
eraseNegation !a a = erase-⊥ (!a a)

data ⊥′ {a} : Set a where

⊥′-elim : ∀ {a b} {A : Set a} → ⊥′ {b} → A
⊥′-elim ()
