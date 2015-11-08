
module Prelude.Empty where

open import Prelude.Erased

data ⊥ : Set where

⊥-elim : ∀ {a} {A : Set a} → ⊥ → A
⊥-elim ()

private postulate erasedBottom : ⊥

{-# DISPLAY erasedBottom = [erased] #-}

erase-⊥ : ⊥ → ⊥
erase-⊥ _ = erasedBottom

infix 4 ¬_
¬_ : ∀ {a} (A : Set a) → Set a
¬ A = A → ⊥

eraseNegation : ∀ {a} {A : Set a} → ¬ A → ¬ A
eraseNegation !a a = erase-⊥ (!a a)

data ⊥′ {a} : Set a where

⊥′-elim : ∀ {a b} {A : Set a} → ⊥′ {b} → A
⊥′-elim ()
