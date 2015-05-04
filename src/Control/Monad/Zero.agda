
module Control.Monad.Zero where

open import Prelude

record MonadZero {a b} (M : Set a → Set b) : Set (lsuc a ⊔ b) where
  field mzero : ∀ {A} → M A

open MonadZero {{...}} public

{-# DISPLAY MonadZero.mzero _ = mzero #-}

instance
  MonadZeroMaybe : ∀ {a} → MonadZero {a} Maybe
  MonadZeroMaybe = record { mzero = nothing }

module _ {a b} {M : Set a → Set b} {{_ : MonadZero M}} where

  guard! : ∀ {A} → Bool → M A → M A
  guard! true  m = m
  guard! false _ = mzero

  guard : ∀ {p A} {P : Set p} → Dec P → ({{_ : P}} → M A) → M A
  guard (yes p) m = m {{p}}
  guard (no  _) _ = mzero
