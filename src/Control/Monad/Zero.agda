
module Control.Monad.Zero where

open import Prelude

record MonadZero {a b} (M : Set a → Set b) : Set (lsuc a ⊔ b) where
  field mzero : ∀ {A} → M A
        overlap {{super}} : Monad M

open MonadZero public using (super)
open MonadZero {{...}} public

{-# DISPLAY MonadZero.mzero _ = mzero #-}

instance
  MonadZeroMaybe : ∀ {a} → MonadZero {a} Maybe
  mzero {{MonadZeroMaybe}} = nothing
  super MonadZeroMaybe = it

  MonadZeroList : ∀ {a} → MonadZero {a} List
  mzero {{MonadZeroList}} = []
  super MonadZeroList = it

module _ {a b} {M : Set a → Set b} {{_ : MonadZero M}} where

  guard! : ∀ {A} → Bool → M A → M A
  guard! true  m = m
  guard! false _ = mzero

  guard : ∀ {p A} {P : Set p} → Dec P → ({{_ : P}} → M A) → M A
  guard (yes p) m = m {{p}}
  guard (no  _) _ = mzero
