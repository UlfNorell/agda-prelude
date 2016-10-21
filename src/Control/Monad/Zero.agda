
module Control.Monad.Zero where

open import Prelude

record MonadZero {a b} (M : Set a → Set b) : Set (lsuc a ⊔ b) where
  instance constructor mkMonadZero
  field overlap {{super-zero}}  : FunctorZero M
        overlap {{super-monad}} : Monad M

open MonadZero public
