
module Control.Monad.State where

open import Prelude
open import Control.Monad.Zero

data StateT {a} (S : Set a) (M : Set a → Set a) (A : Set a) : Set a where
  stateT : (S → M (A × S)) → StateT S M A

runStateT : ∀ {a} {S : Set a} {M : Set a → Set a} {A : Set a} →
              StateT S M A → S → M (A × S)
runStateT (stateT f) = f

-- Instances --

private
  returnStateT : ∀ {a} {S : Set a} {M : Set a → Set a} {{MonadM : Monad M}} {A : Set a} →
                   A → StateT S M A
  returnStateT x = stateT λ s → return (x , s)

  bindStateT : ∀ {a} {S : Set a} {M : Set a → Set a} {{MonadM : Monad M}} {A B : Set a} →
                 StateT S M A → (A → StateT S M B) → StateT S M B
  bindStateT m f = stateT λ s → runStateT m s >>= λ r → uncurry (runStateT ∘ f) r

module _ {a} {S : Set a} {M : Set a → Set a} {{MonadM : Monad M}} where
  instance
    MonadStateT : Monad {a = a} (StateT S M)
    MonadStateT = record { return = returnStateT
                         ; _>>=_  = bindStateT
                         }

    FunctorStateT : Functor {a = a} (StateT S M)
    FunctorStateT = defaultMonadFunctor {{MonadStateT}}

    ApplicativeStateT : Applicative {a = a} (StateT S M)
    ApplicativeStateT = defaultMonadApplicative {{MonadStateT}}

    MonadZeroStateT : {{_ : MonadZero M}} → MonadZero {a = a} (StateT S M)
    MonadZeroStateT = record { mzero = stateT λ _ → mzero }

  -- State operations --

  lift : {A : Set a} → M A → StateT S M A
  lift m = stateT λ s → m >>= λ x → return (x , s)

  gets : {A : Set a} → (S → A) → StateT S M A
  gets f = stateT λ s → return (f s , s)

  modify : (S → S) → StateT S M S
  modify f = stateT λ s → return (s , f s)

  get : StateT S M S
  get = gets id

  put : S → StateT S M S
  put s = modify (const s)
