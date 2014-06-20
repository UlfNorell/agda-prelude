
module Control.Monad.State where

open import Prelude

data StateT {a} (S : Set a) (M : Set a → Set a) (A : Set a) : Set a where
  stateT : (S → M (A × S)) → StateT S M A

runStateT : ∀ {a} {S : Set a} {M : Set a → Set a} {A : Set a} →
              StateT S M A → S → M (A × S)
runStateT (stateT f) = f

-- Instances --

MonadStateT : ∀ {a} {S : Set a} {M : Set a → Set a} {{MonadM : Monad M}} →
                Monad {a = a} (StateT S M)
MonadStateT = record { return = λ x → stateT λ s → return (x , s)
                     ; _>>=_  = λ m f → stateT λ s →
                                  runStateT m s >>= λ r →
                                  uncurry (runStateT ∘ f) r
                     }

FunctorStateT : ∀ {a} {S : Set a} {M : Set a → Set a} {{MonadM : Monad M}} →
                  Functor {a = a} (StateT S M)
FunctorStateT = defaultMonadFunctor {{MonadStateT}}

ApplicativeStateT : ∀ {a} {S : Set a} {M : Set a → Set a} {{MonadM : Monad M}} →
                    Applicative {a = a} (StateT S M)
ApplicativeStateT = defaultMonadApplicative {{MonadStateT}}

-- State operations --

lift : ∀ {a} {S : Set a} {M : Set a → Set a} {{MonadM : Monad M}} {A : Set a} →
       M A → StateT S M A
lift m = stateT λ s → m >>= λ x → return (x , s)

gets : ∀ {a} {S A : Set a} {M : Set a → Set a} {{MonadM : Monad M}} →
         (S → A) → StateT S M A
gets f = stateT λ s → return (f s , s)

modify : ∀ {a} {S : Set a} {M : Set a → Set a} {{MonadM : Monad M}} →
           (S → S) → StateT S M S
modify f = stateT λ s → return (s , f s)

get : ∀ {a} {S : Set a} {M : Set a → Set a} {{MonadM : Monad M}} →
        StateT S M S
get = gets id

put : ∀ {a} {S : Set a} {M : Set a → Set a} {{MonadM : Monad M}} →
        S → StateT S M S
put s = modify (const s)
