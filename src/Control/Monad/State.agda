
module Control.Monad.State where

open import Prelude
open import Control.Monad.Zero

record StateT {a} (S : Set a) (M : Set a → Set a) (A : Set a) : Set a where
  no-eta-equality
  constructor stateT
  field runStateT : S → M (A × S)

open StateT public

-- Instances --

module _ {a} {S : Set a} {M : Set a → Set a} where

  instance
    FunctorStateT : {{_ : Functor M}} → Functor {a = a} (StateT S M)
    runStateT (fmap {{FunctorStateT}} f m) s = first f <$> runStateT m s

    AlternativeStateT : {{_ : Alternative M}} → Alternative {a = a} (StateT S M)
    runStateT (empty {{AlternativeStateT}})     s = empty
    runStateT (_<|>_ {{AlternativeStateT}} x y) s = runStateT x s <|> runStateT y s
    super AlternativeStateT = it

  module _ {{_ : Monad M}} where

    private
      bindStateT : ∀ {A B} → StateT S M A → (A → StateT S M B) → StateT S M B
      runStateT (bindStateT m f) s = runStateT m s >>= λ r → uncurry (runStateT ∘ f) r

    instance
      ApplicativeStateT : Applicative {a = a} (StateT S M)
      runStateT (pure  {{ApplicativeStateT}} x)     s = pure (x , s)
      _<*>_ {{ApplicativeStateT}} = monadAp bindStateT
      super ApplicativeStateT = it

      MonadStateT : Monad {a = a} (StateT S M)
      _>>=_  {{MonadStateT}} = bindStateT
      super MonadStateT = it

      MonadZeroStateT : {{_ : MonadZero M}} → MonadZero {a = a} (StateT S M)
      runStateT (mzero {{MonadZeroStateT}}) _ = mzero
      super MonadZeroStateT = it

    lift : {A : Set a} → M A → StateT S M A
    runStateT (lift m) s = m >>= λ x → return (x , s)

    gets : {A : Set a} → (S → A) → StateT S M A
    runStateT (gets f) s = return (f s , s)

    modify : (S → S) → StateT S M S
    runStateT (modify f) s = return (s , f s)

    get : StateT S M S
    get = gets id

    put : S → StateT S M S
    put s = modify (const s)
