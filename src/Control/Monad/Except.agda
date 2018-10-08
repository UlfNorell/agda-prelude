
module Control.Monad.Except where

open import Prelude
open import Control.Monad.Zero
open import Control.Monad.Identity
open import Control.Monad.Transformer

record ExceptT {a} (E : Set a) (M : Set a → Set a) (A : Set a) : Set a where
  no-eta-equality
  constructor maybeT
  field runExceptT : M (Either E A)

open ExceptT public

module _ {a} {E : Set a} {M : Set a → Set a} where

  instance
    FunctorExceptT : {{_ : Functor M}} → Functor {a = a} (ExceptT E M)
    runExceptT (fmap {{FunctorExceptT}} f m) = fmap f <$> runExceptT m

    FunctorZeroExceptT : {{_ : Monad M}} {{_ : Monoid E}} → FunctorZero {a = a} (ExceptT E M)
    runExceptT (empty {{FunctorZeroExceptT}}) = return (left mempty)

    AlternativeExceptT : {{_ : Monad M}} {{_ : Monoid E}} → Alternative {a = a} (ExceptT E M)
    runExceptT (_<|>_ {{AlternativeExceptT {{monadM}}}} mx my) = do
      right x ← runExceptT mx
        where
          left e₁ → do
            right y ← runExceptT my
              where left e₂ → return (left (e₁ <> e₂))
            return (right y)
      return (right x)

  module _ {{_ : Monad M}} where

    private
      bindExceptT : ∀ {A B} → ExceptT E M A → (A → ExceptT E M B) → ExceptT E M B
      runExceptT (bindExceptT m f) = do
        right x ← runExceptT m
          where left e → return (left e)
        runExceptT (f x)

    instance
      ApplicativeExceptT : Applicative {a = a} (ExceptT E M)
      runExceptT (pure {{ApplicativeExceptT}} x) = pure (right x)
      _<*>_ {{ApplicativeExceptT}} = monadAp bindExceptT

      MonadExceptT : Monad {a = a} (ExceptT E M)
      _>>=_  {{MonadExceptT}} = bindExceptT

    liftExceptT : {A : Set a} → M A → ExceptT E M A
    runExceptT (liftExceptT m) = right <$> m

instance
  TransformerExceptT : ∀ {a} {E : Set a} → Transformer {a} (ExceptT E)
  lift {{TransformerExceptT}} = liftExceptT

Except : ∀ {a} (E : Set a) (A : Set a) → Set a
Except R = ExceptT R Identity

runExcept : ∀ {a} {E : Set a} {A : Set a} → Except E A → Either E A
runExcept m = runIdentity (runExceptT m)
