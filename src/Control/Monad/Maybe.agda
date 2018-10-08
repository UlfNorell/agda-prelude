
module Control.Monad.Maybe where

open import Prelude
open import Control.Monad.Zero
open import Control.Monad.Transformer

record MaybeT {a} (M : Set a → Set a) (A : Set a) : Set a where
  no-eta-equality
  constructor maybeT
  field runMaybeT : M (Maybe A)

open MaybeT public

module _ {a} {M : Set a → Set a} where

  instance
    FunctorMaybeT : {{_ : Functor M}} → Functor {a = a} (MaybeT M)
    runMaybeT (fmap {{FunctorMaybeT}} f m) = fmap f <$> runMaybeT m

    FunctorZeroMaybeT : {{_ : Monad M}} → FunctorZero {a = a} (MaybeT M)
    runMaybeT (empty {{FunctorZeroMaybeT}}) = return nothing

    AlternativeMaybeT : {{_ : Monad M}} → Alternative {a = a} (MaybeT M)
    runMaybeT (_<|>_ {{AlternativeMaybeT {{monadM}}}} mx my) = do
      just x ← runMaybeT mx
        where nothing → runMaybeT my
      return (just x)

  module _ {{_ : Monad M}} where

    private
      bindMaybeT : ∀ {A B} → MaybeT M A → (A → MaybeT M B) → MaybeT M B
      runMaybeT (bindMaybeT m f) = do
        just x ← runMaybeT m
          where nothing → return nothing
        runMaybeT (f x)

    instance
      ApplicativeMaybeT : Applicative {a = a} (MaybeT M)
      runMaybeT (pure {{ApplicativeMaybeT}} x) = pure (just x)
      _<*>_ {{ApplicativeMaybeT}} = monadAp bindMaybeT

      MonadMaybeT : Monad {a = a} (MaybeT M)
      _>>=_  {{MonadMaybeT}} = bindMaybeT

    liftMaybeT : {A : Set a} → M A → MaybeT M A
    runMaybeT (liftMaybeT m) = just <$> m

instance
  TransformerMaybeT : ∀ {a} → Transformer {a} MaybeT
  lift {{TransformerMaybeT}} = liftMaybeT
