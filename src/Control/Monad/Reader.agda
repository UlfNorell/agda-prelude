
module Control.Monad.Reader where

open import Prelude
open import Control.Monad.Zero
open import Control.Monad.Identity

record ReaderT {a} (R : Set a) (M : Set a → Set a) (A : Set a) : Set a where
  no-eta-equality
  constructor readerT
  field runReaderT : R → M A

open ReaderT public

module _ {a} {R : Set a} {M : Set a → Set a} where

  instance
    FunctorReaderT : {{_ : Functor M}} → Functor {a = a} (ReaderT R M)
    runReaderT (fmap {{ FunctorReaderT }} f m) r = f <$> runReaderT m r

    FunctorZeroReaderT : {{_ : FunctorZero M}} → FunctorZero {a = a} (ReaderT R M)
    runReaderT (empty {{FunctorZeroReaderT}}) r = empty

    AlternativeReaderT : {{_ : Alternative M}} → Alternative {a = a} (ReaderT R M)
    runReaderT (_<|>_ {{AlternativeReaderT}} x y) r = runReaderT x r <|> runReaderT y r

  module _ {{_ : Monad M}} where

    private
      bindReaderT : ∀ {A B} → ReaderT R M A → (A → ReaderT R M B) → ReaderT R M B
      runReaderT (bindReaderT m f) r = runReaderT m r >>= λ x → runReaderT (f x) r

    instance
      ApplicativeReaderT : Applicative {a = a} (ReaderT R M)
      runReaderT (pure {{ApplicativeReaderT}} x) r = pure x
      _<*>_ {{ApplicativeReaderT}} = monadAp bindReaderT

      MonadReaderT : Monad {a = a} (ReaderT R M)
      _>>=_  {{MonadReaderT}} = bindReaderT

    lift : {A : Set a} → M A → ReaderT R M A
    runReaderT (lift m) r = m

    asks : {A : Set a} → (R → A) → ReaderT R M A
    runReaderT (asks f) r = return (f r)

    ask : ReaderT R M R
    ask = asks id

    local : {A : Set a} → (R → R) → ReaderT R M A → ReaderT R M A
    runReaderT (local f m) r = runReaderT m (f r)

Reader : ∀ {a} (R : Set a) (A : Set a) → Set a
Reader R = ReaderT R Identity

runReader : ∀ {a} {R : Set a} {A : Set a} → Reader R A → R → A
runReader m r = runIdentity (runReaderT m r)
