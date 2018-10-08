
module Control.Monad.Writer where

open import Prelude
open import Control.Monad.Zero
open import Control.Monad.Identity

record WriterT {a} (W : Set a) (M : Set a → Set a) (A : Set a) : Set a where
  no-eta-equality
  constructor writerT
  field runWriterT : M (A × W)

open WriterT public

module _ {a} {W : Set a} {M : Set a → Set a} where

  instance
    FunctorWriterT : {{_ : Functor M}} → Functor {a = a} (WriterT W M)
    runWriterT (fmap {{ FunctorWriterT }} f m) = first f <$> runWriterT m

    FunctorZeroWriterT : {{_ : FunctorZero M}} → FunctorZero {a = a} (WriterT W M)
    runWriterT (empty {{FunctorZeroWriterT}}) = empty

    AlternativeWriterT : {{_ : Alternative M}} → Alternative {a = a} (WriterT W M)
    runWriterT (_<|>_ {{AlternativeWriterT}} x y) = runWriterT x <|> runWriterT y

  module _ {{_ : Monoid W}} {{_ : Monad M}} where

    private
      bindWriterT : ∀ {A B} → WriterT W M A → (A → WriterT W M B) → WriterT W M B
      runWriterT (bindWriterT m f) = do
        (x , w₁) ← runWriterT m
        (y , w₂) ← (runWriterT (f x))
        return (y , w₁ <> w₂)

    instance
      ApplicativeWriterT : Applicative {a = a} (WriterT W M)
      runWriterT (pure {{ApplicativeWriterT}} x) = return (x , mempty)
      _<*>_ {{ApplicativeWriterT}} = monadAp bindWriterT

      MonadWriterT : Monad {a = a} (WriterT W M)
      _>>=_  {{MonadWriterT}} = bindWriterT

    lift : {A : Set a} → M A → WriterT W M A
    runWriterT (lift m) = (_, mempty) <$> m

    writer : {A : Set a} → A × W → WriterT W M A
    runWriterT (writer (x , w)) = return (x , w)

    tell : W → WriterT W M ⊤′
    runWriterT (tell w) = return (tt , w)

    listens : {A B : Set a} → (W → B) → WriterT W M A → WriterT W M (A × B)
    runWriterT (listens f m) = do
      (x , w) ← runWriterT m
      return ((x , f w) , w)

    listen : {A : Set a} → WriterT W M A → WriterT W M (A × W)
    listen = listens id

    pass : {A : Set a} → WriterT W M (A × (W → W)) → WriterT W M A
    runWriterT (pass m) = do
      ((x , f) , w) ← runWriterT m
      return (x , f w)

    censor : {A : Set a} → (W → W) → WriterT W M A → WriterT W M A
    censor f m = pass ((_, f) <$> m)


Writer : ∀ {a} (W : Set a) (A : Set a) → Set a
Writer W = WriterT W Identity

runWriter : ∀ {a} {W : Set a} {A : Set a} → Writer W A → A × W
runWriter m = runIdentity (runWriterT m)

execWriter : ∀ {a} {W : Set a} {A : Set a} → Writer W A → W
execWriter = snd ∘ runWriter
