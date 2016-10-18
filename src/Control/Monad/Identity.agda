
module Control.Monad.Identity where

open import Prelude
open import Container.Foldable
open import Container.Traversable

record Identity {a} (A : Set a) : Set a where
  constructor mkIdentity
  field
    runIdentity : A

open Identity public

instance
  FunctorId : ∀ {a} → Functor (Identity {a})
  runIdentity (fmap {{FunctorId}} f m) = f (runIdentity m)

  ApplicativeId : ∀ {a} → Applicative (Identity {a})
  runIdentity (pure {{ApplicativeId}} x) = x
  runIdentity (_<*>_ {{ApplicativeId}} mf mx) = runIdentity mf (runIdentity mx)
  super ApplicativeId = it

  MonadId : ∀ {a} → Monad (Identity {a})
  _>>=_ {{MonadId}} m f = f (runIdentity m)
  super MonadId = it

  FunctorId′ : ∀ {a b} → Functor′ {a} {b} Identity
  runIdentity (fmap′ {{FunctorId′}} f m) = f (runIdentity m)

  ApplicativeId′ : ∀ {a b} → Applicative′ {a} {b} Identity
  runIdentity (_<*>′_ {{ApplicativeId′}} mf mx) = runIdentity mf (runIdentity mx)
  super ApplicativeId′ = it

  MonadId′ : ∀ {a b} → Monad′ {a} {b} Identity
  _>>=′_ {{MonadId′}} m f = f (runIdentity m)
  super MonadId′ = it

  FoldableId : ∀ {a w} → Foldable {w = w} (Identity {a})
  foldMap {{FoldableId}} f m = f (runIdentity m)
  super FoldableId = it

  TraversableId : ∀ {a} → Traversable (Identity {a})
  traverse {{TraversableId}} f m = pure mkIdentity <*> f (runIdentity m)
  super TraversableId = it
