
module Container.Traversable where

open import Prelude

record Traversable {a} (T : Set a → Set a) : Set (lsuc a) where
  field
    traverse : ∀ {F A B} {{AppF : Applicative F}} → (A → F B) → T A → F (T B)

open Traversable {{...}} public

record Traversable′ {a b} (T : ∀ {a} → Set a → Set a) : Set (lsuc (a ⊔ b)) where
  field
    traverse′ : ∀ {F : Set b → Set b} {A : Set a} {B : Set b}
                  {{AppF : Applicative F}} → (A → F B) → T A → F (T B)

open Traversable′ {{...}} public

{-# DISPLAY Traversable.traverse   _ = traverse #-}
{-# DISPLAY Traversable′.traverse′ _ = traverse′ #-}

--- Instances ---

instance
  TraversableMaybe : ∀ {a} → Traversable {a} Maybe
  traverse {{TraversableMaybe}} f m = maybe (pure nothing) (λ x -> pure just <*> f x) m

  TraversableList : ∀ {a} → Traversable {a} List
  traverse {{TraversableList}} f xs = foldr (λ x fxs → pure _∷_ <*> f x <*> fxs) (pure []) xs

  TraversableVec : ∀ {a n} → Traversable {a} (λ A → Vec A n)
  traverse {{TraversableVec}} f []       = pure []
  traverse {{TraversableVec}} f (x ∷ xs) = ⦇ f x ∷ traverse f xs ⦈

  Traversable′Maybe : ∀ {a b} → Traversable′ {a} {b} Maybe
  traverse′ {{Traversable′Maybe}} f m = maybe (pure nothing) (λ x -> pure just <*> f x) m

  Traversable′List : ∀ {a b} → Traversable′ {a} {b} List
  traverse′ {{Traversable′List}} f xs = foldr (λ x fxs → pure _∷_ <*> f x <*> fxs) (pure []) xs

  Traversable′Vec : ∀ {a b n} → Traversable′ {a} {b} (λ A → Vec A n)
  traverse′ {{Traversable′Vec}} f []       = pure []
  traverse′ {{Traversable′Vec}} f (x ∷ xs) = ⦇ f x ∷ traverse′ f xs ⦈

mapM : ∀ {a b} {F : Set b → Set b} {A : Set a} {B : Set b} {{AppF : Applicative F}} →
         (A → F B) → List A → F (List B)
mapM = traverse′

mapM! : ∀ {a} {F : Set → Set} {A : Set a} {{FunF : Functor F}} {{AppF : Applicative F}} →
          (A → F ⊤) → List A → F ⊤
mapM! f xs = _ <$ mapM f xs
