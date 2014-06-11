
module Data.Traversable where

open import Prelude

record Traversable {a} (T : Set a → Set a) : Set (lsuc a) where
  field
    traverse : ∀ {F A B} {{AppF : Applicative F}} → (A → F B) → T A → F (T B)

open Traversable {{...}} public

--- Instances ---

TraversableMaybe : ∀ {a} → Traversable {a} Maybe
TraversableMaybe = record { traverse = λ f m → maybe (pure nothing)
                                                      (λ x -> pure just <*> f x) m }

TraversableList : ∀ {a} → Traversable {a} List
TraversableList = record { traverse = λ f xs → foldr (λ x fxs → pure _∷_ <*> f x <*> fxs)
                                                     (pure []) xs }

mapM : ∀ {a} {F : Set a → Set a} {A B} {{AppF : Applicative F}} →
         (A → F B) → List A → F (List B)
mapM = traverse
