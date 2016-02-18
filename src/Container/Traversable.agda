
module Container.Traversable where

open import Prelude

record Traversable {a} (T : Set a → Set a) : Set (lsuc a) where
  field
    traverse : ∀ {F A B} {{AppF : Applicative F}} → (A → F B) → T A → F (T B)

open Traversable {{...}} public

--- Instances ---

instance
  TraversableMaybe : ∀ {a} → Traversable {a} Maybe
  TraversableMaybe = record { traverse = λ f m → maybe (pure nothing)
                                                       (λ x -> pure just <*> f x) m }

  TraversableList : ∀ {a} → Traversable {a} List
  TraversableList = record { traverse = λ f xs → foldr (λ x fxs → pure _∷_ <*> f x <*> fxs)
                                                       (pure []) xs }

  TraversableVec : ∀ {a n} → Traversable {a} (λ A → Vec A n)
  TraversableVec {a} {n} = record { traverse = trav }
    where
      trav : ∀ {n} {F : Set a → Set a} {A B : Set a} {{AppF : Applicative F}} →
             (A → F B) → Vec A n → F (Vec B n)
      trav f [] = pure []
      trav f (x ∷ xs) = pure _∷_ <*> f x <*> trav f xs

mapM : ∀ {a} {F : Set a → Set a} {A B} {{AppF : Applicative F}} →
         (A → F B) → List A → F (List B)
mapM = traverse

mapM! : ∀ {F : Set → Set} {A} {{FunF : Functor F}} {{AppF : Applicative F}} →
          (A → F ⊤) → List A → F ⊤
mapM! f xs = _ <$ mapM f xs
