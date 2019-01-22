
module Prelude.Applicative.Indexed {i} {I : Set i} where

open import Agda.Primitive
open import Prelude.Unit
open import Prelude.Functor
open import Prelude.Function
open import Prelude.Equality
open import Prelude.Number
open import Prelude.Semiring
open import Prelude.Fractional

record IApplicative {a b} (F : I → I → Set a → Set b) : Set (i ⊔ lsuc a ⊔ b) where
  infixl 4 _<*>_ _<*_ _*>_
  field
    pure  : ∀ {A i} → A → F i i A
    _<*>_ : ∀ {A B i j k} → F i j (A → B) → F j k A → F i k B
    overlap {{super}} : ∀ {i j} → Functor (F i j)

  _<*_ : ∀ {A B i j k} → F i j A → F j k B → F i k A
  a <* b = ⦇ const a b ⦈

  _*>_ : ∀ {A B i j k} → F i j A → F j k B → F i k B
  a *> b = ⦇ (const id) a b ⦈

open IApplicative {{...}} public

{-# DISPLAY IApplicative.pure  _ = pure  #-}
{-# DISPLAY IApplicative._<*>_ _ = _<*>_ #-}
{-# DISPLAY IApplicative._<*_  _ = _<*_  #-}
{-# DISPLAY IApplicative._*>_  _ = _*>_  #-}

-- Level polymorphic functors
record IApplicative′ {a b} (F : ∀ {a} → I → I → Set a → Set a) : Set (i ⊔ lsuc (a ⊔ b)) where
  infixl 4 _<*>′_
  field
    _<*>′_ : {A : Set a} {B : Set b} {i j k : I} → F i j (A → B) → F j k A → F i k B
    overlap {{super}} : ∀ {i j} → Functor′ {a} {b} (F i j)

open IApplicative′ {{...}} public

module _ {F : ∀ {a} → I → I → Set a → Set a}
         {{_ : ∀ {a} → IApplicative {a = a} F}}
         {{_ : ∀ {a b} → IApplicative′ {a = a} {b = b} F}}
         {a b} {A : Set a} {B : Set b} {i j k} where

  infixl 4 _<*′_ _*>′_
  _<*′_ : F i j A → F j k B → F i k A
  a <*′ b = pure const <*>′ a <*>′ b

  _*>′_ : F i j A → F j k B → F i k B
  a *>′ b = pure (const id) <*>′ a <*>′ b
