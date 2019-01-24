
module Prelude.Monad.Indexed {i} {I : Set i} where

open import Agda.Primitive
open import Prelude.Function
open import Prelude.Functor
open import Prelude.Applicative.Indexed {I = I}

record IMonad {a b} (M : I → I → Set a → Set b) : Set (i ⊔ lsuc a ⊔ b) where
  infixr 1 _=<<_
  infixl 1 _>>=_ _>>_
  field
    _>>=_ : ∀ {A B i j k} → M i j A → (A → M j k B) → M i k B
    overlap {{super}} : IApplicative M

  _>>_ : ∀ {A B i j k} → M i j A → M j k B → M i k B
  m₁ >> m₂ = m₁ >>= λ _ → m₂

  _=<<_ : ∀ {A B i j k} → (A → M j k B) → M i j A → M i k B
  _=<<_ = flip _>>=_

return : ∀ {a b} {A : Set a} {M : I → I → Set a → Set b} {{_ : IMonad M}}
         {i : I} → A → M i i A
return = pure

open IMonad {{...}} public

{-# DISPLAY IMonad._>>=_  _ = _>>=_  #-}
{-# DISPLAY IMonad._=<<_  _ = _=<<_  #-}
{-# DISPLAY IMonad._>>_   _ = _>>_   #-}

join : ∀ {a} {M : I → I → Set a → Set a} {{_ : IMonad M}} {A : Set a}
       {i j k} → M i j (M j k A) → M i k A
join = _=<<_ id

-- Level polymorphic monads
record IMonad′ {a b} (M : ∀ {a} → I → I → Set a → Set a) : Set (i ⊔ lsuc (a ⊔ b)) where
  field
    _>>=′_ : {A : Set a} {B : Set b} {i j k : I} → M i j A → (A → M j k B) → M i k B
    overlap {{super}} : IApplicative′ {a} {b} M

  _>>′_ : {A : Set a} {B : Set b} {i j k : I} → M i j A → M j k B → M i k B
  m >>′ m′ = m >>=′ λ _ → m′

open IMonad′ {{...}} public
