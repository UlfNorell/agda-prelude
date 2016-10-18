
module Prelude.Monad where

open import Agda.Primitive
open import Prelude.Function
open import Prelude.Functor
open import Prelude.Applicative

record Monad {a b} (M : Set a → Set b) : Set (lsuc a ⊔ b) where
  infixr 1 _=<<_
  infixl 1 _>>=_ _>>_
  field
    _>>=_ : ∀ {A B} → M A → (A → M B) → M B
    overlap {{super}} : Applicative M

  _>>_ : ∀ {A B} → M A → M B → M B
  m₁ >> m₂ = m₁ >>= λ _ → m₂

  _=<<_ : ∀ {A B} → (A → M B) → M A → M B
  _=<<_ = flip _>>=_

return : ∀ {a b} {A : Set a} {M : Set a → Set b} {{_ : Monad M}} → A → M A
return = pure

monadAp : ∀ {a b} {A B : Set a} {M : Set a → Set b}
            {{_ : Functor M}} →
            (M (A → B) → ((A → B) → M B) → M B) →
            M (A → B) → M A → M B
monadAp _>>=_ mf mx = mf >>= λ f → fmap f mx

open Monad using (super) public
open Monad {{...}} public hiding (super)

{-# DISPLAY Monad._>>=_  _ = _>>=_  #-}
{-# DISPLAY Monad._=<<_  _ = _=<<_  #-}
{-# DISPLAY Monad._>>_   _ = _>>_   #-}

join : ∀ {a} {M : Set a → Set a} {{_ : Monad M}} {A : Set a} → M (M A) → M A
join = _=<<_ id

-- Level polymorphic monads
record Monad′ {a b} (M : ∀ {a} → Set a → Set a) : Set (lsuc (a ⊔ b)) where
  field
    _>>=′_ : {A : Set a} {B : Set b} → M A → (A → M B) → M B
    overlap {{super}} : Applicative′ {a} {b} M

open Monad′ using (super) public
open Monad′ {{...}} public hiding (super)

monadAp′ : ∀ {a b} {A : Set a} {B : Set b} {M : ∀ {a} → Set a → Set a}
             {{_ : Functor′ {a} {b} M}} →
            (M (A → B) → ((A → B) → M B) → M B) →
            M (A → B) → M A → M B
monadAp′ _>>=_ mf mx = mf >>= λ f → fmap′ f mx

infix -10 do_
do_ : ∀ {a} {A : Set a} → A → A
do x = x

infixr 0 do-bind do-seq do-pbind do-let

syntax do-bind  m (λ x → m₁) = x ← m -| m₁
syntax do-pbind m (λ x → m₁) = x ← m =| m₁
syntax do-seq   m m₁          = m ~| m₁
syntax do-let   m (λ x → m₁) = x := m -| m₁

do-bind = _>>=_
do-seq = _>>_
do-pbind = _>>=′_
do-let = case_of_

infixr 0 caseM_of_
caseM_of_ = _>>=_
