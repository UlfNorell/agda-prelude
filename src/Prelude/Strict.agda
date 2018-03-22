
module Prelude.Strict where

open import Prelude.Equality
open import Agda.Builtin.Strict

force : ∀ {a b} {A : Set a} {B : A → Set b} (x : A) → (∀ x → B x) → B x
force x f = primForce x f

force′ : ∀ {a b} {A : Set a} {B : A → Set b} → (x : A) → (∀ y → x ≡ y → B y) → B x
force′ x k = (force x λ y → k y) refl

forceLemma = primForceLemma

{-# INLINE force #-}

{-# DISPLAY primForce      = force #-}
{-# DISPLAY primForceLemma = forceLemma #-}

seq : ∀ {a b} {A : Set a} {B : Set b} → A → B → B
seq x y = force x (λ _ → y)

{-# INLINE seq #-}

infixr 0 _$!_
_$!_ : ∀ {a b} {A : Set a} {B : A → Set b} → (∀ x → B x) → ∀ x → B x
f $! x = force x f

{-# INLINE _$!_ #-}
