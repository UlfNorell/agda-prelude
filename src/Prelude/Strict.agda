
module Prelude.Strict where

open import Prelude.Equality

private
 primitive
  primForce      : ∀ {a b} {A : Set a} {B : A → Set b} (x : A) → (∀ x → B x) → B x
  primForceLemma : ∀ {a b} {A : Set a} {B : A → Set b} (x : A) (f : ∀ x → B x) → primForce x f ≡ f x

force : ∀ {a b} {A : Set a} {B : A → Set b} (x : A) → (∀ x → B x) → B x
force x f = primForce x f

forceLemma = primForceLemma

{-# INLINE force #-}

{-# DISPLAY primForce      = force #-}
{-# DISPLAY primForceLemma = forceLemma #-}

-- Warning: this doesn't work at compile-time due to call-by-name evaluation.
seq : ∀ {a b} {A : Set a} {B : Set b} → A → B → B
seq x y = force x (λ _ → y)

{-# INLINE seq #-}

infixr 0 _$!_
_$!_ : ∀ {a b} {A : Set a} {B : A → Set b} → (∀ x → B x) → ∀ x → B x
f $! x = force x f

{-# INLINE _$!_ #-}
