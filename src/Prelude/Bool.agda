
module Prelude.Bool where

open import Prelude.Unit
open import Prelude.Empty
open import Prelude.Equality
open import Prelude.Decidable
open import Prelude.Function

open import Agda.Builtin.Bool public

infix 0 if_then_else_
if_then_else_ : ∀ {a} {A : Set a} → Bool → A → A → A
if true  then x else y = x
if false then x else y = y
{-# INLINE if_then_else_ #-}

infixr 3 _&&_
infixr 2 _||_

_||_ : Bool → Bool → Bool
true  || _ = true
false || x = x
{-# INLINE _||_ #-}

_&&_ : Bool → Bool → Bool
true  && x = x
false && _ = false
{-# INLINE _&&_ #-}

not : Bool → Bool
not true  = false
not false = true
{-# INLINE not #-}

data IsTrue : Bool → Set where
  instance true : IsTrue true

data IsFalse : Bool → Set where
  instance false : IsFalse false

instance
  EqBool : Eq Bool
  _==_ {{EqBool}} false false = yes refl
  _==_ {{EqBool}} false true  = no λ ()
  _==_ {{EqBool}} true  false = no λ ()
  _==_ {{EqBool}} true  true  = yes refl

decBool : ∀ b → Dec (IsTrue b)
decBool false = no λ ()
decBool true  = yes true
{-# INLINE decBool #-}

isYes : ∀ {a} {A : Set a} → Dec A → Bool
isYes (yes _) = true
isYes (no _)  = false

isNo : ∀ {a} {A : Set a} → Dec A → Bool
isNo = not ∘ isYes

infix 0 if′_then_else_
if′_then_else_ : ∀ {a} {A : Set a} (b : Bool) → ({{_ : IsTrue b}} → A) → ({{_ : IsFalse b}} → A) → A
if′ true  then x else _ = x
if′ false then _ else y = y
