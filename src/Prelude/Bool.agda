
module Prelude.Bool where

open import Prelude.Unit
open import Prelude.Empty
open import Prelude.Equality
open import Prelude.Decidable
open import Prelude.Function

data Bool : Set where
  false true : Bool

{-# BUILTIN BOOL Bool   #-}
{-# BUILTIN TRUE true   #-}
{-# BUILTIN FALSE false #-}

{-# COMPILED_DATA Bool Bool False True #-}

infix 0 if_then_else_
if_then_else_ : ∀ {a} {A : Set a} → Bool → A → A → A
if true  then x else y = x
if false then x else y = y

infixr 3 _&&_
infixr 2 _||_

_||_ : Bool → Bool → Bool
true  || _ = true
false || x = x

_&&_ : Bool → Bool → Bool
true  && x = x
false && _ = false

not : Bool → Bool
not true  = false
not false = true

IsTrue : Bool → Set
IsTrue true  = ⊤
IsTrue false = ⊥

IsFalse : Bool → Set
IsFalse = IsTrue ∘ not

eqBool : (x y : Bool) → Dec (x ≡ y)
eqBool false false = yes refl
eqBool false true  = no (λ ())
eqBool true  false = no (λ ())
eqBool true  true  = yes refl

EqBool : Eq Bool
EqBool = record { _==_ = eqBool }

isYes : ∀ {a} {A : Set a} → Dec A → Bool
isYes (yes _) = true
isYes (no _)  = false

isNo : ∀ {a} {A : Set a} → Dec A → Bool
isNo = not ∘ isYes

if′_then_else : ∀ {a} {A : Set a} (b : Bool) → ({{_ : IsTrue b}} → A) → ({{_ : IsFalse b}} → A) → A
if′ true  then x else _ = x
if′ false then _ else y = y
