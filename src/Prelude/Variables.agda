
module Prelude.Variables where

open import Agda.Primitive
open import Agda.Builtin.Nat
open import Agda.Builtin.List

variable
  ℓ ℓ₁ ℓ₂ ℓ₃ : Level
  A B C : Set ℓ
  F M : Set ℓ₁ → Set ℓ₂
  x y z : A
  xs ys zs : List A
  n m : Nat
