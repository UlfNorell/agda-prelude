
module Prelude.Semiring where

open import Prelude.Nat
open import Prelude.Function

record Semiring {a} (A : Set a) : Set a where
  infixl 6 _+_
  infixl 7 _*_
  field zro one : A
        _+_ _*_ : A → A → A
        fromNat : Nat → A

open Semiring {{...}} public

infixr 8 _^_
_^_ : ∀ {a} {A : Set a} {{_ : Semiring A}} → A → Nat → A
n ^ zero  = one
n ^ suc m = n ^ m * n

instance
  SemiringNat : Semiring Nat
  SemiringNat = record { zro = 0 ; one = 1
                       ; _+_ = _+N_ ; _*_ = _*N_
                       ; fromNat = id }
