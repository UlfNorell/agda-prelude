
module Prelude.Semiring where

open import Prelude.Nat.Core
open import Prelude.Function

record Semiring {a} (A : Set a) : Set a where
  infixl 6 _+_
  infixl 7 _*_
  field zro one : A
        _+_ _*_ : A → A → A

open Semiring {{...}} public

{-# DISPLAY Semiring.zro _ = zro #-}
{-# DISPLAY Semiring.one _ = one #-}
{-# DISPLAY Semiring._+_ _ a b = a + b #-}
{-# DISPLAY Semiring._*_ _ a b = a * b #-}

infixr 8 _^_
_^_ : ∀ {a} {A : Set a} {{_ : Semiring A}} → A → Nat → A
n ^ zero  = one
n ^ suc m = n ^ m * n

record Subtractive {a} (A : Set a) : Set a where
  infixl 6 _-_
  field _-_    : A → A → A
        negate : A → A

open Subtractive {{...}} public

{-# DISPLAY Subtractive._-_ _ a b = a - b #-}
{-# DISPLAY Subtractive.negate _ = negate #-}
