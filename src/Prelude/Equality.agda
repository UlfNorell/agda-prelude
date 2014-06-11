
module Prelude.Equality where

infix 4 _≡_
data _≡_ {a} {A : Set a} (x : A) : A → Set a where
  refl : x ≡ x

{-# BUILTIN EQUALITY _≡_ #-}
{-# BUILTIN REFL refl #-}

open import Prelude.Decidable

record Eq {a} (A : Set a) : Set a where
  infix 4 _==_
  field
    _==_ : (x y : A) → Dec (x ≡ y)

open Eq {{...}} public
