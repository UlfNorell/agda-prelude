
module Builtin.Float where

open import Prelude.Bool
open import Prelude.Equality
open import Prelude.Equality.Unsafe
open import Prelude.Decidable

postulate Float : Set

{-# BUILTIN FLOAT Float #-}

primitive
  primFloatEquality  : Float → Float → Bool

-- This is a little dangerous since NaN is not equal to itself, but the
-- type checker will accept refl : NaN ≡ NaN. Right now we don't export
-- any operations on floats so it's no problem, but there's some thinking
-- to be done if we want to.
EqFloat : Eq Float
EqFloat = record { _==_ = eqFloat }
  where
    eqFloat : ∀ x y → Dec (x ≡ y)
    eqFloat x y with primFloatEquality x y
    ... | true  = yes unsafeEqual
    ... | false = no  unsafeNotEqual
