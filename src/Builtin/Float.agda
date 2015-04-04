
module Builtin.Float where

open import Prelude.Bool
open import Prelude.Equality
open import Prelude.Equality.Unsafe
open import Prelude.Decidable
open import Prelude.Ord

postulate Float : Set

{-# BUILTIN FLOAT Float #-}

primitive
  primFloatEquality : Float → Float → Bool
  primFloatLess     : Float → Float → Bool 

-- This is a little dangerous since NaN is not equal to itself, but the
-- type checker will accept refl : NaN ≡ NaN. Right now we don't export
-- any operations on floats so it's no problem, but there's some thinking
-- to be done if we want to.
instance
  EqFloat : Eq Float
  EqFloat = record { _==_ = eqFloat }
    where
      eqFloat : ∀ x y → Dec (x ≡ y)
      eqFloat x y with primFloatEquality x y
      ... | true  = yes unsafeEqual
      ... | false = no  unsafeNotEqual

data LessFloat (x y : Float) : Set where
  less-float : primFloatLess x y ≡ true → LessFloat x y

instance
  OrdFloat : Ord Float
  OrdFloat = defaultOrd cmpFloat
    where
      cmpFloat : ∀ x y → Comparison LessFloat x y
      cmpFloat x y with inspect (primFloatLess x y)
      ... | true  with≡ eq = less (less-float eq)
      ... | false with≡ _ with inspect (primFloatLess y x)
      ...   | true  with≡ eq = greater (less-float eq)
      ...   | false with≡ _  = equal unsafeEqual   -- Same issue with NaN as for equality
