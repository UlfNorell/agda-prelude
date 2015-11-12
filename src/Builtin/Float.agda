
module Builtin.Float where

open import Prelude
open import Prelude.Equality.Unsafe

postulate Float : Set

{-# BUILTIN FLOAT Float #-}

private
 primitive
  primFloatEquality : Float → Float → Bool
  primFloatLess     : Float → Float → Bool
  primNatToFloat    : Nat → Float
  primFloatPlus     : Float → Float → Float
  primFloatMinus    : Float → Float → Float
  primFloatTimes    : Float → Float → Float
  primFloatDiv      : Float → Float → Float
  primFloatSqrt     : Float → Float
  primRound         : Float → Int
  primFloor         : Float → Int
  primCeiling       : Float → Int
  primExp           : Float → Float
  primLog           : Float → Float
  primSin           : Float → Float
  primShowFloat     : Float → String

natToFloat : Nat → Float
natToFloat = primNatToFloat

intToFloat : Int → Float
intToFloat (pos    x) = natToFloat x
intToFloat (negsuc x) = primFloatMinus -1.0 (natToFloat x)

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
      ...   | false with≡ _  = equal unsafeEqual

instance
  ShowFloat : Show Float
  ShowFloat = simpleShowInstance primShowFloat

instance
  NumFloat : Number Float
  Number.Constraint NumFloat _ = ⊤
  Number.fromNat    NumFloat x = primNatToFloat x

  SemiringFloat : Semiring Float
  Semiring.zro SemiringFloat = 0.0
  Semiring.one SemiringFloat = 1.0
  Semiring._+_ SemiringFloat = primFloatPlus
  Semiring._*_ SemiringFloat = primFloatTimes

  SubFloat : Subtractive Float
  Subtractive._-_    SubFloat   = primFloatMinus
  Subtractive.negate SubFloat x = 0.0 - x

  NegFloat : Negative Float
  Negative.Constraint NegFloat _ = ⊤
  Negative.fromNeg    NegFloat x = negate (primNatToFloat x)

  FracFloat : Fractional Float
  Fractional.Constraint FracFloat _ _ = ⊤
  Fractional._/_ FracFloat x y = primFloatDiv x y

floor   = primFloor
round   = primRound
ceiling = primCeiling
exp     = primExp
ln      = primLog
sin     = primSin
sqrt    = primFloatSqrt

π : Float
π = 3.141592653589793

cos : Float → Float
cos x = sin (π / 2.0 - x)

tan : Float → Float
tan x = sin x / cos x

log : Float → Float → Float
log base x = ln x / ln base

_**_ : Float → Float → Float
a ** x = exp (x * ln a)
