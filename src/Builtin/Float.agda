
module Builtin.Float where

open import Prelude
open import Prelude.Equality.Unsafe

open import Agda.Builtin.Float
open Agda.Builtin.Float public using (Float)

natToFloat : Nat → Float
natToFloat = primNatToFloat

intToFloat : Int → Float
intToFloat (pos    x) = natToFloat x
intToFloat (negsuc x) = primFloatMinus -1.0 (natToFloat x)

instance
  EqFloat : Eq Float
  _==_ {{EqFloat}} x y with primFloatEquality x y
  ... | true  = yes unsafeEqual
  ... | false = no  unsafeNotEqual

data LessFloat (x y : Float) : Set where
  less-float : primFloatNumericalLess x y ≡ true → LessFloat x y

instance
  OrdFloat : Ord Float
  OrdFloat = defaultOrd cmpFloat
    where
      cmpFloat : ∀ x y → Comparison LessFloat x y
      cmpFloat x y with inspect (primFloatNumericalLess x y)
      ... | true  with≡ eq = less (less-float eq)
      ... | false with≡ _ with inspect (primFloatNumericalLess y x)
      ...   | true  with≡ eq = greater (less-float eq)
      ...   | false with≡ _  = equal unsafeEqual

  OrdLawsFloat : Ord/Laws Float
  Ord/Laws.super OrdLawsFloat    = it
  less-antirefl {{OrdLawsFloat}} (less-float eq) = unsafeNotEqual eq
  less-antisym  {{OrdLawsFloat}} (less-float eq) (less-float eq₁) = unsafeNotEqual (eq ⟨≡⟩ʳ eq₁)
  less-trans    {{OrdLawsFloat}} (less-float _)  (less-float _)   = less-float unsafeEqual

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
  Subtractive._-_    SubFloat = primFloatMinus
  Subtractive.negate SubFloat = primFloatNegate

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

NaN : Float
NaN = 0.0 / 0.0

Inf : Float
Inf = 1.0 / 0.0

-Inf : Float
-Inf = -1.0 / 0.0
