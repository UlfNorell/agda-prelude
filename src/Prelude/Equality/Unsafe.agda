
module Prelude.Equality.Unsafe where

open import Prelude.Equality
open import Prelude.Empty

private primitive primTrustMe : ∀ {a} {A : Set a} {x y : A} → x ≡ y

-- unsafeEqual {x = x} {y = y} evaluates to refl if x and y are
-- definitionally equal.

unsafeEqual : ∀ {a} {A : Set a} {x y : A} → x ≡ y
unsafeEqual = primTrustMe

postulate
  unsafeNotEqual : ∀ {a} {A : Set a} {x y : A} → ¬ (x ≡ y)

unsafeCoerce : ∀ {a} {A : Set a} {B : Set a} → A → B
unsafeCoerce {A = A} {B} x with unsafeEqual {x = A} {y = B}
unsafeCoerce x | refl = x