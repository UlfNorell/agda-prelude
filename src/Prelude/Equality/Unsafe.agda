
module Prelude.Equality.Unsafe where

open import Prelude.Equality
open import Prelude.Empty

private primitive primTrustMe : ∀ {a} {A : Set a} {x y : A} → x ≡ y

-- unsafeEqual {x = x} {y = y} evaluates to refl if x and y are
-- definitionally equal.
unsafeEqual : ∀ {a} {A : Set a} {x y : A} → x ≡ y
unsafeEqual = primTrustMe

-- "Safe" version of unsafeEqual. Throws away the actual proof
-- and replaces it by unsafeEqual.
safeEqual : ∀ {a} {A : Set a} {x y : A} → x ≡ y → x ≡ y
safeEqual _ = unsafeEqual

postulate
 unsafeNotEqual : ∀ {a} {A : Set a} {x y : A} → ¬ (x ≡ y)

safeNotEqual : ∀ {a} {A : Set a} {x y : A} → ¬ (x ≡ y) → ¬ (x ≡ y)
safeNotEqual _ = unsafeNotEqual

unsafeCoerce : ∀ {a} {A : Set a} {B : Set a} → A → B
unsafeCoerce {A = A} {B} x with unsafeEqual {x = A} {y = B}
unsafeCoerce x | refl = x