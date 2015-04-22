
module Prelude.Equality.Unsafe where

open import Prelude.Equality
open import Prelude.Empty
open import Prelude.Erased

private primitive primTrustMe : ∀ {a} {A : Set a} {x y : A} → x ≡ y

-- unsafeEqual {x = x} {y = y} evaluates to refl if x and y are
-- definitionally equal.
unsafeEqual : ∀ {a} {A : Set a} {x y : A} → x ≡ y
unsafeEqual = primTrustMe

{-# DISPLAY primTrustMe = [erased] #-}

-- Used in decidable equality for primitive types (String, Char and Float)
unsafeNotEqual : ∀ {a} {A : Set a} {x y : A} → ¬ (x ≡ y)
unsafeNotEqual _ = erase-⊥ trustme
  where postulate trustme : ⊥

-- Erase an equality proof. Throws away the actual proof
-- and replaces it by unsafeEqual.
eraseEquality : ∀ {a} {A : Set a} {x y : A} → x ≡ y → x ≡ y
eraseEquality _ = unsafeEqual

unsafeCoerce : ∀ {a} {A : Set a} {B : Set a} → A → B
unsafeCoerce {A = A} {B} x with unsafeEqual {x = A} {y = B}
unsafeCoerce x | refl = x