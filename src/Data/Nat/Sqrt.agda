
module Data.Nat.Sqrt where

open import Prelude hiding (_<?_)
open import Data.Nat.Properties
open import Tactic.Nat
open import Data.Nat.BinarySearch

data Sqrt n : Set where
  root : ∀ r → r ^ 2 ≤ n → n < suc r ^ 2 → Sqrt n

getSqrt : ∀ {n} → Sqrt n → Nat
getSqrt (root r _ _) = r

private
  infix 4 _<?_
  _<?_ : (a b : Nat) → Dec (a < b)
  a <?  b with compare a b
  a <?  b | less    a<b = yes a<b
  a <? .a | equal  refl = no (λ a<a → less-antirefl a<a refl)
  a <?  b | greater a>b = no (λ a<b → less-antisym a>b a<b)

sqrt : ∀ n → Sqrt n
sqrt n with binarySearch 0 n (λ r → n <? r ^ 2)
sqrt n | here k !n< n< _ _ = root k (less-raa (λ lt → !n< (suc-monotoneʳ lt))) n<
sqrt 0 | none !n<n² = root 0 (diff! 0) (diff! 0)
sqrt 1 | none !n<n² = root 1 (diff! 0) (diff! 2)
sqrt (suc (suc n)) | none !n<n² = ⊥-elim (!n<n² (diff (n * (n + 3) + 1) auto))
sqrt n | below (diff _ ())
sqrt n | bad-range (diff _ ())

sqrt! : Nat → Nat
sqrt! n = getSqrt (sqrt n)

sqrt-below : ∀ n → sqrt! n ^ 2 ≤ n
sqrt-below n with sqrt n
... | root _ lo _ = lo

sqrt-above : ∀ n → suc (sqrt! n) ^ 2 > n
sqrt-above n with sqrt n
... | root _ _ hi = hi

private
  lem : (n r a : Nat) →
        4 + n ≡ suc a + r * r →
        LessNat (suc n) r → ⊥
  lem n ._ a eq (diff! c) = refute eq

sqrt-less : ∀ n → n > 2 → suc (sqrt! n) < n
sqrt-less 0 (diff k ())
sqrt-less 1 (diff k eq) = refute eq
sqrt-less 2 (diff k eq) = refute eq
sqrt-less (suc (suc (suc n))) _ with sqrt (3 + n)
sqrt-less (suc (suc (suc n))) _ | root r (diff a eq) _ =
  less-raa (lem n r a eq ∘ suc-monotoneʳ ∘ suc-monotoneʳ)
