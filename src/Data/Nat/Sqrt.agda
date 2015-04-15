
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
  a <? .a | equal  refl = no (λ a<a → refute a<a)
  a <?  b | greater a>b = no (λ a<b → less-antisym a>b a<b)

sqrt : ∀ n → Sqrt n
sqrt 0 = root 0 (diff! 0) (diff! 0)  -- just to avoid unfolding neutral application
sqrt n with binarySearch 0 n (λ r → n <? r ^ 2)
sqrt n | here k !n< n< _ _ = root k (less-raa (λ lt → !n< (by lt))) n<
sqrt 0 | none _ = root 0 (diff! 0) (diff! 0)
sqrt 1 | none _ = root 1 (diff! 0) (diff! 2)
sqrt (suc (suc n)) | none !n<n² = ⊥-elim (!n<n² auto)
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
