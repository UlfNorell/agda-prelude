{-# OPTIONS -v profile.interactive:700 #-}
module Data.Nat.GCD where

open import Prelude
open import Control.WellFounded
open import Data.Nat.Properties
open import Data.Nat.DivMod
open import Data.Nat.Divide
open import Tactic.Nat
open import Prelude.Equality.Unsafe

--- GCD ---

data GCD (a b : Nat) : Set where
  gcd-res : ∀ d → d Divides a → d Divides b → 
          (∀ k {{_ : NonZero k}} → k Divides a → k Divides b → k Divides d) →
          GCD a b

private
  gcd-step : ∀ {a b} q {r} → GCD (suc b) r → q * suc b + r ≡ a → GCD a (suc b)
  gcd-step q (gcd-res d d|b d|r gr) refl =
    gcd-res d (divides-add (divides-mul-r q d|b) d|r) d|b
            (λ k k|a k|b → gr k k|b (divides-sub-l k|a (divides-mul-r q k|b)))

  gcd-cert-acc : ∀ a b → Acc LessThan b → GCD a b
  gcd-cert-acc a zero _ = gcd-res a (factor! 1) (factor! 0) (λ k k|a _ → k|a)
  gcd-cert-acc a (suc b) (acc wf) =
    case a divmod suc b of λ
    { (qr q r lt eq) → gcd-step q (gcd-cert-acc (suc b) r (wf r lt)) eq }

gcd : ∀ a b → GCD a b
gcd a b =
  case gcd-cert-acc a b (wfNat b) of
  λ { (gcd-res d d|a d|b gr) → gcd-res d d|a d|b $ λ k k|a k|b → fast-divides (gr k k|a k|b) }

gcd! : Nat → Nat → Nat
gcd! a b = case gcd a b of λ { (gcd-res d _ _ _) → d }
