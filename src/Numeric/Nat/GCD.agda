
module Numeric.Nat.GCD where

open import Prelude
open import Control.WellFounded
open import Numeric.Nat.Properties
open import Numeric.Nat.DivMod
open import Numeric.Nat.Divide
open import Tactic.Nat

--- GCD ---

data GCD (a b : Nat) : Set where
  gcd-res : ∀ d (d|a : d Divides a) (d|b : d Divides b)
              (g : ∀ k → k Divides a → k Divides b → k Divides d) →
              GCD a b

get-gcd : ∀ {a b} → GCD a b → Nat
get-gcd (gcd-res d _ _ _) = d

private
  gcd-step : ∀ {a b} q {r} → GCD (suc b) r → q * suc b + r ≡ a → GCD a (suc b)
  gcd-step q (gcd-res d d|b d|r gr) refl =
    gcd-res d (divides-add (divides-mul-r q d|b) d|r) d|b
            (λ k k|a k|b → gr k k|b (divides-sub-l k|a (divides-mul-r q k|b)))

  gcd-cert-acc : ∀ a b → Acc _<_ b → GCD a b
  gcd-cert-acc a zero _ = gcd-res a (factor 1 auto) (factor! 0) (λ k k|a _ → k|a)
  gcd-cert-acc a (suc b) (acc wf) =
    case a divmod suc b of λ
    { (qr q r lt eq) → gcd-step q (gcd-cert-acc (suc b) r (wf r lt)) eq }

private
  erase-prf : ∀ {a b} → GCD a b → GCD a b
  erase-prf (gcd-res d d|a d|b gr) = gcd-res d (fast-divides d|a) (fast-divides d|b)
                                     λ k k|a k|b → fast-divides (gr k k|a k|b)

gcd : ∀ a b → GCD a b
gcd 0 b = gcd-res b (factor! 0) divides-refl (λ _ _ k|b → k|b)
gcd 1 b = gcd-res 1 divides-refl (factor b auto) (λ _ k|1 _ → k|1)
gcd a b = erase-prf (gcd-cert-acc a b (wfNat b))

gcd! : Nat → Nat → Nat
gcd! a b = get-gcd (gcd a b)

--- Properties ---

private
  gcd-unique′ : ∀ {a b} (g₁ g₂ : GCD a b) → get-gcd g₁ ≡ get-gcd g₂
  gcd-unique′ (gcd-res zero _ _ _) (gcd-res zero _ _ _) = refl
  gcd-unique′ (gcd-res zero 0|a 0|b _) (gcd-res (suc d) _ _ gr) =
    sym (divides-zero (gr 0 0|a 0|b))
  gcd-unique′ (gcd-res (suc d) _ _ gr) (gcd-res zero 0|a 0|b _) =
    divides-zero (gr 0 0|a 0|b)
  gcd-unique′ (gcd-res (suc d) d|a d|b grd) (gcd-res (suc d′) d′|a d′|b grd′) =
    divides-antisym (grd′ (suc d) d|a d|b)
                    (grd (suc d′) d′|a d′|b)

gcd-unique : ∀ a b d → d Divides a → d Divides b → (∀ k → k Divides a → k Divides b → k Divides d) →
               gcd! a b ≡ d
gcd-unique a b d d|a d|b gr = gcd-unique′ (gcd a b) (gcd-res d d|a d|b gr)

gcd-mul-l : ∀ a b → gcd! a (a * b) ≡ a
gcd-mul-l a b = gcd-unique a (a * b) a divides-refl (divides-mul-l b divides-refl) (λ _ k|a _ → k|a)

gcd-mul-r : ∀ a b → gcd! b (a * b) ≡ b
gcd-mul-r a b = gcd-unique b (a * b) b divides-refl (divides-mul-r a divides-refl) (λ _ k|b _ → k|b)

gcd-zero : ∀ n → gcd! 0 n ≡ n
gcd-zero n = gcd-unique 0 n n (factor! 0) divides-refl (λ _ _ k|n → k|n)

gcd-commute : ∀ a b → gcd! a b ≡ gcd! b a
gcd-commute a b with gcd b a
gcd-commute a b | gcd-res d d|b d|a g = gcd-unique a b d d|a d|b (λ k → flip (g k))
