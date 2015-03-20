
module Control.WellFounded where

open import Prelude

data Acc {a} {A : Set a} (_<_ : A → A → Set a) (x : A) : Set a where
  acc : (∀ y → y < x → Acc _<_ y) → Acc _<_ x

-- LessNat is well-founded --

private
  wfNatSlow : (n : Nat) → Acc LessThan n

  wfNatSlow′ : (n j y : Nat) → n ≡ suc (j + y) → Acc LessThan y
  wfNatSlow′ (suc n)  zero  .n refl = wfNatSlow n
  wfNatSlow′ (suc n) (suc j) y eq   = wfNatSlow′ n j y (suc-inj eq)
  wfNatSlow′ zero     zero   y ()
  wfNatSlow′ zero    (suc j) y ()

  wfNatSlow n = acc λ { y (diff j eq) → wfNatSlow′ n j y eq }

  -- Need to match on n to avoid unfolding on neutral argument!
  wfNatFast : {k : Nat} → (n : Nat) → Acc LessThan n
  wfNatFast {zero}     n    = wfNatSlow n
  wfNatFast {suc k}  zero   = wfNatSlow zero
  wfNatFast {suc k} (suc n) = acc λ m _ → wfNatFast {k} m

wfNat : (n : Nat) → Acc LessThan n
wfNat n = wfNatFast {1000000000} n
