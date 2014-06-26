
module Control.WellFounded where

open import Prelude

data Acc {a} {A : Set a} (_<_ : A → A → Set a) (x : A) : Set a where
  acc : (∀ y → y < x → Acc _<_ y) → Acc _<_ x

private
  -- Don't bother the termination checker for the first N iterations.
  -- After those we do it the proper way.
  fastAcc′ : ∀ {a} {A : Set a} {R : A → A → Set a} → Nat → (∀ y → Acc R y) → ∀ x → Acc R x
  fastAcc′ zero    wf x = wf x
  fastAcc′ (suc n) wf _ = acc λ { y _ → fastAcc′ n wf y }

fastAcc : ∀ {a} {A : Set a} {R : A → A → Set a} → (∀ y → Acc R y) → ∀ x → Acc R x
fastAcc = fastAcc′ 1000000000

-- LessNat is well-founded --

private
  wfNatSlow : (n : Nat) → Acc LessThan n

  wfNatSlow′ : (n j y : Nat) → n ≡ suc (j + y) → Acc LessThan y
  wfNatSlow′ (suc n)  zero  .n refl = wfNatSlow n
  wfNatSlow′ (suc n) (suc j) y eq   = wfNatSlow′ n j y (suc-inj eq)
  wfNatSlow′ zero     zero   y ()
  wfNatSlow′ zero    (suc j) y ()

  wfNatSlow n = acc λ { y (diffP j eq) → wfNatSlow′ n j y eq }

wfNat : (n : Nat) → Acc LessThan n
wfNat n = fastAcc wfNatSlow n
