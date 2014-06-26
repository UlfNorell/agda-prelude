
module Control.WellFounded where

open import Prelude
open import Prelude.Equality.Unsafe using (safeEqual)

data Acc {a} {A : Set a} (_<_ : A → A → Set a) (x : A) : Set a where
  acc : (∀ y → y < x → Acc _<_ y) → Acc _<_ x

-- LessNat is well-founded --

private
  wfNoCheat : (n : Nat) → Acc LessThan n

  wfNoCheat′ : (n j y : Nat) → n ≡ suc (j + y) → Acc LessThan y
  wfNoCheat′ (suc n)  zero  .n refl = wfNoCheat n
  wfNoCheat′ (suc n) (suc j) y eq   = wfNoCheat′ n j y (safeEqual (suc-inj eq))
  wfNoCheat′ zero     zero   y ()
  wfNoCheat′ zero    (suc j) y ()

  wfNoCheat n = acc λ { y (diffP j eq) → wfNoCheat′ n j y eq }

  -- For performance reasons we don't bother the termination checker
  -- for the first 1 billion iterations. After those we do it the
  -- proper way.
  wfCheat : Nat → (n : Nat) → Acc LessThan n
  wfCheat zero       n = wfNoCheat n
  wfCheat (suc fuel) n = acc λ { y _ → wfCheat fuel y }

wfNat : (n : Nat) → Acc LessThan n
wfNat n = wfCheat 1000000000 n
