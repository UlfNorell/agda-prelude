
module Prelude.Nat where

open import Prelude.Unit
open import Prelude.Empty
open import Prelude.Bool
open import Prelude.Decidable
open import Prelude.Equality
open import Prelude.Equality.Unsafe using (eraseEquality)
open import Prelude.Ord
open import Prelude.Number
open import Prelude.Semiring
open import Prelude.Function
open import Prelude.Smashed

open import Prelude.Nat.Properties
open import Prelude.Nat.Core public

--- Equality ---

private
  eqNatSound : ∀ n m → IsTrue (eqNat n m) → n ≡ m
  eqNatSound zero zero _ = refl
  eqNatSound zero (suc m) ()
  eqNatSound (suc n) zero ()
  eqNatSound (suc n) (suc m) p rewrite eqNatSound n m p = refl

  eqNatComplete : ∀ n m → IsFalse (eqNat n m) → ¬ (n ≡ m)
  eqNatComplete zero zero () eq
  eqNatComplete zero (suc m) neq ()
  eqNatComplete (suc n) zero neq ()
  eqNatComplete (suc n) (suc m) neq eq = eqNatComplete n m neq (suc-inj eq)

  decEqNat : (n m : Nat) → Dec (n ≡ m)
  decEqNat n m with eqNat n m | eqNatSound n m | eqNatComplete n m
  ... | true  | eq | _   = yes (eraseEquality (eq true))
  ... | false | _  | neq = no  (eraseNegation (neq false))
  {-# INLINE decEqNat #-}

instance
  EqNat : Eq Nat
  _==_ {{EqNat}} = decEqNat

--- Comparison ---

data LessNat n m : Set where
  diff : ∀ k (eq : m ≡ suc k +N n) → LessNat n m

{-# DISPLAY LessNat a b = a < b #-}

pattern diff! k = diff k refl

private
  lemLessNatMinus : ∀ n m → IsTrue (lessNat n m) → m ≡ suc (m - suc n) + n
  lemLessNatMinus  _       zero  ()
  lemLessNatMinus  zero   (suc m) _   = sym (suc $≡ add-zero-r m)
  lemLessNatMinus (suc n) (suc m) n<m = suc $≡ (lemLessNatMinus n m n<m ⟨≡⟩ʳ add-suc-r (m - suc n) n)

  lemNoLessEqual : ∀ n m → ¬ IsTrue (lessNat n m) → ¬ IsTrue (lessNat m n) → n ≡ m
  lemNoLessEqual zero zero _ _ = refl
  lemNoLessEqual zero (suc m) h₁ h₂ = ⊥-elim (h₁ true)
  lemNoLessEqual (suc n) zero h₁ h₂ = ⊥-elim (h₂ true)
  lemNoLessEqual (suc n) (suc m) h₁ h₂ = cong suc (lemNoLessEqual n m h₁ h₂)

  -- Using eraseEquality here lets us not worry about the performance of the
  -- proofs.
  compareNat : ∀ n m → Comparison LessNat n m
  compareNat n m with decBool (lessNat n m)
  ... | yes p = less (diff (m - suc n) (eraseEquality (lemLessNatMinus n m p)))
  ... | no np₁ with decBool (lessNat m n)
  ...             | yes p  = greater (diff (n - suc m) (eraseEquality (lemLessNatMinus m n p)))
  ...             | no np₂ = equal (eraseEquality (lemNoLessEqual n m np₁ np₂))
  {-# INLINE compareNat #-}

private
  nat-lt-to-leq : ∀ {x y} → LessNat x y → LessNat x (suc y)
  nat-lt-to-leq (diff k eq) = diff (suc k) (cong suc eq)

  nat-eq-to-leq : ∀ {x y} → x ≡ y → LessNat x (suc y)
  nat-eq-to-leq eq = diff 0 (cong suc (sym eq))

  nat-from-leq : ∀ {x y} → LessNat x (suc y) → LessEq LessNat x y
  nat-from-leq (diff zero eq)    = equal (sym (suc-inj eq))
  nat-from-leq (diff (suc k) eq) = less (diff k (suc-inj eq))

  nat-lt-antirefl : ∀ {a} → LessNat a a → ⊥
  nat-lt-antirefl {a} (diff k eq) = case add-inj₁ 0 (suc k) a eq of λ ()

  nat-lt-antisym : ∀ {a b} → LessNat a b → LessNat b a → ⊥
  nat-lt-antisym {a} (diff! k) (diff j eq) =
    case add-inj₁ 0 (suc j + suc k) a (eq ⟨≡⟩ suc $≡ add-assoc j (suc k) a) of λ ()

  nat-lt-trans : ∀ {a b c} → LessNat a b → LessNat b c → LessNat a c
  nat-lt-trans (diff k eq) (diff j eq₁) = diff (j + suc k) (eraseEquality
    (case eq of λ where refl → case eq₁ of λ where refl → add-assoc (suc j) (suc k) _))

instance
  OrdNat : Ord Nat
  Ord._<_         OrdNat = LessNat
  Ord._≤_         OrdNat a b = LessNat a (suc b)
  Ord.compare     OrdNat = compareNat
  Ord.eq-to-leq   OrdNat = nat-eq-to-leq
  Ord.lt-to-leq   OrdNat = nat-lt-to-leq
  Ord.leq-to-lteq OrdNat = nat-from-leq

  OrdNatLaws : Ord/Laws Nat
  Ord/Laws.super OrdNatLaws = it
  less-antirefl {{OrdNatLaws}} = nat-lt-antirefl
  less-trans    {{OrdNatLaws}} = nat-lt-trans

instance
  SmashedNatLess : {a b : Nat} → Smashed (a < b)
  smashed {{SmashedNatLess}} {diff! k} {diff k₁ eq} with add-inj₁ (suc k) (suc k₁) _ eq | eq
  ... | refl | refl = refl

  SmashedNatComp : {a b : Nat} → Smashed (Comparison _<_ a b)
  smashed {{SmashedNatComp}} {less _    } {less _    } = less $≡ smashed
  smashed {{SmashedNatComp}} {less lt   } {equal refl} = ⊥-elim (less-antirefl {A = Nat} lt)
  smashed {{SmashedNatComp}} {less lt   } {greater gt} = ⊥-elim (less-antisym  {A = Nat} lt gt)
  smashed {{SmashedNatComp}} {equal refl} {less lt   } = ⊥-elim (less-antirefl {A = Nat} lt)
  smashed {{SmashedNatComp}} {equal _   } {equal _   } = equal $≡ smashed
  smashed {{SmashedNatComp}} {equal refl} {greater gt} = ⊥-elim (less-antirefl {A = Nat} gt)
  smashed {{SmashedNatComp}} {greater gt} {less lt   } = ⊥-elim (less-antisym  {A = Nat} lt gt)
  smashed {{SmashedNatComp}} {greater gt} {equal refl} = ⊥-elim (less-antirefl {A = Nat} gt)
  smashed {{SmashedNatComp}} {greater _ } {greater _ } = greater $≡ smashed

suc-monotone : {a b : Nat} → a < b → Nat.suc a < suc b
suc-monotone (diff! k) = diff k (sym (add-suc-r (suc k) _))

suc-comparison : {a b : Nat} → Comparison _<_ a b → Comparison _<_ (Nat.suc a) (suc b)
suc-comparison (less lt)    = less    (suc-monotone lt)
suc-comparison (equal eq)   = equal   (suc $≡ eq)
suc-comparison (greater gt) = greater (suc-monotone gt)
