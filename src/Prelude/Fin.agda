
module Prelude.Fin where

open import Prelude.Nat
open import Prelude.Equality
open import Prelude.Decidable
open import Prelude.Ord
open import Prelude.Bool
open import Prelude.Function
open import Prelude.Number
open import Prelude.Nat.Properties using (suc-inj)

data Fin : Nat → Set where
  zero : ∀ {n} → Fin (suc n)
  suc  : ∀ {n} (i : Fin n) → Fin (suc n)

finToNat : ∀ {n} → Fin n → Nat
finToNat  zero   = zero
finToNat (suc i) = suc (finToNat i)

finToNat-inj : ∀ {n} {i j : Fin n} → finToNat i ≡ finToNat j → i ≡ j
finToNat-inj {i = zero } {zero } p = refl
finToNat-inj {i = zero } {suc j} ()
finToNat-inj {i = suc i} {zero } ()
finToNat-inj {i = suc i} {suc j} p rewrite finToNat-inj (suc-inj p) = refl

natToFin : ∀ {n} (m : Nat) {{m<n : IsTrue (lessNat m n)}} → Fin n
natToFin {zero }  _   {{}}
natToFin {suc n}  zero   = zero
natToFin {suc n} (suc m) = suc (natToFin m)

instance
  NumberFin : ∀ {n} → Number (Fin n)
  Number.Constraint (NumberFin {n}) k = IsTrue (lessNat k n)
  fromNat {{NumberFin}} = natToFin

--- Equality ---

fsuc-inj : ∀ {n} {i j : Fin n} → Fin.suc i ≡ suc j → i ≡ j
fsuc-inj refl = refl

private
  eqFin : ∀ {n} (i j : Fin n) → Dec (i ≡ j)
  eqFin  zero    zero    = yes refl
  eqFin  zero   (suc  j) = no λ ()
  eqFin (suc i)  zero    = no λ ()
  eqFin (suc i) (suc  j) with eqFin i j
  eqFin (suc i) (suc .i) | yes refl = yes refl
  eqFin (suc i) (suc  j) | no neq   = no λ eq → neq (fsuc-inj eq)

instance
  EqFin : ∀ {n} → Eq (Fin n)
  _==_ {{EqFin}} = eqFin

--- Ord ---

instance
  OrdFin : ∀ {n} → Ord (Fin n)
  OrdFin = OrdBy finToNat-inj

  OrdLawsFin : ∀ {n} → Ord/Laws (Fin n)
  OrdLawsFin = OrdLawsBy finToNat-inj
