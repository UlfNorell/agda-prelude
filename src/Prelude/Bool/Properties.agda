module Prelude.Bool.Properties where


open import Prelude.Equality
open import Prelude.Bool
open import Prelude.Decidable
open import Prelude.Empty

-- Properties of ==? --
module _ {a} {A : Set a} {{EqA : Eq A}} where

  ==-reflexive : (x : A) → (x == x) ≡ yes refl
  ==-reflexive x with  x == x
  ...| yes refl = refl
  ...| no notEq = ⊥-elim (notEq refl)

  ==?-reflexive : (x : A) → (x ==? x) ≡ true
  ==?-reflexive x with  x == x
  ...| yes refl = refl
  ...| no notEq = ⊥-elim (notEq refl)

  ≡⇒==? : {x y : A} → (x ≡ y) → (x ==? y) ≡ true
  ≡⇒==? {x = x} {y = y} refl with x == y
  ...| yes refl = refl
  ...| no a≢b = ⊥-elim (a≢b refl)


  ≢⇒==? : {x y : A} → x ≢ y → (x ==? y) ≡ false
  ≢⇒==? {x = x} {y = y} x≢y with x == y
  ...| yes x≡y = ⊥-elim (x≢y x≡y)
  ...| no _ = refl

  ==?⇒≡ : {x y : A} → (x ==? y) ≡ true → x ≡ y
  ==?⇒≡ {x = x} {y = y} ==?≡true
    with x == y
  ...| yes x≡y = x≡y
  ...| no x≢y with (≢⇒==? x≢y) | ==?≡true
  ...| _ | ()

  ==?≡false⇒≢ : {a b : A} → (a ==? b) ≡ false → a ≢ b
  ==?≡false⇒≢ {a = a} {b = b} ==?≡false
    with a == b
  ...| no ¬eq = ¬eq
  ...| yes eq with ≡⇒==? | ==?≡false
  ...| _ | ()
