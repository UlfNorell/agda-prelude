module Prelude.Bool.Properties where


open import Prelude.Equality
open import Prelude.Bool
open import Prelude.Decidable
open import Prelude.Empty
open import Prelude.Variables

de-morg-neg-conj : (a b : Bool) → not (a && b) ≡ (not a || not b)
de-morg-neg-conj true true = refl
de-morg-neg-conj false true = refl
de-morg-neg-conj true false  = refl
de-morg-neg-conj false false  = refl

de-morg-neg-disj : (a : Bool) → (b : Bool) → not (a || b) ≡ (not a && not b)
de-morg-neg-disj true true = refl
de-morg-neg-disj false true = refl
de-morg-neg-disj true false  = refl
de-morg-neg-disj false false  = refl

true≢false : _≢_ {A = Bool} true false
true≢false ()

false≢true : _≢_ {A = Bool} false true
false≢true ()

x||true : (x || true) ≡ true
x||true {true} = refl
x||true {false} = refl

x&&false : (x && false) ≡ false
x&&false {true} = refl
x&&false {false} = refl

IsTrue⇒≡ : IsTrue x → x ≡ true
IsTrue⇒≡ true = refl

IsFalse⇒≡ : IsFalse x → x ≡ false
IsFalse⇒≡ false = refl

not[x]≡false⇒x≡true : not x ≡ false → x ≡ true
not[x]≡false⇒x≡true {true} _ = refl
not[x]≡false⇒x≡true {false} ()

not[x]≡true⇒x≡false : not x ≡ true → x ≡ false
not[x]≡true⇒x≡false {true} ()
not[x]≡true⇒x≡false {false} _ = refl

-- Properties of ==? --
module _ {a} {A : Set a} {{EqA : Eq A}} where

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
