module Prelude.Ord.Properties where

open import Prelude.Ord
open import Prelude.Empty
open import Prelude.Equality
open import Prelude.Equality.Inspect

open import Prelude.Function
open import Prelude.Decidable
open import Prelude.Bool
open import Prelude.Bool.Properties


-- Ord/Laws extra lemmas
module _  {ℓ} {A : Set ℓ} {{_ : Ord/Laws A}} where

  <⇒≤ : {a b : A} → a < b → a ≤ b
  <⇒≤ = lt-to-leq

  ≡⇒≮ : {a b : A} → a ≡ b → a ≮ b
  ≡⇒≮ refl a<b = less-antisym a<b a<b

  <⇒≱ : {a b : A} → a < b → a ≱ b
  <⇒≱ = flip leq-less-antisym

  ≮⇒≥ : {a b : A} → a ≮ b → a ≥ b
  ≮⇒≥ {a = a} {b = b} ¬a<b
    with compare a b
  ...| less a<b = ⊥-elim (¬a<b a<b)
  ...| equal a≡b = eq-to-leq (sym a≡b)
  ...| greater a>b = lt-to-leq a>b

  ≰⇒> : {a b : A} → a ≰ b → a > b
  ≰⇒> {a = a} {b = b} a≰b
    with compare a b
  ...| less a<b = ⊥-elim (a≰b (lt-to-leq a<b))
  ...| equal a≡b = ⊥-elim (a≰b (eq-to-leq a≡b))
  ...| greater b>a = b>a

  ≰⇒≥ : {a b : A} → a ≰ b → a ≥ b
  ≰⇒≥ = <⇒≤ ∘ ≰⇒>

  <?⇒< :  {a b : A} → (a <? b) ≡ true → a < b
  <?⇒< {a = a} {b = b} a<?b
    with compare a b
  ...| less a<b = a<b
  ...| equal a≡b rewrite a≡b = case a<?b of λ ()
  ...| greater _ = case a<?b of λ ()

  ≮?⇒≮ : {a b : A} → (a <? b) ≡ false → a ≮ b
  ≮?⇒≮ {a = a} {b = b} a≮?b
    with compare a b
  ...| less _ = case a≮?b of λ ()
  ...| equal a≡b rewrite a≡b = λ a<b → ⊥-elim (less-antirefl a<b)
  ...| greater a>b = λ a<b → ⊥-elim (less-antisym a>b a<b)

  ≤?⇒≤ :  {a b : A} → (a ≤? b) ≡ true → a ≤ b
  ≤?⇒≤ {a = a} {b = b} a≤?b
    with inspect (compare b a)
  ...| less a<b with≡ compare≡ rewrite compare≡ =
       case a≤?b of λ ()
  ...| equal a≡b with≡ _ = eq-to-leq (sym a≡b)
  ...| greater a>b with≡ _ = lt-to-leq a>b

  ≰?⇒≰ :  {a b : A} → (a ≤? b) ≡ false → a ≰ b
  ≰?⇒≰ {a = a} {b = b} a≰?b
    with (compare b a)
  ...| less b<a = <⇒≱ b<a
  ...| equal a≡b rewrite a≡b = case a≰?b of λ ()
  ...| greater _ = case a≰?b of λ ()

  ≰?⇒≥ : {a b : A} → (a ≤? b) ≡ false → a ≥ b
  ≰?⇒≥ = ≰⇒≥ ∘ ≰?⇒≰

  ≤⇒≤? : {a b : A} → a ≤ b → (a ≤? b) ≡ true
  ≤⇒≤? {a = a} {b = b} a≤b
    with compare b a
  ... | less lt = ⊥-elim ((<⇒≱ lt) a≤b)
  ... | equal eq = refl
  ... | greater gt = refl
