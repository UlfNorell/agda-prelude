
module Prelude.Ord.Reasoning where

open import Prelude.Equality
open import Prelude.Ord
open import Prelude.Function

module _ {a} {A : Set a} {{OrdA : Ord/Laws A}} where

  private
    lt/leq-trans : ∀ {x y z : A} → x < y → y ≤ z → x < z
    lt/leq-trans x<y y≤z =
      case leq-to-lteq {A = A} y≤z of λ where
        (less  y<z)  → less-trans {A = A} x<y y<z
        (equal refl) → x<y

    leq/lt-trans : ∀ {x y z : A} → x ≤ y → y < z → x < z
    leq/lt-trans x≤y y<z =
      case leq-to-lteq {A = A} x≤y of λ where
        (less  x<y)  → less-trans {A = A} x<y y<z
        (equal refl) → y<z

  data _≲_ (x y : A) : Set a where
    strict    : x < y → x ≲ y
    nonstrict : x ≤ y → x ≲ y

  module _ {x y : A} where
    OrdProof : x ≲ y → Set a
    OrdProof (strict    _) = x < y
    OrdProof (nonstrict _) = x ≤ y

    infix -1 ordProof_
    ordProof_ : (p : x ≲ y) → OrdProof p
    ordProof strict    p = p
    ordProof nonstrict p = p

  infixr 0 eqOrdStep ltOrdStep leqOrdStep
  infix  1 _∎Ord

  syntax eqOrdStep x q p = x ≡[ p ] q
  eqOrdStep : ∀ (x : A) {y z} → y ≲ z → x ≡ y → x ≲ z
  x ≡[ x=y ] strict    y<z = strict    (case x=y of λ where refl → y<z)
  x ≡[ x=y ] nonstrict y≤z = nonstrict (case x=y of λ where refl → y≤z)
    -- ^ Note: don't match on the proof here, we need to decide strict vs nonstrict for neutral proofs

  syntax eqOrdStepʳ x q p = x ≡[ p ]ʳ q
  eqOrdStepʳ : ∀ (x : A) {y z} → y ≲ z → y ≡ x → x ≲ z
  x ≡[ y=x ]ʳ strict    y<z = strict    (case y=x of λ where refl → y<z)
  x ≡[ y=x ]ʳ nonstrict y≤z = nonstrict (case y=x of λ where refl → y≤z)

  syntax ltOrdStep x q p = x <[ p ] q
  ltOrdStep : ∀ (x : A) {y z} → y ≲ z → x < y → x ≲ z
  x <[ x<y ] strict    y<z = strict (less-trans {A = A} x<y y<z)
  x <[ x<y ] nonstrict y≤z = strict (lt/leq-trans x<y y≤z)

  syntax leqOrdStep x q p = x ≤[ p ] q
  leqOrdStep : ∀ (x : A) {y z} → y ≲ z → x ≤ y → x ≲ z
  x ≤[ x≤y ] strict    y<z = strict    (leq/lt-trans x≤y y<z)
  x ≤[ x≤y ] nonstrict y≤z = nonstrict (leq-trans {A = A} x≤y y≤z)

  _∎Ord : ∀ (x : A) → x ≲ x
  x ∎Ord = nonstrict (eq-to-leq {A = A} refl)
