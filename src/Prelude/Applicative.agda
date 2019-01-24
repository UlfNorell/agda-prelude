
module Prelude.Applicative where

open import Agda.Primitive
open import Prelude.Unit
open import Prelude.Functor
open import Prelude.Function
open import Prelude.Equality
open import Prelude.Number
open import Prelude.Semiring
open import Prelude.Fractional

open import Prelude.Applicative.Indexed {I = ⊤} as Indexed

Applicative : ∀ {a b} (F : Set a → Set b) → Set (lsuc a ⊔ b)
Applicative F = Indexed.IApplicative (λ _ _ → F)

Applicative′ : ∀ {a b} (F : ∀ {a} → Set a → Set a) → Set (lsuc (a ⊔ b))
Applicative′ {a} {b} F = Indexed.IApplicative′ {a = a} {b = b} (λ _ _ → F)

open Indexed public hiding (IApplicative; IApplicative′)

fmapApplicative : ∀ {a b} {F : Set a → Set b} →
                    (∀ {A} → A → F A) → (∀ {A B} → F (A → B) → F A → F B) →
                    ∀ {A B} → (A → B) → F A → F B
fmapApplicative pure _<*>_ f m = pure f <*> m

module _ {a b} {F : Set a → Set b} {{AppF : Applicative F}} where

  defaultApplicativeNumber : {A : Set a} {{NumA : Number A}} -- levels get in the way of having constraints
                             {{_ : NoNumConstraint NumA}} →
                             Number (F A)
  Number.Constraint defaultApplicativeNumber n = ⊤′
  fromNat {{defaultApplicativeNumber}} n = pure (fromNat n)

  defaultApplicativeNegative : {A : Set a} {{NegA : Negative A}} -- levels get in the way of having constraints
                             {{_ : NoNegConstraint NegA}} →
                             Negative (F A)
  Negative.Constraint defaultApplicativeNegative _ = ⊤′
  fromNeg {{defaultApplicativeNegative}} n = pure (fromNeg n)

  defaultApplicativeSemiring : {A : Set a} {{_ : Semiring A}} → Semiring (F A)
  zro {{defaultApplicativeSemiring}} = pure zro
  one {{defaultApplicativeSemiring}} = pure one
  _+_ {{defaultApplicativeSemiring}} x y = _+_ <$> x <*> y
  _*_ {{defaultApplicativeSemiring}} x y = _*_ <$> x <*> y

  defaultApplicativeSubtractive : {A : Set a} {{_ : Subtractive A}} → Subtractive (F A)
  _-_    {{defaultApplicativeSubtractive}} x y = _-_ <$> x <*> y
  negate {{defaultApplicativeSubtractive}} x   = negate <$> x

  defaultApplicativeFractional : {A : Set a} {{FracA : Fractional A}}  -- only if no constraints
                                 {{_ : Fractional.NoConstraint FracA}} →
                                 Fractional (F A)
  Fractional.Constraint defaultApplicativeFractional _ _ = ⊤′
  Fractional._/_ defaultApplicativeFractional x y = (λ x y → x / y) <$> x <*> y

-- Congruence for _<*>_ and friends

module _ {a b} {A B : Set a} {F : Set a → Set b} {{_ : Applicative F}} where

  infixl 4 _=*=_
  _=*=_ : {f g : F (A → B)} {x y : F A} → f ≡ g → x ≡ y → (f <*> x) ≡ (g <*> y)
  refl =*= refl = refl

  _=*_ : {a₁ a₂ : F A} {b₁ b₂ : F B} → a₁ ≡ a₂ → b₁ ≡ b₂ → (a₁ <* b₁) ≡ (a₂ <* b₂)
  refl =* refl = refl

  _*=_ : {a₁ a₂ : F A} {b₁ b₂ : F B} → a₁ ≡ a₂ → b₁ ≡ b₂ → (a₁ *> b₁) ≡ (a₂ *> b₂)
  refl *= refl = refl

module _ {F  : ∀ {a}   → Set a → Set a}
         {{_ : ∀ {a b} → Applicative′ {a} {b} F}}
         {{_ : ∀ {a}   → Applicative {a} F}}
         {a b} {A : Set a} {B : Set b} where

  infixl 4 _=*=′_
  _=*=′_ : {f g : F (A → B)} {x y : F A} → f ≡ g → x ≡ y → (f <*>′ x) ≡ (g <*>′ y)
  refl =*=′ refl = refl

  _=*′_ : {a₁ a₂ : F A} {b₁ b₂ : F B} → a₁ ≡ a₂ → b₁ ≡ b₂ → (a₁ <*′ b₁) ≡ (a₂ <*′ b₂)
  refl =*′ refl = refl

  _*=′_ : {a₁ a₂ : F A} {b₁ b₂ : F B} → a₁ ≡ a₂ → b₁ ≡ b₂ → (a₁ *>′ b₁) ≡ (a₂ *>′ b₂)
  refl *=′ refl = refl
