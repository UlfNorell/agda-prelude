
-- Fast exponentiation

module Numeric.Nat.Pow where

open import Prelude
open import Numeric.Nat.DivMod
open import Control.WellFounded
open import Tactic.Nat
open import Tactic.Cong

module _ {a} {A : Set a} {{_ : Semiring A}} where
  private
    expAcc : A → (n : Nat) → Acc _<_ n → A
    expAcc a  zero    wf = one
    expAcc a (suc n) (acc wf) with n divmod 2
    ... | qr q 0 _ eq = force (a * a) λ a² → expAcc a² q (wf q (by eq)) * a
    ... | qr q 1 _ eq = force (a * a) λ a² → expAcc a² (suc q) (wf (suc q) (by eq))
    ... | qr q (suc (suc _)) lt _ = refute lt

  infixr 8 _^′_
  _^′_ : A → Nat → A
  a ^′ n = expAcc a n (wfNat n)

  module _ (assoc : (a b c : A) → a * (b * c) ≡ (a * b) * c)
           (idr   : (a : A) → a * one ≡ a)
           (idl   : (a : A) → one * a ≡ a) where

    private
      force-eq : ∀ {a b} {A : Set a} {B : A → Set b} (x : A) {f : ∀ x → B x} {y : B x} →
                   f x ≡ y → force x f ≡ y
      force-eq x eq = forceLemma x _ ⟨≡⟩ eq

      on-assoc-l : {a b c a₁ b₁ c₁ : A} → (a * b) * c ≡ (a₁ * b₁) * c₁ → a * (b * c) ≡ a₁ * (b₁ * c₁)
      on-assoc-l eq = assoc _ _ _ ⟨≡⟩ eq ⟨≡⟩ʳ assoc _ _ _

      on-assoc-r : {a b c a₁ b₁ c₁ : A} → a * (b * c) ≡ a₁ * (b₁ * c₁) → (a * b) * c ≡ (a₁ * b₁) * c₁
      on-assoc-r eq = assoc _ _ _ ʳ⟨≡⟩ eq ⟨≡⟩ assoc _ _ _

      lem-pow-mul-l : (a : A) (n : Nat) → a * a ^ n ≡ a ^ n * a
      lem-pow-mul-l a zero    = idr _ ⟨≡⟩ʳ idl _
      lem-pow-mul-l a (suc n) = assoc _ _ _ ⟨≡⟩ (_* a) $≡ lem-pow-mul-l a n

      lem-pow-mul-distr : (a : A) (n : Nat) → (a * a) ^ n ≡ a ^ n * a ^ n
      lem-pow-mul-distr a  zero   = sym (idl _)
      lem-pow-mul-distr a (suc n) =
        (_* (a * a)) $≡ lem-pow-mul-distr a n ⟨≡⟩ʳ
        on-assoc-r (((a ^ n) *_) $≡ (on-assoc-l ((_* a) $≡ lem-pow-mul-l a n)))

      lem-pow-add-distr : (a : A) (n m : Nat) → a ^ (n + m) ≡ a ^ n * a ^ m
      lem-pow-add-distr a  zero   m = sym (idl _)
      lem-pow-add-distr a (suc n) m =
        (_* a) $≡ lem-pow-add-distr a n m ⟨≡⟩ʳ
        on-assoc-r (((a ^ n) *_) $≡ lem-pow-mul-l a m)

      lem : ∀ a n (wf : Acc _<_ n) → expAcc a n wf ≡ a ^ n
      lem a  zero   wf = refl
      lem a (suc n) (acc wf) with n divmod 2
      lem a (suc ._) (acc wf) | qr q 0 _ refl =
        force-eq (a * a) (cong (_* a) (
          lem (a * a) q (wf q (diff _ auto)) ⟨≡⟩
          lem-pow-mul-distr a q ⟨≡⟩
          lem-pow-add-distr a q q ʳ⟨≡⟩
          cong (_^_ a) {x = q + q} {y = q * 2 + 0} auto))
      lem a (suc ._) (acc wf) | qr q 1 _ refl =
        force-eq (a * a) $
          lem (a * a) (suc q) (wf (suc q) (diff _ auto)) ⟨≡⟩
          (a * a) ^ q * (a * a)
            ≡⟨ by-cong (lem-pow-mul-distr a q ⟨≡⟩ʳ lem-pow-add-distr a q q) ⟩
          a ^ (q + q) * (a * a)
            ≡⟨ by-cong {x = q + q} {y = q * 2} auto ⟩
          a ^ (q * 2) * (a * a)
            ≡⟨ by-cong (idl a) ⟩
          a ^ (q * 2) * (a ^ 1 * a)
            ≡⟨ assoc _ _ _ ⟩
          a ^ (q * 2) * a ^ 1 * a
            ≡⟨ by-cong (lem-pow-add-distr a (q * 2) 1) ⟩
          a ^ (q * 2 + 1) * a ∎
      ... | qr _ (suc (suc _)) lt _ = refute lt

    lem-^′-sound : ∀ a n → a ^′ n ≡ a ^ n
    lem-^′-sound a n = lem a n (wfNat n)

  {-# DISPLAY expAcc a n _ = a ^′ n #-}
