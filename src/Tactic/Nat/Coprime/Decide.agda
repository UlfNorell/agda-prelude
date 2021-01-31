module Tactic.Nat.Coprime.Decide where

open import Prelude
open import Prelude.Equality.Unsafe
open import Prelude.List.Relations.Any
open import Prelude.List.Relations.All
open import Prelude.List.Relations.Properties

open import Numeric.Nat
open import Tactic.Nat.Coprime.Problem

private
  infix 4 _isIn_
  _isIn_ : Nat → Exp → Bool
  x isIn atom y = isYes (x == y)
  x isIn a ⊗ b = x isIn a || x isIn b

  proves : Nat → Nat → Formula → Bool
  proves x y (a ⋈ b) = x isIn a && y isIn b || x isIn b && y isIn a

  hypothesis : Nat → Nat → List Formula → Bool
  hypothesis x y Γ = any? (proves x y) Γ

  canProve' : List Formula → Exp → Exp → Bool
  canProve' Γ (atom x) (atom y) = hypothesis x y Γ
  canProve' Γ a (b ⊗ c) = canProve' Γ a b && canProve' Γ a c
  canProve' Γ (a ⊗ b) c = canProve' Γ a c && canProve' Γ b c

canProve : Problem → Bool
canProve (Γ ⊨ a ⋈ b) = canProve' Γ a b

-- Soundness proof --

private
  invert-&&₁ : ∀ {a b} → (a && b) ≡ true → a ≡ true
  invert-&&₁ {false} ()
  invert-&&₁ {true}  prf = refl

  invert-&&₂ : ∀ {a b} → (a && b) ≡ true → b ≡ true
  invert-&&₂ {false} ()
  invert-&&₂ {true} prf = prf

  invert-|| : ∀ a {b} → (a || b) ≡ true → Either (a ≡ true) (b ≡ true)
  invert-|| false prf = right prf
  invert-|| true  prf = left prf

  sound-eq : (a b : Nat) → isYes (a == b) ≡ true → a ≡ b
  sound-eq a b ok with a == b
  sound-eq a b ok | yes a=b = a=b
  sound-eq a b () | no _

  sound-any : ∀ {A : Set} (p : A → Bool) xs → any? p xs ≡ true → Any (λ x → p x ≡ true) xs
  sound-any p [] ()
  sound-any p (x ∷ xs) ok with p x | graphAt p x
  ... | false | _          = suc (sound-any p xs ok)
  ... | true  | ingraph eq = zero eq

private
  syntax WithHyps Γ (λ ρ → A) = ρ ∈ Γ ⇒ A
  WithHyps : List Formula → (Env → Set) → Set
  WithHyps Γ F = ∀ ρ → All (⟦_⟧f ρ) Γ → F ρ

  sound-isIn' : ∀ x y a b → (x isIn a) ≡ true → (y isIn b) ≡ true → ∀ ρ → ⟦ a ⋈ b ⟧f ρ → Coprime (ρ x) (ρ y)

  sound-isIn-⊗-l : ∀ x y a b c → (x isIn a) ≡ true → (y isIn b ⊗ c) ≡ true →
                                 ∀ ρ → ⟦ a ⋈ b ⊗ c ⟧f ρ → Coprime (ρ x) (ρ y)
  sound-isIn-⊗-l x y a b c oka okbc ρ H =
    case invert-|| (y isIn b) okbc of λ where
      (left okb)  → sound-isIn' x y a b oka okb ρ (mul-coprime-l (⟦ a ⟧e ρ) (⟦ b ⟧e ρ) (⟦ c ⟧e ρ) H)
      (right okc) → sound-isIn' x y a c oka okc ρ (mul-coprime-r (⟦ a ⟧e ρ) (⟦ b ⟧e ρ) (⟦ c ⟧e ρ) H)

  sound-isIn' x y (atom x') (atom y') oka okb ρ H =
    case₂ sound-eq x x' oka , sound-eq y y' okb of λ where
      refl refl → H
  sound-isIn' x y a@(atom _) (b ⊗ c) oka okbc ρ H = sound-isIn-⊗-l x y a b c oka okbc ρ H
  sound-isIn' x y a@(_ ⊗ _) (b ⊗ c) oka okbc ρ H = sound-isIn-⊗-l x y a b c oka okbc ρ H
  sound-isIn' x y (a ⊗ b) c@(atom _) okab okc ρ H =
    let nf = λ e → ⟦ e ⟧e ρ
        H' = coprime-sym _ (nf c) H
    in
    case invert-|| (x isIn a) okab of λ where
      (left  oka) → sound-isIn' x y a c oka okc ρ
                      (coprime-sym (nf c) _
                        (mul-coprime-l (nf c) (nf a) (nf b) H'))
      (right okb) → sound-isIn' x y b c okb okc ρ
                      (coprime-sym (nf c) _
                        (mul-coprime-r (nf c) (nf a) _ H'))

  sound-isIn : ∀ x y a b → (x isIn a && y isIn b) ≡ true → ∀ ρ → ⟦ a ⋈ b ⟧f ρ → Coprime (ρ x) (ρ y)
  sound-isIn x y a b ok = sound-isIn' x y a b (invert-&&₁ ok) (invert-&&₂ ok)

  sound-proves : ∀ x y φ → proves x y φ ≡ true → ∀ ρ → ⟦ φ ⟧f ρ → Coprime (ρ x) (ρ y)
  sound-proves x y (a ⋈ b) ok ρ H =
    case invert-|| (x isIn a && y isIn b) ok of λ where
      (left  ok) → sound-isIn x y a b ok ρ H
      (right ok) → sound-isIn x y b a ok ρ (coprime-sym (⟦ a ⟧e ρ) _ H)

  sound-hyp : ∀ x y Γ → hypothesis x y Γ ≡ true → ρ ∈ Γ ⇒ Coprime (ρ x) (ρ y)
  sound-hyp x y Γ ok ρ Ξ =
    case lookupAny Ξ (sound-any (proves x y) Γ ok) of λ where
      (φ , H , okφ) → sound-proves x y φ okφ ρ H

  sound' : ∀ Γ a b → canProve' Γ a b ≡ true → ρ ∈ Γ ⇒ ⟦ a ⋈ b ⟧f ρ

  sound-⊗-r : ∀ Γ a b c → (canProve' Γ a b && canProve' Γ a c) ≡ true → ρ ∈ Γ ⇒ ⟦ a ⋈ b ⊗ c ⟧f ρ
  sound-⊗-r Γ a b c ok ρ Ξ =
    let a⋈b : ⟦ a ⋈ b ⟧f ρ
        a⋈b = sound' Γ a b (invert-&&₁ ok) ρ Ξ
        a⋈c : ⟦ a ⋈ c ⟧f ρ
        a⋈c = sound' Γ a c (invert-&&₂ ok) ρ Ξ
    in coprime-mul-r (⟦ a ⟧e ρ) _ _ a⋈b a⋈c

  sound' Γ (atom x) (atom y) ok ρ Ξ = sound-hyp x y Γ ok ρ Ξ
  sound' Γ a@(atom _) (b ⊗ c) ok ρ Ξ = sound-⊗-r Γ a b c ok ρ Ξ
  sound' Γ a@(_ ⊗ _) (b ⊗ c) ok ρ Ξ = sound-⊗-r Γ a b c ok ρ Ξ
  sound' Γ (a ⊗ b) c@(atom _) ok ρ Ξ =
    let a⋈c : ⟦ a ⋈ c ⟧f ρ
        a⋈c = sound' Γ a c (invert-&&₁ ok) ρ Ξ
        b⋈c : ⟦ b ⋈ c ⟧f ρ
        b⋈c = sound' Γ b c (invert-&&₂ ok) ρ Ξ
    in coprime-mul-l (⟦ a ⟧e ρ) _ _ a⋈c b⋈c

sound : ∀ Q → canProve Q ≡ true → ∀ ρ → ⟦ Q ⟧p ρ
sound Q@(Γ ⊨ a ⋈ b) ok ρ = curryProblem Q ρ (sound' Γ a b ok ρ)
