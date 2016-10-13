
module Tactic.Nat.Auto where

open import Prelude
open import Builtin.Reflection
open import Tactic.Reflection.Quote
open import Tactic.Reflection

open import Tactic.Nat.NF
open import Tactic.Nat.Exp
open import Tactic.Nat.Reflect
open import Tactic.Nat.Auto.Lemmas

open Tactic.Nat.Reflect public using (cantProve; invalidGoal)

module _ {Atom : Set} {{_ : Eq Atom}} {{_ : Ord Atom}} where
  liftNFEq : ∀ (e₁ : Exp Atom) e₂ ρ → ⟦ norm e₁ ⟧n ρ ≡ ⟦ norm e₂ ⟧n ρ → ⟦ e₁ ⟧e ρ ≡ ⟦ e₂ ⟧e ρ
  liftNFEq e₁ e₂ ρ H = eraseEquality $
    ⟦ e₁      ⟧e ρ ≡⟨ sound e₁ ρ ⟩
    ⟦ norm e₁ ⟧n ρ ≡⟨ H ⟩
    ⟦ norm e₂ ⟧n ρ ≡⟨ sound e₂ ρ ⟩ʳ
    ⟦ e₂      ⟧e ρ ∎

  unliftNFEq : ∀ (e₁ : Exp Atom) e₂ ρ → ⟦ e₁ ⟧e ρ ≡ ⟦ e₂ ⟧e ρ → ⟦ norm e₁ ⟧n ρ ≡ ⟦ norm e₂ ⟧n ρ
  unliftNFEq e₁ e₂ ρ H =
    ⟦ norm e₁ ⟧n ρ ≡⟨ sound e₁ ρ ⟩ʳ
    ⟦ e₁      ⟧e ρ ≡⟨ H ⟩
    ⟦ e₂      ⟧e ρ ≡⟨ sound e₂ ρ ⟩
    ⟦ norm e₂ ⟧n ρ ∎

  auto-proof : ∀ e₁ e₂ → norm e₁ ≡ norm e₂ → ∀ ρ → ⟦ e₁ ⟧e ρ ≡ ⟦ e₂ ⟧e ρ
  auto-proof e₁ e₂ nfeq ρ = liftNFEq e₁ e₂ ρ (cong (λ n → ⟦ n ⟧n ρ) nfeq)

auto-tactic : Type → Tactic
auto-tactic t hole =
  caseM termToEq t of λ where
   nothing → unify hole $ failedProof (quote invalidGoal) t
   (just ((e₁ , e₂) , Γ)) →
     do prf ← newMeta!
     -| unify hole (def₄ (quote auto-proof) (` e₁) (` e₂) prf (quotedEnv Γ))
     ~| unify prf (con₀ (quote refl)) <|>
          (caseM normalise =<< inferType prf of λ where
             (def (quote _≡_) (_ ∷ _ ∷ vArg lnf ∷ vArg rnf ∷ [])) →
                typeError $ strErr "Normal forms are not equal:" ∷ termErr lnf ∷ strErr "≠" ∷ termErr rnf
                          ∷ []
             sgoal → typeError $ strErr "Huh? This is a weird equality goal:" ∷ termErr sgoal ∷ [])

macro
  auto : Tactic
  auto = on-goal auto-tactic
