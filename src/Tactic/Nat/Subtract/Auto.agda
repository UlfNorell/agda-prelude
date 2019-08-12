
module Tactic.Nat.Subtract.Auto where

open import Prelude
open import Prelude.Variables
open import Builtin.Reflection
open import Tactic.Reflection.Quote
open import Tactic.Reflection.Meta

open import Tactic.Nat.Reflect
open import Tactic.Nat.NF
open import Tactic.Nat.Auto
open import Tactic.Nat.Simpl.Lemmas
open import Tactic.Nat.Subtract.Exp
open import Tactic.Nat.Subtract.Reflect
open import Tactic.Nat.Subtract.Lemmas
open import Tactic.Nat.Less.Lemmas

autosub-proof : ∀ eqn ρ → Maybe (⟦ eqn ⟧eqn ρ)
autosub-proof (e₁ :≡ e₂) ρ with normSub e₁ == normSub e₂
autosub-proof (e₁ :≡ e₂) ρ | no _   = nothing
autosub-proof (e₁ :≡ e₂) ρ | yes eq = just (liftNFSubEq e₁ e₂ ρ (cong (λ n → ⟦ n ⟧sn ρ) eq))
autosub-proof (e₁ :< e₂) ρ with cancel (normSub e₁) (normSub e₂) | simplifySubLess e₁ e₂ ρ
autosub-proof (e₁ :< e₂) ρ | [] , (suc n , []) ∷ nf | simp =
  let sk : SubNF
      sk = (suc n , []) ∷ nf
      k  = (    n , []) ∷ nf in
  just $ simp $ LessNat.diff (⟦ k ⟧sns ρ) $
    ns-sound sk (atomEnvS ρ) ⟨≡⟩
    auto ⟨≡⟩ʳ (λ z → suc (z + 0)) $≡ lem-eval-sns-nS k ρ
autosub-proof (e₁ :< e₂) ρ | _  , _ | simp = nothing

autosub-tactic : Type → TC Term
autosub-tactic t = do
  ensureNoMetas t
  just (eqn , Γ) ← termToSubEqn t
    where nothing → typeError $ strErr "Invalid goal:" ∷ termErr t ∷ []
  pure $
    getProof (quote cantProve) t $
      def (quote autosub-proof)
          ( vArg (` eqn)
          ∷ vArg (quotedEnv Γ)
          ∷ [] )
