-- Tactic for proving coprimality.
-- Finds Coprime hypotheses in the context.
module Tactic.Nat.Coprime where

import Agda.Builtin.Nat as Builtin

open import Prelude
open import Control.Monad.Zero
open import Control.Monad.State
open import Container.List
open import Container.Traversable
open import Numeric.Nat
open import Tactic.Reflection
open import Tactic.Reflection.Parse
open import Tactic.Reflection.Quote

open import Tactic.Nat.Coprime.Problem
open import Tactic.Nat.Coprime.Decide
open import Tactic.Nat.Coprime.Reflect

private
  Proof : Problem → Env → Set
  Proof Q ρ with canProve Q
  ... | true  = ⟦ Q ⟧p ρ
  ... | false = ⊤

  erasePrf : ∀ Q {ρ} → ⟦ Q ⟧p ρ → ⟦ Q ⟧p ρ
  erasePrf ([] ⊨ a ⋈ b) Ξ = eraseEquality Ξ
  erasePrf (ψ ∷ Γ ⊨ φ) Ξ = λ H → erasePrf (Γ ⊨ φ) (Ξ H)

  proof : ∀ Q ρ → Proof Q ρ
  proof Q ρ with canProve Q | sound Q
  ... | true  | prf = erasePrf Q (prf refl ρ)
  ... | false | _   = _

  -- For the error message

  unquoteE : List Term → Exp → Term
  unquoteE ρ (atom x) = fromMaybe (lit (nat 0)) (index ρ x)
  unquoteE ρ (e ⊗ e₁) = def₂ (quote _*_) (unquoteE ρ e) (unquoteE ρ e₁)

  unquoteF : List Term → Formula → Term
  unquoteF ρ (a ⋈ b) = def₂ (quote Coprime) (unquoteE ρ a) (unquoteE ρ b)

macro
  auto-coprime : Tactic
  auto-coprime ?hole = withNormalisation true $ do
    goal ← inferType ?hole
    ensureNoMetas goal
    cxt  ← reverse <$> getContext
    (_ , Hyps , Q) , ρ ← runParse (parseProblem (map unArg cxt) goal)
    unify ?hole (def (quote proof) $ map vArg (` Q ∷ quotedEnv ρ ∷ Hyps))
      <|> do
        case Q of λ where
          (Γ ⊨ φ) → typeErrorFmt "Cannot prove %t from %e"
                                 (unquoteF ρ φ)
                                 (punctuate (strErr "and") (map (termErr ∘ unquoteF ρ) Γ))
