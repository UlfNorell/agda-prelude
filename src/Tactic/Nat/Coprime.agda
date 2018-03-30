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

record CantProve (Q : Problem) : Set where

private
  Proof : Problem → Env → Set
  Proof Q ρ with canProve Q
  ... | true  = ⟦ Q ⟧p ρ
  ... | false = CantProve Q

  erasePrf : ∀ Q {ρ} → ⟦ Q ⟧p ρ → ⟦ Q ⟧p ρ
  erasePrf ([] ⊨ a ⋈ b) Ξ = eraseEquality Ξ
  erasePrf (ψ ∷ Γ ⊨ φ) Ξ = λ H → erasePrf (Γ ⊨ φ) (Ξ H)

  proof : ∀ Q ρ → Proof Q ρ
  proof Q ρ with canProve Q | sound Q
  ... | true  | prf = erasePrf Q (prf refl ρ)
  ... | false | _   = _

macro
  auto-coprime : Tactic
  auto-coprime ?hole = withNormalisation true $ do
    goal ← inferType ?hole
    cxt  ← reverse <$> getContext
    (_ , Hyps , Q) , Γ ← runParse (parseProblem (map unArg cxt) goal)
    unify ?hole $ def (quote proof) $ map vArg (` Q ∷ quotedEnv Γ ∷ Hyps)
