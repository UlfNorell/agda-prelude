
module Tactic.Nat.Induction where

open import Prelude
open import Tactic.Nat.Auto
open import Tactic.Nat.Simpl
open import Tactic.Nat.Reflect
open import Builtin.Reflection
open import Tactic.Reflection.Quote
open import Tactic.Reflection

nat-induction : (P : Nat → Set) → P 0 → (∀ n → P n → P (suc n)) → ∀ n → P n
nat-induction P base step  zero   = base
nat-induction P base step (suc n) = step n (nat-induction P base step n)

induction-goal-must-be-a-function-type : ⊤
induction-goal-must-be-a-function-type = _

induction-tactic : Term → Term
induction-tactic (pi a b) =
  let P = lam visible (unEl <$> b)
  in def (quote nat-induction)
         ( vArg P
         ∷ vArg (on-goal (quote auto-tactic))
         ∷ vArg (lam visible $ abs "_" $ on-goal (quote assumed-tactic))
         ∷ [])
induction-tactic t =
  def (quote getProof)
    $ vArg (con (quote nothing) [])
    ∷ vArg (def (quote induction-goal-must-be-a-function-type) [])
    ∷ []

macro
  induction : Term
  induction = on-goal (quote induction-tactic)
