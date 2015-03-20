
module Tactic.Nat.Induction where

open import Prelude
open import Tactic.Nat.Auto
open import Tactic.Nat.Simpl
open import Tactic.Nat.Reflect
open import Builtin.Reflection
open import Tactic.Reflection.Quote

nat-induction : (P : Nat → Set) → P 0 → (∀ n → P n → P (suc n)) → ∀ n → P n
nat-induction P base step  zero   = base
nat-induction P base step (suc n) = step n (nat-induction P base step n)

`tactic : Name → Term
`tactic x = quote-goal $ abs "g" $ unquote-term $ def x (vArg quote-context ∷ vArg (var 0 []) ∷ [])

induction-goal-must-be-a-function-type : ⊤
induction-goal-must-be-a-function-type = _

induction : List (Arg Type) → Term → Term
induction Γ (pi a b) =
  let P = lam visible (unEl <$> b)
  in def (quote nat-induction)
         ( vArg P
         ∷ vArg (`tactic (quote auto))
         ∷ vArg (lam visible $ abs "_" $ `tactic (quote assumed))
         ∷ [])
induction _ t =
  def (quote getProof)
    $ vArg (con (quote nothing) [])
    ∷ vArg (def (quote induction-goal-must-be-a-function-type) [])
    ∷ []
