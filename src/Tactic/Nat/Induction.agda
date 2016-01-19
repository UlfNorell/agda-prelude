
module Tactic.Nat.Induction where

open import Prelude
open import Tactic.Nat.Subtract
open import Tactic.Nat.Reflect
open import Builtin.Reflection
open import Tactic.Reflection.Quote
open import Tactic.Reflection.DeBruijn
open import Tactic.Reflection.Substitute
open import Tactic.Reflection

nat-induction : (P : Nat → Set) → P 0 → (∀ n → P n → P (suc n)) → ∀ n → P n
nat-induction P base step  zero   = base
nat-induction P base step (suc n) = step n (nat-induction P base step n)

induction-goal-must-be-a-function-type : ⊤
induction-goal-must-be-a-function-type = _

-- induction-tactic : Term → Term
-- induction-tactic (pi a b) =
--   let P = lam visible (unEl <$> b)
--   in def (quote nat-induction)
--          ( vArg P
--          ∷ vArg (on-goal (quote autosub-tactic))
--          ∷ vArg (lam visible $ abs "_" $ lam visible $ abs "ih" $
--                 on-type-of-term (quote by-tactic) (var 0 []))
--          ∷ [])
-- induction-tactic t = failedProof (quote induction-goal-must-be-a-function-type) t

-- TODO: in library
private
  newMeta! : TC Term
  newMeta! = newMeta (el unknown unknown)

  vlam : Term → Term
  vlam b = lam visible (abs "_" b)

macro
  induction : Tactic
  induction hole =
    caseM unEl <$> inferType hole of λ
    { (pi a b)   →
        let P = lam visible (unEl <$> b)
            inStepCxt : {A : Set} → TC A → TC A
            inStepCxt {_} = extendContext (vArg (el unknown (quoteTerm Nat))) ∘
                            extendContext (vArg (el unknown unknown)) in
        do base ← newMeta!
        -| step ← inStepCxt newMeta!
        -| unify hole (def (quote nat-induction)
                           (vArg P ∷ vArg base ∷ vArg (vlam $ vlam step) ∷ []))
        ~| unify base =<< autosub-tactic =<< inferType base
        ~| inStepCxt (unify step =<< by-tactic (var 0 []) =<< inferType step)
    ; (meta x _) → blockOnMeta x
    ; _          → typeErrorS "Induction tactic must be applied to a function goal"
    }
