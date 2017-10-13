
open import Agda.Builtin.Reflection using (Name)

-- See Tactic.Nat for a description of the various tactics.

module Tactic.Nat.Generic (`≤ `toLeq `fromLeq : Name) where

open import Prelude
open import Tactic.Reflection
open import Tactic.Nat.Induction using (nat-induction)
open import Tactic.Nat.Subtract using (autosub-tactic; by-tactic; refutesub-tactic; simplifygoal-tactic; simplifysub-tactic)

private
  a→0 : Type → Term
  a→0 (def op _) = ifYes op == `≤ then def₀ `toLeq else def₀ (quote id)
  a→0 _ = def₀ (quote id) -- TODO perhaps return unknown?

  0→a : Type → Term
  0→a (def op _) = ifYes op == `≤ then def₀ `fromLeq else def₀ (quote id)
  0→a _ = def₀ (quote id) -- TODO perhaps return unknown?

  applyTactic : (Type → TC Term) → Term → TC ⊤
  applyTactic tac hole = do
    goal ← inferType hole
    unify hole ∘ (0→a goal `$_) =<< tac =<< inferNormalisedType (a→0 goal `$ hole)

macro
  auto : Tactic
  auto hole = applyTactic autosub-tactic hole

  by : Term → Tactic
  by prf hole = do
    Prf ← inferNormalisedType prf
    applyTactic (by-tactic (a→0 Prf `$ prf)) hole

  refute : Term → Tactic
  refute prf hole = do
    Prf ← inferNormalisedType prf
    unify hole =<< refutesub-tactic (a→0 Prf `$ prf)

  simplify-goal : Tactic
  simplify-goal hole = do
    goal    ← inferFunRange hole
    s-goal₀ ← simplifygoal-tactic =<< inferFunRange (a→0 goal `∘ hole)
    hole =′ 0→a goal `∘ s-goal₀ `∘ a→0 goal

  simplify : Term → Tactic
  simplify prf hole = do
    goal    ← inferFunRange hole
    Prf     ← inferNormalisedType prf
    s-goal₀ ← simplifysub-tactic (a→0 Prf `$ prf) =<< inferFunRange (a→0 goal `∘ hole)
    hole =′ (`λ $ 0→a goal `$ weaken 1 s-goal₀ `$ `λ $ a→0 goal `$ var₁ 1 (0→a Prf `$ var₀ 0))

  induction : Tactic
  induction hole = do
    pi _ (abs _ goal) ← inferNormalisedType hole
      where meta x _ → blockOnMeta x
            _        → typeErrorS "Induction tactic must be applied to a function goal"
    hole₀ ← (a→0 goal `∘ hole) :′ unknown
    pi a b ← inferNormalisedType hole₀
      where meta x _ → blockOnMeta x
            _        → typeErrorS "Induction tactic must be applied to a function goal"
    let P = lam visible b
        inStepCxt : {A : Set} → TC A → TC A
        inStepCxt {_} = λ′ (vArg (quoteTerm Nat)) ∘
                        λ′ (vArg unknown)
    base ← unknown :′ unknown
    step ← inStepCxt $ unknown :′ unknown
    hole =′ 0→a goal `∘ def₃ (quote nat-induction)
                             P base (`λ $ `λ step)
    unify base =<< autosub-tactic =<< inferNormalisedType base
    inStepCxt (unify step =<< by-tactic (var₀ 0) =<< inferNormalisedType step)
