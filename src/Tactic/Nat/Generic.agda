open import Agda.Builtin.Reflection using (Name)
module Tactic.Nat.Generic (`_≤ₐ_ `≤ₐ→≤₀ `≤₀→≤ₐ : Name) where

-- See Tactic.Nat for a description of the various tactics.

open import Prelude
open import Tactic.Reflection
open import Tactic.Nat.Induction using (nat-induction)
open import Tactic.Nat.Subtract using (autosub-tactic; by-tactic; refutesub-tactic; simplifygoal-tactic; simplifysub-tactic)

private
  a→0 : Type → Term
  a→0 (def operator _) = ifYes operator == `_≤ₐ_ then def₀ `≤ₐ→≤₀ else def₀ (quote id)
  a→0 _ = def₀ (quote id) -- TODO perhaps return unknown?

  0→a : Type → Term
  0→a (def operator _) = ifYes operator == `_≤ₐ_ then def₀ `≤₀→≤ₐ else def₀ (quote id)
  0→a _ = def₀ (quote id) -- TODO perhaps return unknown?

macro
  auto : Tactic
  auto holeₐ = do
    goalₐ ← inferType holeₐ -|
    hole₀ := a→0 goalₐ `$ holeₐ -|
    (holeₐ =′_) ∘ (0→a goalₐ `$_) =<< autosub-tactic =<< inferType =<< normalise hole₀

  by : Term → Tactic
  by prfₐ holeₐ = do
    goalₐ ← inferType holeₐ -|
    hole₀ := a→0 goalₐ `$ holeₐ -|
    Prfₐ ← inferType prfₐ -|
    prf₀ := a→0 Prfₐ `$ prfₐ -|
    (holeₐ =′_) ∘ (0→a goalₐ `$_) =<< by-tactic prf₀ =<< inferType =<< normalise hole₀

  refute : Term → Tactic
  refute prfₐ holeₐ = do
    Prfₐ ← inferType prfₐ -|
    prf₀ := a→0 Prfₐ `$ prfₐ -|
    (holeₐ =′_) =<< refutesub-tactic prf₀

  simplify-goal : Tactic
  simplify-goal holeₐ = do
    goalₐ ← inferFunRange holeₐ -|
    s-goal₀ ← simplifygoal-tactic =<< inferFunRange (a→0 goalₐ `∘ holeₐ) -|
    holeₐ =′ 0→a goalₐ `∘ s-goal₀ `∘ a→0 goalₐ

  simplify : Term → Tactic
  simplify prfₐ holeₐ =
    goalₐ ← inferFunRange holeₐ -|
    Prfₐ ← inferType prfₐ -|
    prf₀ := a→0 Prfₐ `$ prfₐ -|
    s-goal₀ ← simplifysub-tactic prf₀ =<< inferFunRange (a→0 goalₐ `∘ holeₐ) -|
    holeₐ =′ (`λ $ 0→a goalₐ `$ weaken 1 s-goal₀ `$ `λ $ a→0 goalₐ `$ var₁ 1 (0→a Prfₐ `$ var₀ 0))

  induction : Tactic
  induction holeₐ = do
    goalₐ ← caseM inferType holeₐ of (λ
    { (pi _ (abs _ t)) → pure t
    ; (meta x _) → blockOnMeta x
    ; _ → typeErrorS "Induction tactic must be applied to a function goal"
    }) -|
    hole₀ ← (a→0 goalₐ `∘ holeₐ) :′ unknown -|
    caseM inferType hole₀ of λ
    { (pi a b)   →
        let P = lam visible b
            inStepCxt : {A : Set} → TC A → TC A
            inStepCxt {_} = λ′ (vArg (quoteTerm Nat)) ∘
                            λ′ (vArg unknown) in
        do base ← unknown :′ unknown -|
           step ← inStepCxt $ unknown :′ unknown -|
           holeₐ =′ 0→a goalₐ `∘ def₃ (quote nat-induction)
                                      P
                                      base
                                      (`λ $ `λ step) ~|
           base =′_ =<< autosub-tactic =<< inferType base ~|
           inStepCxt (step =′_ =<< by-tactic (var₀ 0) =<< inferType step)
    ; (meta x _) → blockOnMeta x
    ; _          → typeErrorS "Induction tactic must be applied to a function goal"
    }
