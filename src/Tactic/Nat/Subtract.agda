
module Tactic.Nat.Subtract where

open import Prelude
open import Builtin.Reflection
open import Tactic.Reflection.Quote
open import Tactic.Reflection
open import Control.Monad.State

open import Tactic.Nat.Reflect
open import Tactic.Nat.NF
open import Tactic.Nat.Exp
open import Tactic.Nat.Auto
open import Tactic.Nat.Auto.Lemmas
open import Tactic.Nat.Simpl.Lemmas
open import Tactic.Nat.Simpl
open import Tactic.Nat.Reflect

open import Tactic.Nat.Subtract.Exp
open import Tactic.Nat.Subtract.Reflect
open import Tactic.Nat.Subtract.Lemmas
open import Tactic.Nat.Less.Lemmas

-- Tactics --

open import Tactic.Nat.Subtract.Auto public
open import Tactic.Nat.Subtract.Simplify using (simplify-goal; simplifysub ) public
open import Tactic.Nat.Subtract.By public
open import Tactic.Nat.Subtract.Refute public

macro
  autosub : Tactic
  autosub hole =
    inferType hole >>= λ goal → unify hole =<< autosub-tactic goal

  by : Term → Tactic
  by prf hole =
    inferType hole >>= λ goal → unify hole =<< by-tactic prf goal

  refutesub : Term → Tactic
  refutesub prf hole = unify hole =<< refutesub-tactic prf
