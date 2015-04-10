
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
open import Tactic.Nat.Subtract.Simplify using (simplifysub-tactic) public
open import Tactic.Nat.Subtract.By public
open import Tactic.Nat.Subtract.Refute public

macro
  autosub : Term
  autosub = on-goal (quote autosub-tactic)

  by : Term → Term
  by = on-type-of-term (quote by-tactic)

  simplifysub : Term → Term
  simplifysub = rewrite-argument-tactic (quote simplifysub-tactic)

  simplify-goal : Term
  simplify-goal = rewrite-goal-tactic (quote simplifysub-tactic)

  refutesub : Term → Term
  refutesub = on-type-of-term (quote refutesub-tactic)
