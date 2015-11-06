
module Tactic.Reflection where

open import Prelude
open import Builtin.Reflection

on-goal : Name → Term
on-goal tac = quote-goal $ abs "g" $ unquote-term (def tac (vArg (var 0 []) ∷ [])) []

use : ∀ {a b} {A : Set a} {B : Set b} → A → (A → B) → B
use x f = f x
{-# STATIC use #-}

on-type-of-term : Name → Term → Term
on-type-of-term tac t =
  def (quote use)
    $ vArg t
    ∷ vArg (on-goal tac)
    ∷ []

infixr -100 apply-tactic apply-goal-tactic
syntax apply-tactic (λ _ → tac) (λ x → goal) = tac to x => goal
apply-tactic : ∀ {a b} {A : Set a} {B : Set b} → (A → B) → A → B
apply-tactic f x = f x

syntax apply-goal-tactic (λ _ → tac) goal = tac => goal
apply-goal-tactic = apply-tactic

rewrite-goal-tactic : Name → Term
rewrite-goal-tactic tac =
  quote-goal $ abs "g" $
    unquote-term (def tac (vArg (var 0 []) ∷ []))
                 (vArg (var 1 []) ∷ [])

rewrite-argument-tactic : Name → Term → Term
rewrite-argument-tactic tac t =
  def (quote use) $ vArg t ∷ vArg (rewrite-goal-tactic tac) ∷ []
