
module Tactic.Reflection where

open import Prelude
open import Builtin.Reflection

on-goal : (Type → Tactic) → Tactic
on-goal tac hole = inferType hole >>= λ goal → tac goal hole

use : ∀ {a b} {A : Set a} {B : Set b} → A → (A → B) → B
use x f = f x
{-# INLINE use #-}
