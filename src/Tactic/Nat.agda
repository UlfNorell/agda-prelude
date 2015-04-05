
module Tactic.Nat where

open import Prelude

open import Tactic.Nat.Reflect public using (cantProve; invalidGoal; QED)
open import Tactic.Nat.Induction public
open import Tactic.Nat.Subtract public renaming
  ( autosub          to auto
  ; simplifysub      to simplify
  ; follows-from-sub to follows-from
  ; refutesub        to refute )

open import Tactic.Reflection public using (apply-tactic; apply-goal-tactic)