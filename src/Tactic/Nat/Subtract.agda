
module Tactic.Nat.Subtract where

open import Tactic.Nat.Subtract.Auto public using (autosub-tactic)
open import Tactic.Nat.Subtract.Simplify public using (simplifysub-tactic; simplifygoal-tactic)
open import Tactic.Nat.Subtract.By public using (by-tactic)
open import Tactic.Nat.Subtract.Refute public using (refutesub-tactic)
