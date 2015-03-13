
module Tactic.Nat where

open import Prelude

open import Tactic.Nat.Auto  public
open import Tactic.Nat.Simpl public
open import Tactic.Nat.Reflect public using (cantProve; invalidGoal; QED)
