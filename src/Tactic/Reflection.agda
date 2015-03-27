
module Tactic.Reflection where

open import Prelude
open import Builtin.Reflection

on-goal : Name → Term
on-goal tac = quote-goal $ abs "g" $ unquote-term (def tac (vArg (var 0 []) ∷ []))
