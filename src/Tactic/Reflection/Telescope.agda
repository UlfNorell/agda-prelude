
module Tactic.Reflection.Telescope where

open import Prelude
open import Builtin.Reflection
open import Tactic.Reflection.DeBruijn

Telescope = List (Arg Type)

telView : Type → Telescope × Type
telView (el _ (pi a (abs _ b))) = first (_∷_ a) (telView b)
telView a                       = [] , a

telPi : Telescope → Type → Type
telPi tel b = foldr (λ a b → el unknown (pi a (abs "_" b))) b tel

dataParameters : Name → Nat
dataParameters d =
  case definitionOf d of
   λ { (data-type npars cs) → npars
     ; _ → 0 }
