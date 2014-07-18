
module Tactic.Reflection.Telescope where

open import Prelude
open import Builtin.Reflection
open import Tactic.Reflection.DeBruijn

Telescope = List (Arg Type)

telView : Type → Telescope × Type
telView (el _ (pi a b)) = first (_∷_ a) (telView b)
telView a               = [] , a

telPi : Telescope → Type → Type
telPi tel b = foldr (λ a b → el unknown (pi a b)) b tel

private
  countPars : Nat → List Term → Nat
  countPars (suc n) (var i [] ∷ xs) =
    ifYes i == n then 1 + countPars n xs else 0
  countPars _ _ = 0

  conParams : Telescope × Type → Nat
  conParams (tel , tgt) =
    case unEl tgt of
    λ { (def _ args) → countPars (length tel) (map unArg args)
      ; _ → 0
      }

dataParameters : Name → Nat
dataParameters d =
  case definitionOf d of
   λ { (data-type cs) → foldr min (length tel) (map (conParams ∘ telView ∘ typeOf) cs)
     ; _ → 0 }
  where
    tel = fst $ telView $ typeOf d
