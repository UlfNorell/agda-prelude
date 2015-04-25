
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

arity : Name → Nat
arity = length ∘ fst ∘ telView ∘ typeOf

argTel : Name → Telescope
argTel = fst ∘ telView ∘ typeOf

telePat : Telescope → List (Arg Pattern)
telePat = map (var "_" <$_)

private
  teleArgs′ : Nat → List (Arg Type) → List (Arg Term)
  teleArgs′ (suc n) (a ∷ Γ) = (var n [] <$ a) ∷ teleArgs′ n Γ
  teleArgs′ _ _ = []

teleArgs : Telescope → List (Arg Term)
teleArgs Γ = teleArgs′ (length Γ) Γ

conParams : Name → Nat
conParams c =
  case definitionOf c of λ
  { (data-cons d) → dataParameters d
  ; _             → 0 }

conPat : Name → Pattern
conPat c = con c $ telePat $ drop (conParams c) (argTel c)

conTerm : Name → Term
conTerm c = con c (teleArgs $ drop (conParams c) (argTel c))

