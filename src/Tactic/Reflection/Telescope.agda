
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

arity : Name → TC Nat
arity f = length ∘ fst ∘ telView <$> getType f

argTel : Name → TC Telescope
argTel f = fst ∘ telView <$> getType f

telePat : Telescope → List (Arg Pattern)
telePat = map (var "_" <$_)

private
  teleArgs′ : Nat → List (Arg Type) → List (Arg Term)
  teleArgs′ (suc n) (a ∷ Γ) = (var n [] <$ a) ∷ teleArgs′ n Γ
  teleArgs′ _ _ = []

teleArgs : Telescope → List (Arg Term)
teleArgs Γ = teleArgs′ (length Γ) Γ

conParams : Name → TC Nat
conParams c =
  caseM getDefinition c of λ
  { (data-cons d) → getParameters d
  ; _             → pure 0 }

conPat : Name → TC Pattern
conPat c =
  do np ← conParams c
  -| con c ∘ telePat ∘ drop np <$> argTel c

conTerm : Name → TC Term
conTerm c =
  do np ← conParams c
  -| con c ∘ teleArgs ∘ drop np <$> argTel c
