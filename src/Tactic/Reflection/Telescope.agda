
module Tactic.Reflection.Telescope where

open import Prelude hiding (abs)
open import Builtin.Reflection
open import Tactic.Reflection.DeBruijn

telView : Type → Telescope × Type
telView (pi a (abs x b)) = first (_∷_ (x , a)) (telView b)
telView a                = [] , a

visibleArity : Type → Nat
visibleArity = length ∘ filter (isVisible ∘ snd) ∘ fst ∘ telView

telPi : Telescope → Type → Type
telPi tel b = foldr (λ (x , a) b → pi a (abs x b)) b tel

arity : Name → TC Nat
arity f = length ∘ fst ∘ telView <$> getType f

argTel : Name → TC Telescope
argTel f = fst ∘ telView <$> getType f

telePat : Telescope → List (Arg Pattern)
telePat tel = zipWith (λ x (_ , a) → var x <$ a) (reverse $ from 0 for n) tel
  where n = length tel

private
  teleArgs′ : Nat → List (Arg Type) → List (Arg Term)
  teleArgs′ (suc n) (a ∷ Γ) = (var n [] <$ a) ∷ teleArgs′ n Γ
  teleArgs′ _ _ = []

teleArgs : Telescope → List (Arg Term)
teleArgs Γ = teleArgs′ (length Γ) (map snd Γ)

conParams : Name → TC Nat
conParams c =
  caseM getDefinition c of λ
  { (data-cons d) → getParameters d
  ; _             → pure 0 }

conPat : Name → TC Pattern
conPat c = do
  np ← conParams c
  con c ∘ telePat ∘ drop np <$> argTel c

conTerm : Name → TC Term
conTerm c = do
  np ← conParams c
  con c ∘ teleArgs ∘ drop np <$> argTel c
