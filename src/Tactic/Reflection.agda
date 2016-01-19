
module Tactic.Reflection where

open import Prelude
open import Builtin.Reflection           public
open import Tactic.Reflection.DeBruijn   public
open import Tactic.Reflection.Telescope  public
open import Tactic.Reflection.Substitute public
open import Tactic.Reflection.Free       public

el! : Term → Type
el! = el unknown

set₀ : Type
set₀ = el! (agda-sort (lit 0))

set! : Type
set! = el! (agda-sort unknown)

pattern def₀ f         = def f []
pattern def₁ f x       = def f (vArg x ∷ [])
pattern def₂ f x y     = def f (vArg x ∷ vArg y ∷ [])
pattern def₃ f x y z   = def f (vArg x ∷ vArg y ∷ vArg z ∷ [])
pattern def₄ f x y z u = def f (vArg x ∷ vArg y ∷ vArg z ∷ vArg u ∷ [])

pattern con₀ c         = con c []
pattern con₁ c x       = con c (vArg x ∷ [])
pattern con₂ c x y     = con c (vArg x ∷ vArg y ∷ [])
pattern con₃ c x y z   = con c (vArg x ∷ vArg y ∷ vArg z ∷ [])
pattern con₄ c x y z u = con c (vArg x ∷ vArg y ∷ vArg z ∷ vArg u ∷ [])

pattern _`→_  a b = pi (vArg (el unknown a)) (abs "_" (el unknown b))
pattern _`→ʰ_ a b = pi (hArg (el unknown a)) (abs "_" (el unknown b))
pattern _`→ⁱ_ a b = pi (iArg (el unknown a)) (abs "_" (el unknown b))
infixr 4 _`→_ _`→ʰ_ _`→ⁱ_

on-goal : (Type → Tactic) → Tactic
on-goal tac hole = inferType hole >>= λ goal → tac goal hole

forceFun : Type → TC Type
forceFun (el s a) =
  newMeta set! >>= λ dom →
  newMeta set! >>= λ rng →
  unify a (pi (vArg (el! dom)) (abs "_" (el! $ weaken 1 rng))) >>
  el s <$> normalise a
