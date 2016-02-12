
module Tactic.Reflection where

open import Prelude
open import Builtin.Reflection           public
open import Tactic.Reflection.DeBruijn   public
open import Tactic.Reflection.Telescope  public
open import Tactic.Reflection.Substitute public
open import Tactic.Reflection.Free       public

set₀ : Type
set₀ = agda-sort (lit 0)

set! : Type
set! = agda-sort unknown

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

infixr 4 _`→_ _`→ʰ_ _`→ⁱ_
_`→_ _`→ʰ_ _`→ⁱ_ : Type → Type → Type
_`→_  a b = pi (vArg a) (abs "_" b)
_`→ʰ_ a b = pi (hArg a) (abs "_" b)
_`→ⁱ_ a b = pi (iArg a) (abs "_" b)

on-goal : (Type → Tactic) → Tactic
on-goal tac hole = inferType hole >>= λ goal → tac goal hole

forceFun : Type → TC Type
forceFun a =
  do dom ← newMeta set!
  -| rng ← newMeta set!
  -| unify a (dom `→ weaken 1 rng)
  ~| normalise a

macro
  runT : Tactic → Tactic
  runT t = t

evalTC : ∀ {a} {A : Set a} → TC A → Tactic
evalTC c hole =
  do v ← c
  =| `v ← quoteTC v
  =| unify hole `v

macro
  evalT : ∀ {a} {A : Set a} → TC A → Tactic
  evalT = evalTC
