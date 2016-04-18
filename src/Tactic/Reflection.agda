
module Tactic.Reflection where

open import Prelude
open import Builtin.Reflection           public
open import Tactic.Reflection.DeBruijn   public
open import Tactic.Reflection.Telescope  public
open import Tactic.Reflection.Substitute public
open import Tactic.Reflection.Free       public
open import Tactic.Reflection.Equality   public

set₀ : Type
set₀ = agda-sort (lit 0)

set! : Type
set! = agda-sort unknown

pattern var₀ x         = var x []
pattern var₁ x a       = var x (vArg a ∷ [])
pattern var₂ x a b     = var x (vArg a ∷ vArg b ∷ [])
pattern var₃ x a b c   = var x (vArg a ∷ vArg b ∷ vArg c ∷ [])
pattern var₄ x a b c d = var x (vArg a ∷ vArg b ∷ vArg c ∷ vArg d ∷ [])

pattern con₀ c         = con c []
pattern con₁ c x       = con c (vArg x ∷ [])
pattern con₂ c x y     = con c (vArg x ∷ vArg y ∷ [])
pattern con₃ c x y z   = con c (vArg x ∷ vArg y ∷ vArg z ∷ [])
pattern con₄ c x y z u = con c (vArg x ∷ vArg y ∷ vArg z ∷ vArg u ∷ [])

pattern def₀ f         = def f []
pattern def₁ f x       = def f (vArg x ∷ [])
pattern def₂ f x y     = def f (vArg x ∷ vArg y ∷ [])
pattern def₃ f x y z   = def f (vArg x ∷ vArg y ∷ vArg z ∷ [])
pattern def₄ f x y z u = def f (vArg x ∷ vArg y ∷ vArg z ∷ vArg u ∷ [])

infixr 4 _`→_ _`→ʰ_ _`→ⁱ_
_`→_ _`→ʰ_ _`→ⁱ_ : Type → Type → Type
_`→_  a b = pi (vArg a) (abs "_" b)
_`→ʰ_ a b = pi (hArg a) (abs "_" b)
_`→ⁱ_ a b = pi (iArg a) (abs "_" b)

`λ : Term → Term
`λ b = lam visible (abs "_" b)

infixl 9 _`∘_
_`∘_ : Term → Term → Term
_`∘_ = def₂ (quote _∘_)

infixr -20 _`$_
_`$_ : Term → Term → Term
_`$_ = def₂ (quote _$_)

_:′_ : Term → Type → TC Term
_:′_ = checkType

λ′ : ∀ {a} {A : Set a} → Arg Type → TC A → TC A
λ′ = extendContext

infix 2 _=′_
_=′_ : Term → Term → TC ⊤
_=′_ = unify

on-goal : (Type → Tactic) → Tactic
on-goal tac hole = inferType hole >>= λ goal → tac goal hole

forceFun : Type → TC Type
forceFun a =
  do dom ← newMeta set!
  -| rng ← newMeta set!
  -| unify a (dom `→ weaken 1 rng)
  ~| normalise a

inferFunRange : Term → TC Type
inferFunRange hole = unPi =<< forceFun =<< inferType hole where
  unPi : Type → TC Type
  unPi (pi _ (abs _ (meta x _))) = blockOnMeta! x
  unPi (pi _ (abs _ b)) = maybe (typeError (strErr "Must be applied in a non-dependent function position" ∷ termErr b ∷ [])) pure $ strengthen 1 b
  unPi x = typeError (strErr "Invalid goal" ∷ termErr x ∷ [])

macro
  runT : Tactic → Tactic
  runT t = t

evalTC : ∀ {a} {A : Set a} → TC A → Tactic
evalTC {A = A} c hole =
  do v ← c
  =| `v ← quoteTC v
  -| `A ← quoteTC A
  -| checkedHole ← checkType hole `A
  -| unify checkedHole `v

macro
  evalT : ∀ {a} {A : Set a} → TC A → Tactic
  evalT = evalTC
