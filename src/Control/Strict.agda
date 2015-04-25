
module Control.Strict where

open import Prelude

record Forceable {b a} (A : Set a) : Set (a ⊔ lsuc b) where
  constructor forceableDict
  field
    force : {B : A → Set b} (x : A) → (∀ y → B y) → B x
    force-is-id : ∀ {B : A → Set b} x (f : ∀ y → B y) → force x f ≡ f x

open Forceable {{...}} public

{-# DISPLAY Forceable.force _ = force #-}

-- Proof helpers --

-- More efficient to type check this than the inlining.
force-eq : ∀ {a b} {A : Set a} {B : A → Set b} {{_ : Forceable A}} (x : A) {f : ∀ x → B x} {y : B x} →
             f x ≡ y → force x f ≡ y
force-eq x eq = force-is-id x _ ⟨≡⟩ eq

-- Deriving Forceable --

open import Builtin.Reflection
open import Tactic.Deriving.Eq
open import Tactic.Reflection.Telescope
open import Tactic.Reflection.DeBruijn

pattern el′ a = el unknown a
pattern any  = el′ unknown

private
  derivedType′ : Nat → Telescope → Name → List (Arg Term) → Type
  derivedType′ (suc n) (a ∷ Γ) d vs = el′ $ pi (hArg (unArg a)) $ abs "_" $ derivedType′ n Γ d ((var n [] <$ a) ∷ vs) 
  derivedType′ zero    [] d vs =
    el′ $ pi (hArg any) $ abs "b" $
    el′ $ def (quote Forceable) $
      hArg (var 0 []) ∷
      vArg (weaken 1 $ def d (reverse vs)) ∷ []
  derivedType′ _ _ _ _ = any  -- impossible

  derivedType : Telescope → Name → Type
  derivedType Γ x = derivedType′ (length Γ) Γ x []

  mkClause : (Name → Term) → Name → Clause
  mkClause f c = clause (vArg (conPat c) ∷ vArg (var "f") ∷ []) (f c)

  match : List Name → (Name → Term) → Term
  match cs f = pat-lam (map (mkClause f) cs) []

  derivedInstance : List Name → Term
  derivedInstance cs =
    con (quote forceableDict)
        (vArg (match cs (λ c → var 0 (vArg (weaken 1 (conTerm c)) ∷ []))) ∷
         vArg (match cs (λ _ → con (quote refl) [])) ∷ [])

deriveForceable : Name → Function
deriveForceable d =
  case definitionOf d of λ
  { (data-type pars cs) →
    fun-def (derivedType (argTel d) d)
            [ clause [] (derivedInstance cs) ]
  ; _ → fun-def (el′ (def (quote ⊥) [])) [ clause [] (lit (string $ "Not a datatype: " & show d)) ]
  }

instance
  unquoteDecl ForceNat    = deriveForceable (quote Nat)
  unquoteDecl ForceList   = deriveForceable (quote List)
  unquoteDecl ForceMaybe  = deriveForceable (quote Maybe)
  unquoteDecl ForceEither = deriveForceable (quote Either)
  unquoteDecl ForceSigma  = deriveForceable (quote Σ)