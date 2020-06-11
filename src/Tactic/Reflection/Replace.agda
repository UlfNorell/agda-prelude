module Tactic.Reflection.Replace where
  open import Prelude

  open import Container.Traversable

  open import Tactic.Reflection
  open import Tactic.Reflection.Equality

  {-# TERMINATING #-}
  _r[_/_] : Term → Term → Term → Term
  p r[ r / l ] =
    ifYes p == l
      then r
      else case p of λ
        { (var x args) → var x $ args r₂[ r / l ]
        ; (con c args) → con c $ args r₂[ r / l ]
        ; (def f args) → def f $ args r₂[ r / l ]
        ; (lam v t) → lam v $ t r₁[ weaken 1 r / weaken 1 l ] -- lam v <$> t r₁[ weaken 1 r / weaken 1 l ]
        ; (pat-lam cs args) →
            let w = length args in
            pat-lam (replaceClause (weaken w l) (weaken w r) <$> cs) $ args r₂[ r / l ]
        ; (pi a b) → pi (a r₁[ r / l ]) (b r₁[ weaken 1 r / weaken 1 l ])
        ; (agda-sort s) → agda-sort $ replaceSort l r s
        ; (lit l) → lit l
        ; (meta x args) → meta x $ args r₂[ r / l ]
        ; unknown → unknown
        }
      where

      replaceClause : Term → Term → Clause → Clause
      replaceClause l r (clause tel pats x) = clause tel pats $ x r[ r / l ]
      replaceClause l r (absurd-clause tel pats) = absurd-clause tel pats

      replaceSort : Term → Term → Sort → Sort
      replaceSort l r (set t) = set $ t r[ r / l ]
      replaceSort l r (lit n) = lit n
      replaceSort l r unknown = unknown

      _r₁[_/_] : {T₀ : Set → Set} {{_ : Traversable T₀}} → T₀ Term → Term → Term → T₀ Term
      p r₁[ r / l ] = _r[ r / l ] <$> p

      _r₂[_/_] : {T₀ T₁ : Set → Set} {{_ : Traversable T₀}} {{_ : Traversable T₁}} →
                 T₁ (T₀ Term) → Term → Term → T₁ (T₀ Term)
      p r₂[ r / l ] = fmap _r[ r / l ] <$> p

  _R[_/_] : List (Arg Type) → Type → Type → List (Arg Type)
  Γ R[ L / R ] = go Γ (strengthen 1 L) (strengthen 1 R) where
    go : List (Arg Type) → Maybe Term → Maybe Term → List (Arg Type)
    go (γ ∷ Γ) (just L) (just R) = (caseF γ of _r[ L / R ]) ∷ go Γ (strengthen 1 L) (strengthen 1 R)
    go Γ _ _ = Γ
