
module Tactic.Reflection.Equality where

open import Prelude
open import Builtin.Reflection
open import Builtin.Float

instance
  EqVisibility : Eq Visibility
  _==_ {{EqVisibility}} visible  visible  = yes refl
  _==_ {{EqVisibility}} visible  hidden   = no (λ ())
  _==_ {{EqVisibility}} visible  instance′ = no (λ ())
  _==_ {{EqVisibility}} hidden   visible  = no (λ ())
  _==_ {{EqVisibility}} hidden   hidden   = yes refl
  _==_ {{EqVisibility}} hidden   instance′ = no (λ ())
  _==_ {{EqVisibility}} instance′ visible  = no (λ ())
  _==_ {{EqVisibility}} instance′ hidden   = no (λ ())
  _==_ {{EqVisibility}} instance′ instance′ = yes refl

  EqRelevance : Eq Relevance
  _==_ {{EqRelevance}} relevant   relevant   = yes refl
  _==_ {{EqRelevance}} relevant   irrelevant = no (λ ())
  _==_ {{EqRelevance}} irrelevant relevant   = no (λ ())
  _==_ {{EqRelevance}} irrelevant irrelevant = yes refl

  EqArgInfo : Eq ArgInfo
  _==_ {{EqArgInfo}} (arg-info v r) (arg-info v₁ r₁) =
    decEq₂ arg-info-inj₁ arg-info-inj₂ (v == v₁) (r == r₁)

  EqArg : ∀ {A} {{EqA : Eq A}} → Eq (Arg A)
  _==_ {{EqArg}} (arg i x) (arg i₁ x₁) = decEq₂ arg-inj₁ arg-inj₂ (i == i₁) (x == x₁)

  EqLiteral : Eq Literal
  _==_ {{EqLiteral}} = eqLit
    where
      eqLit : (x y : Literal) → Dec (x ≡ y)
      eqLit (nat    x) (nat    y) = decEq₁ nat-inj    (x == y)
      eqLit (word64 x) (word64 y) = decEq₁ word64-inj (x == y)
      eqLit (float  x) (float  y) = decEq₁ float-inj  (x == y)
      eqLit (char   x) (char   y) = decEq₁ char-inj   (x == y)
      eqLit (string x) (string y) = decEq₁ string-inj (x == y)
      eqLit (name   x) (name   y) = decEq₁ name-inj   (x == y)
      eqLit (meta   x) (meta   y) = decEq₁ meta-inj   (x == y)

      eqLit (nat    _) (float  _) = no λ()
      eqLit (nat    _) (word64 _) = no λ()
      eqLit (nat    _) (char   _) = no λ()
      eqLit (nat    _) (string _) = no λ()
      eqLit (nat    _) (name   _) = no λ()
      eqLit (nat    _) (meta   _) = no λ()
      eqLit (word64 _) (nat    _) = no λ()
      eqLit (word64 _) (float  _) = no λ()
      eqLit (word64 _) (char   _) = no λ()
      eqLit (word64 _) (string _) = no λ()
      eqLit (word64 _) (name   _) = no λ()
      eqLit (word64 _) (meta   _) = no λ()
      eqLit (float  _) (nat    _) = no λ()
      eqLit (float  _) (word64 _) = no λ()
      eqLit (float  _) (char   _) = no λ()
      eqLit (float  _) (string _) = no λ()
      eqLit (float  _) (name   _) = no λ()
      eqLit (float  _) (meta   _) = no λ()
      eqLit (char   _) (nat    _) = no λ()
      eqLit (char   _) (word64 _) = no λ()
      eqLit (char   _) (float  _) = no λ()
      eqLit (char   _) (string _) = no λ()
      eqLit (char   _) (name   _) = no λ()
      eqLit (char   _) (meta   _) = no λ()
      eqLit (string _) (nat    _) = no λ()
      eqLit (string _) (word64 _) = no λ()
      eqLit (string _) (float  _) = no λ()
      eqLit (string _) (char   _) = no λ()
      eqLit (string _) (name   _) = no λ()
      eqLit (string _) (meta   _) = no λ()
      eqLit (name   _) (nat    _) = no λ()
      eqLit (name   _) (word64 _) = no λ()
      eqLit (name   _) (float  _) = no λ()
      eqLit (name   _) (char   _) = no λ()
      eqLit (name   _) (string _) = no λ()
      eqLit (name   _) (meta   _) = no λ()
      eqLit (meta   _) (nat    _) = no λ()
      eqLit (meta   _) (word64 _) = no λ()
      eqLit (meta   _) (float  _) = no λ()
      eqLit (meta   _) (char   _) = no λ()
      eqLit (meta   _) (string _) = no λ()
      eqLit (meta   _) (name   _) = no λ()

private
  eqSort   : (x y : Sort)    → Dec (x ≡ y)
  eqTerm   : (x y : Term)    → Dec (x ≡ y)
  eqPat    : (x y : Pattern) → Dec (x ≡ y)
  eqClause : (x y : Clause)  → Dec (x ≡ y)

  eqArgTerm : (x y : Arg Term) → Dec (x ≡ y)
  eqArgTerm (arg i x) (arg i₁ x₁) = decEq₂ arg-inj₁ arg-inj₂ (i == i₁) (eqTerm x x₁)

  eqArgPat : (x y : Arg Pattern) → Dec (x ≡ y)
  eqArgPat (arg i x) (arg i₁ x₁) = decEq₂ arg-inj₁ arg-inj₂ (i == i₁) (eqPat x x₁)

  eqAbsTerm : (x y : Abs Term) → Dec (x ≡ y)
  eqAbsTerm (abs s x) (abs s₁ x₁) = decEq₂ abs-inj₁ abs-inj₂ (s == s₁) (eqTerm x x₁)

  eqPats : (x y : List (Arg Pattern)) → Dec (x ≡ y)
  eqPats [] [] = yes refl
  eqPats [] (x ∷ xs) = no λ ()
  eqPats (x ∷ xs) [] = no λ ()
  eqPats (x ∷ xs) (y ∷ ys) = decEq₂ cons-inj-head cons-inj-tail (eqArgPat x y) (eqPats xs ys)

  eqArgs : (x y : List (Arg Term)) → Dec (x ≡ y)
  eqArgs [] [] = yes refl
  eqArgs [] (x ∷ xs) = no λ ()
  eqArgs (x ∷ xs) [] = no λ ()
  eqArgs (x ∷ xs) (y ∷ ys) = decEq₂ cons-inj-head cons-inj-tail (eqArgTerm x y) (eqArgs xs ys)

  eqClauses : (x y : List Clause) → Dec (x ≡ y)
  eqClauses [] [] = yes refl
  eqClauses [] (x ∷ xs) = no λ ()
  eqClauses (x ∷ xs) [] = no λ ()
  eqClauses (x ∷ xs) (y ∷ ys) = decEq₂ cons-inj-head cons-inj-tail (eqClause x y) (eqClauses xs ys)

  eqTerm (var x args) (var x₁ args₁) = decEq₂ var-inj₁ var-inj₂ (x == x₁) (eqArgs args args₁)
  eqTerm (con c args) (con c₁ args₁) = decEq₂ con-inj₁ con-inj₂ (c == c₁) (eqArgs args args₁)
  eqTerm (def f args) (def f₁ args₁) = decEq₂ def-inj₁ def-inj₂ (f == f₁) (eqArgs args args₁)
  eqTerm (meta x args) (meta x₁ args₁) = decEq₂ meta-inj₁ meta-inj₂ (x == x₁) (eqArgs args args₁)
  eqTerm (lam v x) (lam v₁ y) = decEq₂ lam-inj₁ lam-inj₂ (v == v₁) (eqAbsTerm x y)
  eqTerm (pi t₁ t₂) (pi t₃ t₄) = decEq₂ pi-inj₁ pi-inj₂ (eqArgTerm t₁ t₃) (eqAbsTerm t₂ t₄)
  eqTerm (agda-sort x) (agda-sort x₁) = decEq₁ sort-inj (eqSort x x₁)
  eqTerm (lit l) (lit l₁)   = decEq₁ lit-inj (l == l₁)
  eqTerm (pat-lam c args) (pat-lam c₁ args₁) = decEq₂ pat-lam-inj₁ pat-lam-inj₂ (eqClauses c c₁) (eqArgs args args₁)
  eqTerm unknown unknown = yes refl

  eqTerm (var x args) (con c args₁) = no λ ()
  eqTerm (var x args) (def f args₁) = no λ ()
  eqTerm (var x args) (lam v y) = no λ ()
  eqTerm (var x args) (pi t₁ t₂) = no λ ()
  eqTerm (var x args) (agda-sort x₁) = no λ ()
  eqTerm (var x args) (lit x₁) = no λ ()
  eqTerm (var x args) unknown = no λ ()
  eqTerm (con c args) (var x args₁) = no λ ()
  eqTerm (con c args) (def f args₁) = no λ ()
  eqTerm (con c args) (lam v y) = no λ ()
  eqTerm (con c args) (pi t₁ t₂) = no λ ()
  eqTerm (con c args) (agda-sort x) = no λ ()
  eqTerm (con c args) (lit x) = no λ ()
  eqTerm (con c args) unknown = no λ ()
  eqTerm (def f args) (var x args₁) = no λ ()
  eqTerm (def f args) (con c args₁) = no λ ()
  eqTerm (def f args) (lam v y) = no λ ()
  eqTerm (def f args) (pi t₁ t₂) = no λ ()
  eqTerm (def f args) (agda-sort x) = no λ ()
  eqTerm (def f args) (lit x) = no λ ()
  eqTerm (def f args) unknown = no λ ()
  eqTerm (lam v x) (var x₁ args) = no λ ()
  eqTerm (lam v x) (con c args) = no λ ()
  eqTerm (lam v x) (def f args) = no λ ()
  eqTerm (lam v x) (pi t₁ t₂) = no λ ()
  eqTerm (lam v x) (agda-sort x₁) = no λ ()
  eqTerm (lam v x) (lit x₁) = no λ ()
  eqTerm (lam v x) unknown = no λ ()
  eqTerm (pi t₁ t₂) (var x args) = no λ ()
  eqTerm (pi t₁ t₂) (con c args) = no λ ()
  eqTerm (pi t₁ t₂) (def f args) = no λ ()
  eqTerm (pi t₁ t₂) (lam v y) = no λ ()
  eqTerm (pi t₁ t₂) (agda-sort x) = no λ ()
  eqTerm (pi t₁ t₂) (lit x) = no λ ()
  eqTerm (pi t₁ t₂) unknown = no λ ()
  eqTerm (agda-sort x) (var x₁ args) = no λ ()
  eqTerm (agda-sort x) (con c args) = no λ ()
  eqTerm (agda-sort x) (def f args) = no λ ()
  eqTerm (agda-sort x) (lam v y) = no λ ()
  eqTerm (agda-sort x) (pi t₁ t₂) = no λ ()
  eqTerm (agda-sort x) (lit x₁) = no λ ()
  eqTerm (agda-sort x) unknown = no λ ()
  eqTerm (lit x) (var x₁ args) = no λ ()
  eqTerm (lit x) (con c args) = no λ ()
  eqTerm (lit x) (def f args) = no λ ()
  eqTerm (lit x) (lam v y) = no λ ()
  eqTerm (lit x) (pi t₁ t₂) = no λ ()
  eqTerm (lit x) (agda-sort x₁) = no λ ()
  eqTerm (lit x) unknown = no λ ()
  eqTerm unknown (var x args) = no λ ()
  eqTerm unknown (con c args) = no λ ()
  eqTerm unknown (def f args) = no λ ()
  eqTerm unknown (lam v y) = no λ ()
  eqTerm unknown (pi t₁ t₂) = no λ ()
  eqTerm unknown (agda-sort x) = no λ ()
  eqTerm unknown (lit x) = no λ ()

  eqTerm (var _ _) (meta _ _) = no λ ()
  eqTerm (con _ _) (meta _ _) = no λ ()
  eqTerm (def _ _) (meta _ _) = no λ ()
  eqTerm (lam _ _) (meta _ _) = no λ ()
  eqTerm (pi _ _) (meta _ _) = no λ ()
  eqTerm (agda-sort _) (meta _ _) = no λ ()
  eqTerm (lit _) (meta _ _) = no λ ()
  eqTerm unknown (meta _ _) = no λ ()
  eqTerm (meta _ _) (var _ _) = no λ ()
  eqTerm (meta _ _) (con _ _) = no λ ()
  eqTerm (meta _ _) (def _ _) = no λ ()
  eqTerm (meta _ _) (lam _ _) = no λ ()
  eqTerm (meta _ _) (pi _ _) = no λ ()
  eqTerm (meta _ _) (agda-sort _) = no λ ()
  eqTerm (meta _ _) (lit _) = no λ ()
  eqTerm (meta _ _) unknown = no λ ()

  eqTerm (var _ _) (pat-lam _ _) = no λ ()
  eqTerm (con _ _) (pat-lam _ _) = no λ ()
  eqTerm (def _ _) (pat-lam _ _) = no λ ()
  eqTerm (lam _ _) (pat-lam _ _) = no λ ()
  eqTerm (pi _ _) (pat-lam _ _) = no λ ()
  eqTerm (meta _ _) (pat-lam _ _) = no λ ()
  eqTerm (agda-sort _) (pat-lam _ _) = no λ ()
  eqTerm (lit _) (pat-lam _ _) = no λ ()
  eqTerm unknown (pat-lam _ _) = no λ ()
  eqTerm (pat-lam _ _) (var _ _) = no λ ()
  eqTerm (pat-lam _ _) (con _ _) = no λ ()
  eqTerm (pat-lam _ _) (def _ _) = no λ ()
  eqTerm (pat-lam _ _) (lam _ _) = no λ ()
  eqTerm (pat-lam _ _) (pi _ _) = no λ ()
  eqTerm (pat-lam _ _) (meta _ _) = no λ ()
  eqTerm (pat-lam _ _) (agda-sort _) = no λ ()
  eqTerm (pat-lam _ _) (lit _) = no λ ()
  eqTerm (pat-lam _ _) unknown = no λ ()

  eqSort (set t) (set t₁) = decEq₁ set-inj (eqTerm t t₁)
  eqSort (lit n) (lit n₁) = decEq₁ slit-inj (n == n₁)
  eqSort unknown unknown = yes refl
  eqSort (set t) (lit n) = no λ ()
  eqSort (set t) unknown = no λ ()
  eqSort (lit n) (set t) = no λ ()
  eqSort (lit n) unknown = no λ ()
  eqSort unknown (set t) = no λ ()
  eqSort unknown (lit n) = no λ ()

  eqPat (con c ps) (con c₁ ps₁) = decEq₂ pcon-inj₁ pcon-inj₂ (c == c₁) (eqPats ps ps₁)
  eqPat  dot        dot         = yes refl
  eqPat (var s)    (var s₁)     = decEq₁ pvar-inj (s == s₁)
  eqPat (lit l)    (lit l₁)     = decEq₁ plit-inj (l == l₁)
  eqPat (proj f)   (proj f₁)    = decEq₁ proj-inj (f == f₁)
  eqPat  absurd     absurd      = yes refl

  eqPat (con _ _) dot      = no λ ()
  eqPat (con _ _) (var _)  = no λ ()
  eqPat (con _ _) (lit _)  = no λ ()
  eqPat (con _ _) (proj _) = no λ ()
  eqPat (con _ _) absurd   = no λ ()

  eqPat dot (con _ _) = no λ ()
  eqPat dot (var _)   = no λ ()
  eqPat dot (lit _)   = no λ ()
  eqPat dot (proj _)  = no λ ()
  eqPat dot absurd    = no λ ()

  eqPat (var _) (con _ _) = no λ ()
  eqPat (var _) dot       = no λ ()
  eqPat (var _) (lit _)   = no λ ()
  eqPat (var _) (proj _)  = no λ ()
  eqPat (var _) absurd    = no λ ()

  eqPat (lit _) (con _ _) = no λ ()
  eqPat (lit _) dot       = no λ ()
  eqPat (lit _) (var _)   = no λ ()
  eqPat (lit _) (proj _)  = no λ ()
  eqPat (lit _) absurd    = no λ ()

  eqPat (proj _) (con _ _) = no λ ()
  eqPat (proj _) dot       = no λ ()
  eqPat (proj _) (var _)   = no λ ()
  eqPat (proj _) (lit _)   = no λ ()
  eqPat (proj _) absurd    = no λ ()

  eqPat absurd (con _ _) = no λ ()
  eqPat absurd dot       = no λ ()
  eqPat absurd (var _)   = no λ ()
  eqPat absurd (lit _)   = no λ ()
  eqPat absurd (proj _)  = no λ ()

  eqClause (clause ps t)      (clause ps₁ t₁)     = decEq₂ clause-inj₁ clause-inj₂ (eqPats ps ps₁) (eqTerm t t₁)
  eqClause (absurd-clause ps) (absurd-clause ps₁) = decEq₁ absurd-clause-inj (eqPats ps ps₁)
  eqClause (clause _ _) (absurd-clause _) = no λ ()
  eqClause (absurd-clause _) (clause _ _) = no λ ()

instance
  EqTerm : Eq Term
  _==_ {{EqTerm}} = eqTerm

  EqSort : Eq Sort
  _==_ {{EqSort}} = eqSort

  EqClause : Eq Clause
  _==_ {{EqClause}} = eqClause

  EqPattern : Eq Pattern
  _==_ {{EqPattern}} = eqPat
