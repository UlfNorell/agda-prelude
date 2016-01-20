
module Tactic.Deriving.Quotable where

open import Prelude
open import Data.Traversable
open import Tactic.Reflection
open import Tactic.Reflection.Quote.Class
open import Tactic.Deriving

private
  -- Bootstrapping
  qVis : Visibility → Term
  qVis visible = con (quote visible) []
  qVis hidden = con (quote hidden) []
  qVis instance′ = con (quote instance′) []

  qRel : Relevance → Term
  qRel relevant   = con (quote relevant) []
  qRel irrelevant = con (quote irrelevant) []

  qArgInfo : ArgInfo → Term
  qArgInfo (arg-info v r) = con₂ (quote arg-info) (qVis v) (qRel r)

  qArg : Arg Term → Term
  qArg (arg i x) = con₂ (quote arg) (qArgInfo i) x

  qList : List Term → Term
  qList = foldr (λ x xs → con₂ (quote List._∷_) x xs)
                (con₀ (quote List.[]))

  -- Could compute this from the type of the dictionary constructor
  quoteType : Name → TC Type
  quoteType d =
    caseM instanceTelescope d (quote Quotable) of λ
    { (tel , vs) → pure $ telPi tel $ def d vs `→ def (quote Term) []
    }

  dictConstructor : TC Name
  dictConstructor =
    caseM getConstructors (quote Quotable) of λ
    { (c ∷ []) → pure c
    ; _ → typeErrorS "impossible" }

  patArgs : Telescope → List (Arg Pattern)
  patArgs tel = map (var "x" <$_) tel

  quoteArgs′ : Nat → Telescope → List Term
  quoteArgs′ 0 _  = []
  quoteArgs′ _ [] = []
  quoteArgs′ (suc n) (a ∷ tel) =
    qArg (def₁ (quote `) (var n []) <$ a) ∷ quoteArgs′ n tel

  quoteArgs : Nat → Telescope → Term
  quoteArgs pars tel = qList $ replicate pars (qArg $ hArg (con₀ (quote Term.unknown))) ++
                               quoteArgs′ (length tel) tel

  constructorClause : Nat → Name → TC Clause
  constructorClause pars c =
    do tel ← drop pars ∘ fst ∘ telView <$> getType c
    -| pure (clause (vArg (con c (patArgs tel)) ∷ [])
                    (con₂ (quote Term.con) (lit (name c)) (quoteArgs pars tel)))

  quoteClauses : Name → TC (List Clause)
  quoteClauses d =
    do n ← getParameters d
    -| caseM getConstructors d of λ
       { [] → pure [ absurd-clause (vArg absurd ∷ []) ]
       ; cs → mapM (constructorClause n) cs }

declareQuotableInstance : Name → Name → TC ⊤
declareQuotableInstance iname d =
  declareDef (iArg iname) =<< instanceType d (quote Quotable)

defineQuotableInstance : Name → Name → TC ⊤
defineQuotableInstance iname d =
  do fname ← freshName ("quote[" & show d & "]")
  -| declareDef (vArg fname) =<< quoteType d
  ~| dictCon ← dictConstructor
  -| defineFun iname (clause [] (con₁ dictCon (def₀ fname)) ∷ [])
  ~| defineFun fname =<< quoteClauses d
  ~| return _

deriveQuotable : Name → Name → TC ⊤
deriveQuotable iname d =
  declareQuotableInstance iname d >>
  defineQuotableInstance iname d
