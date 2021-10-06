
module Tactic.Deriving.Quotable where

open import Prelude
open import Container.Traversable
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

  qQua : Quantity → Term
  qQua quantity-0 = con (quote quantity-0) []
  qQua quantity-ω = con (quote quantity-ω) []

  qMod : Modality → Term
  qMod (modality r q) = con₂ (quote modality) (qRel r) (qQua q)

  qArgInfo : ArgInfo → Term
  qArgInfo (arg-info v m) = con₂ (quote arg-info) (qVis v) (qMod m)

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
  patArgs tel = zipWith (λ x (_ , a) → var x <$ a) (reverse (from 0 for length tel)) tel

  quoteArgs′ : Nat → Telescope → List Term
  quoteArgs′ 0 _  = []
  quoteArgs′ _ [] = []
  quoteArgs′ (suc n) ((x , a) ∷ tel) =
    qArg (def₁ (quote `) (var n []) <$ a) ∷ quoteArgs′ n tel

  quoteArgs : Nat → Telescope → Term
  quoteArgs pars tel = qList $ replicate pars (qArg $ hArg (con₀ (quote Term.unknown))) ++
                               quoteArgs′ (length tel - pars) (drop pars tel)

  constructorClause : Nat → Name → TC Clause
  constructorClause pars c = do
    tel , _ ← telView <$> getType c
    let ps = patArgs tel
        parPs , conPs = splitAt pars ps
    pure (clause tel
                 (parPs ++ vArg (con c conPs) ∷ [])
                 (con₂ (quote Term.con) (lit (name c)) (quoteArgs pars tel)))

  quoteClauses : Name → TC (List Clause)
  quoteClauses d = do
    n ← getParameters d
    caseM getConstructors d of λ where
      [] → pure [ absurd-clause (("()" , vArg unknown) ∷ []) (vArg (absurd 0) ∷ []) ]
      cs → mapM (constructorClause n) cs

declareQuotableInstance : Name → Name → TC ⊤
declareQuotableInstance iname d =
  declareDef (iArg iname) =<< instanceType d (quote Quotable)

defineQuotableInstance : Name → Name → TC ⊤
defineQuotableInstance iname d = do
  fname ← freshName ("quote[" & show d & "]")
  declareDef (vArg fname) =<< quoteType d
  dictCon ← dictConstructor
  defineFun iname (clause [] [] (con₁ dictCon (def₀ fname)) ∷ [])
  defineFun fname =<< quoteClauses d
  return _

deriveQuotable : Name → Name → TC ⊤
deriveQuotable iname d =
  declareQuotableInstance iname d >>
  defineQuotableInstance  iname d
