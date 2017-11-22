
module Tactic.Reflection.Quote where

open import Prelude
open import Builtin.Reflection
open import Builtin.Float
open import Tactic.Reflection.Quote.Class public
open import Tactic.Deriving.Quotable
open import Container.Traversable

--- Instances ---

private
  QuoteLit : {A : Set} → (A → Literal) → Quotable A
  ` {{QuoteLit f}} x = lit (f x)

-- Primitive types --

instance
  QuotableNat    = QuoteLit nat
  QuotableWord64 = QuoteLit word64
  QuotableFloat  = QuoteLit float
  QuotableString = QuoteLit string
  QuotableChar   = QuoteLit char
  QuotableName   = QuoteLit name

-- Standard data types --

unquoteDecl QuotableBool       = deriveQuotable QuotableBool       (quote Bool)
unquoteDecl QuotableList       = deriveQuotable QuotableList       (quote List)
unquoteDecl QuotableMaybe      = deriveQuotable QuotableMaybe      (quote Maybe)
unquoteDecl QuotableEither     = deriveQuotable QuotableEither     (quote Either)

instance
  QuotableΣ : ∀ {a b} {A : Set a} {B : A → Set b} {{_ : Quotable A}} {{_ : {x : A} → Quotable (B x)}} → Quotable (Σ A λ a → B a)
  QuotableΣ = record { ` = λ { (x , y) → con (quote _,_) ((vArg (` x)) ∷ vArg (` y) ∷ [])} }

unquoteDecl Quotable⊤          = deriveQuotable Quotable⊤          (quote ⊤)
unquoteDecl Quotable⊥          = deriveQuotable Quotable⊥          (quote ⊥)
unquoteDecl Quotable≡          = deriveQuotable Quotable≡          (quote _≡_)
unquoteDecl QuotableComparison = deriveQuotable QuotableComparison (quote Comparison)
unquoteDecl QuotableLessNat    = deriveQuotable QuotableLessNat    (quote LessNat)
unquoteDecl QuotableInt        = deriveQuotable QuotableInt        (quote Int)

-- The reflection machinery can't deal with computational irrelevance (..)
-- unquoteDecl QuotableFin        = deriveQuotable QuotableFin        (quote Fin)
-- unquoteDecl QuotableVec        = deriveQuotable QuotableVec        (quote Vec)

instance
  QuotableFin : ∀ {n} → Quotable (Fin n)
  ` {{QuotableFin}} zero    = con (quote Fin.zero) []
  ` {{QuotableFin}} (suc i) = con (quote Fin.suc) (vArg (` i) ∷ [])

  QuotableVec : ∀ {a} {A : Set a} {n} {{_ : Quotable A}} → Quotable (Vec A n)
  ` {{QuotableVec}} []       = con (quote Vec.[]) []
  ` {{QuotableVec}} (x ∷ xs) = con (quote Vec._∷_) (vArg (` x) ∷ vArg (` xs) ∷ [])

-- Reflection types --

instance
  QuotableMeta : Quotable Meta
  ` {{QuotableMeta}} x = lit (meta x)

private
  deriveQuotableTermTypes : Vec Name _ → TC ⊤
  deriveQuotableTermTypes is = do
    let ts : Vec Name _
        ts = quote Term ∷ quote Clause ∷ quote Sort ∷ []
        its = ⦇ is , ts ⦈
    traverse (uncurry declareQuotableInstance) its
    traverse (uncurry defineQuotableInstance)  its
    pure _

unquoteDecl QuotableVisibility QuotableRelevance QuotableArgInfo
            QuotableArg QuotableAbs QuotableLiteral = do
  deriveQuotable QuotableVisibility (quote Visibility)
  deriveQuotable QuotableRelevance  (quote Relevance)
  deriveQuotable QuotableArgInfo    (quote ArgInfo)
  deriveQuotable QuotableArg        (quote Arg)
  deriveQuotable QuotableAbs        (quote Abs)
  deriveQuotable QuotableLiteral    (quote Literal)

{-# TERMINATING #-}
unquoteDecl QuotablePattern QuotableTerm QuotableClause QuotableSort = do
  deriveQuotable QuotablePattern (quote Pattern)
  deriveQuotableTermTypes (QuotableTerm ∷ QuotableClause ∷ QuotableSort ∷ [])

quoteList : List Term → Term
quoteList = foldr (λ x xs → con (quote List._∷_) (vArg x ∷ vArg xs ∷ [])) (con (quote List.[]) [])
