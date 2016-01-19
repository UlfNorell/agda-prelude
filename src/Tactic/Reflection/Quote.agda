
module Tactic.Reflection.Quote where

open import Prelude
open import Builtin.Reflection
open import Builtin.Float
open import Tactic.Reflection.Quote.Class public
open import Tactic.Deriving.Quotable

--- Instances ---

-- Nat --

pattern `zero  = con (quote Nat.zero) []
pattern `suc n = con (quote Nat.suc) (vArg n ∷ [])

instance
  QuotableNat : Quotable Nat
  QuotableNat = record { ` = λ n → lit (nat n) }

-- Float --

instance
  QuotableFloat : Quotable Float
  ` {{QuotableFloat}} x = lit (float x)

-- Char --

instance
  QuotableChar : Quotable Char
  ` {{QuotableChar}} c = lit (char c)

-- String --

instance
  QuotableString : Quotable String
  ` {{QuotableString}} s = lit (string s)

-- Bool --

pattern `true  = con (quote Bool.true) []
pattern `false = con (quote Bool.false) []

instance
  QuotableBool : Quotable Bool
  QuotableBool = record { ` = quoteBool }
    where
      quoteBool : Bool → Term
      quoteBool false = `false
      quoteBool true  = `true

-- List --

infixr 5 _`∷_
pattern `[]       = con (quote List.[]) []
pattern _`∷_ x xs = con (quote List._∷_) (vArg x ∷ vArg xs ∷ [])

instance
  QuotableList : ∀ {a} {A : Set a} {{QuotableA : Quotable A}} → Quotable (List A)
  QuotableList = record { ` = quoteList }
    where
      quoteList : List _ → Term
      quoteList [] = `[]
      quoteList (x ∷ xs) = ` x `∷ quoteList xs

-- Maybe --

pattern `nothing = con (quote nothing) []
pattern `just x  = con (quote just) (vArg x ∷ [])

instance
  QuotableMaybe : ∀ {a} {A : Set a} {{QuotableA : Quotable A}} → Quotable (Maybe A)
  QuotableMaybe = record { ` = quoteMaybe }
    where
      quoteMaybe : Maybe _ → Term
      quoteMaybe nothing  = `nothing
      quoteMaybe (just x) = `just (` x)

-- Either --

pattern `left  x = con (quote left)  (vArg x ∷ [])
pattern `right x = con (quote right) (vArg x ∷ [])

instance
  QuotableEither : ∀ {a b} {A : Set a} {B : Set b} {{QuotableA : Quotable A}} {{QuotableB : Quotable B}} →
                     Quotable (Either A B)
  QuotableEither = record { ` = quoteEither }
    where
      quoteEither : Either _ _ → Term
      quoteEither (left x)  = `left  (` x)
      quoteEither (right x) = `right (` x)

-- Sigma --

infixr 1 _`,_
pattern _`,_ x y = con (quote _,_) (vArg x ∷ vArg y ∷ [])

instance
  QuotableSigma : ∀ {a b} {A : Set a} {B : A → Set b}
                    {{QuotableA : Quotable A}} {{QuotableB : ∀ {x} → Quotable (B x)}} →
                    Quotable (Σ A B)
  QuotableSigma = record { ` = quoteSigma }
    where
      quoteSigma : Σ _ _ → Term
      quoteSigma (x , y) = ` x `, ` y

-- Name --

instance
  QuotableName : Quotable Name
  ` {{QuotableName}} x = lit (name x)

-- Term --

private
  pattern con₁ c x   = con c (vArg x ∷ [])
  pattern con₂ c x y = con c (vArg x ∷ vArg y ∷ [])
  dummy : Nat
  dummy = 0

instance
  QuotableVisibility : Quotable Visibility
  ` {{QuotableVisibility}} visible = con (quote visible) []
  ` {{QuotableVisibility}} hidden = con (quote hidden) []
  ` {{QuotableVisibility}} instance′ = con (quote instance′) []

  QuotableRelevance : Quotable Relevance
  ` {{QuotableRelevance}} relevant = con (quote relevant) []
  ` {{QuotableRelevance}} irrelevant = con (quote irrelevant) []

  QuotableArgInfo : Quotable ArgInfo
  ` {{QuotableArgInfo}} (arg-info v r) = con₂ (quote arg-info) (` v) (` r)

  QuotableArg : ∀ {A} {{_ : Quotable A}} → Quotable (Arg A)
  ` {{QuotableArg}} (arg i x) = con₂ (quote arg) (` i) (` x)

  QuotableAbs : ∀ {A} {{_ : Quotable A}} → Quotable (Abs A)
  ` {{QuotableAbs}} (abs x b) = con₂ (quote abs) (` x) (` b)

  QuotableLit : Quotable Literal
  ` {{QuotableLit}} (nat x) = con₁ (quote nat) (` x)
  ` {{QuotableLit}} (float x) = con₁ (quote float) (` x)
  ` {{QuotableLit}} (char x) = con₁ (quote char) (` x)
  ` {{QuotableLit}} (string x) = con₁ (quote string) (` x)
  ` {{QuotableLit}} (name x) = con₁ (quote name) (` x)

  {-# TERMINATING #-}
  QuotablePattern : Quotable Pattern
  ` {{QuotablePattern}} (con c ps) = con₂ (quote Pattern.con) (` c) (` ps)
  ` {{QuotablePattern}} dot = con (quote dot) []
  ` {{QuotablePattern}} (var x) = con₁ (quote Pattern.var) (` x)
  ` {{QuotablePattern}} (lit l) = con₁ (quote Pattern.lit) (` l)
  ` {{QuotablePattern}} (proj f) = con₁ (quote proj) (` f)
  ` {{QuotablePattern}} absurd = con (quote absurd) []

  {-# TERMINATING #-}
  QuotableTerm : Quotable Term
  QuotableClause : Quotable Clause
  QuotableType : Quotable Type
  QuotableSort : Quotable Sort

  ` {{QuotableTerm}} (var x args) = con₂ (quote Term.var) (` x) (` args)
  ` {{QuotableTerm}} (con c args) = con₂ (quote Term.con) (` c) (` args)
  ` {{QuotableTerm}} (def f args) = con₂ (quote def) (` f) (` args)
  ` {{QuotableTerm}} (lam v t) = con₂ (quote lam) (` v) (` t)
  ` {{QuotableTerm}} (pat-lam cs args) = con₂ (quote pat-lam) (` cs) (` args)
  ` {{QuotableTerm}} (pi a b) = con₂ (quote pi) (` a) (` b)
  ` {{QuotableTerm}} (agda-sort s) = con₁ (quote agda-sort) (` s)
  ` {{QuotableTerm}} (lit l) = con₁ (quote Term.lit) (` l)
  ` {{QuotableTerm}} (meta x x₁) = con (quote Term.unknown) []   -- Note: no meta literals (yet)
  ` {{QuotableTerm}} unknown = con (quote Term.unknown) []

  ` {{QuotableType}} (el s v) = con₂ (quote el) (` s) (` v)

  ` {{QuotableSort}} (set t) = con₁ (quote set) (` t)
  ` {{QuotableSort}} (lit n) = con₁ (quote Sort.lit) (` n)
  ` {{QuotableSort}} unknown = con (quote Sort.unknown) []

  ` {{QuotableClause}} (clause x x₁)     = con₂ (quote clause) (` x) (` x₁)
  ` {{QuotableClause}} (absurd-clause x) = con₁ (quote absurd-clause) (` x)
