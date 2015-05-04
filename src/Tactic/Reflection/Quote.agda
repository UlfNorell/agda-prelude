
module Tactic.Reflection.Quote where

open import Prelude
open import Builtin.Reflection

record Quotable {a} (A : Set a) : Set a where
  field
    ` : A → Term

open Quotable {{...}} public

--- Instances ---

-- Nat --

pattern `zero  = con (quote Nat.zero) []
pattern `suc n = con (quote Nat.suc) (vArg n ∷ [])

instance
  QuotableNat : Quotable Nat
  QuotableNat = record { ` = λ n → lit (nat n) }

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
  QuotableName = record { ` = λ x → lit (name x) }

-- Term --

instance
  QuotableTerm : Quotable Term
  QuotableTerm = record { ` = quote-term }  -- cheating a little