
module Data.Reflect.Quote where

open import Prelude
open import Data.Reflect

record Quotable {a} (A : Set a) : Set a where
  field
    ` : A → Term

open Quotable {{...}}

--- Instances ---

-- Nat --

pattern `zero  = con (quote Nat.zero) []
pattern `suc n = con (quote Nat.suc) (vArg n ∷ [])

QuotableNat : Quotable Nat
QuotableNat = record { ` = quoteNat }
  where
    quoteNat : Nat → Term
    quoteNat zero    = `zero
    quoteNat (suc n) = `suc (quoteNat n)

-- Bool --

pattern `true  = con (quote true) []
pattern `false = con (quote false) []

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

QuotableList : ∀ {a} {A : Set a} {{QuotableA : Quotable A}} → Quotable (List A)
QuotableList = record { ` = quoteList }
  where
    quoteList : List _ → Term
    quoteList [] = `[]
    quoteList (x ∷ xs) = ` x `∷ quoteList xs

-- Maybe --

pattern `nothing = con (quote nothing) []
pattern `just x  = con (quote just) (vArg x ∷ [])

QuotableMaybe : ∀ {a} {A : Set a} {{QuotableA : Quotable A}} → Quotable (Maybe A)
QuotableMaybe = record { ` = quoteMaybe }
  where
    quoteMaybe : Maybe _ → Term
    quoteMaybe nothing  = `nothing
    quoteMaybe (just x) = `just (` x)

-- Either --

pattern `left  x = con (quote left)  (vArg x ∷ [])
pattern `right x = con (quote right) (vArg x ∷ [])

QuotableEither : ∀ {a b} {A : Set a} {B : Set b} {{QuotableA : Quotable A}} {{QuotableB : Quotable B}} →
                   Quotable (Either A B)
QuotableEither = record { ` = quoteEither }
  where
    quoteEither : Either _ _ → Term
    quoteEither (left x)  = `left  (` x)
    quoteEither (right x) = `right (` x)

-- Sigma --

pattern _`,_ x y = con (quote _,_) (vArg x ∷ vArg y ∷ [])

QuotableSigma : ∀ {a b} {A : Set a} {B : A → Set b}
                  {{QuotableA : Quotable A}} {{QuotableB : ∀ {x} → Quotable (B x)}} →
                  Quotable (Σ A B)
QuotableSigma = record { ` = quoteSigma }
  where
    quoteSigma : Σ _ _ → Term
    quoteSigma (x , y) = ` x `, ` y
