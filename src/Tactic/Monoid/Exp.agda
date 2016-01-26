
module Tactic.Monoid.Exp where

open import Prelude
open import Tactic.Reflection.Quote
open import Tactic.Deriving.Quotable

data Exp : Set where
  var : Nat → Exp
  ε : Exp
  _⊕_ : Exp → Exp → Exp

unquoteDecl QuoteExp = deriveQuotable QuoteExp (quote Exp)

flatten : Exp → List Nat
flatten (var x) = x ∷ []
flatten ε = []
flatten (e ⊕ e₁) = flatten e ++ flatten e₁
