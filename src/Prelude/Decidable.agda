
module Prelude.Decidable where

open import Prelude.Empty

data Dec {a} (P : Set a) : Set a where
  yes : P → Dec P
  no  : ¬ P → Dec P

infix 0 ifYes_then_else_
ifYes_then_else_ : ∀ {a b} {A : Set a} {B : Set b} → Dec A → B → B → B
ifYes yes _ then x else _ = x
ifYes no  _ then _ else y = y
