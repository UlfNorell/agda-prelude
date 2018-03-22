
module Prelude.Decidable where

open import Prelude.Empty

data Dec {a} (P : Set a) : Set a where
  yes : P → Dec P
  no  : ¬ P → Dec P

infix 0 ifYes_then_else_ ifNo_then_else_
ifYes_then_else_ : ∀ {a b} {A : Set a} {B : Set b} → Dec A → B → B → B
ifYes yes _ then x else _ = x
ifYes no  _ then _ else y = y

ifNo_then_else_ : ∀ {a b} {A : Set a} {B : Set b} → Dec A → B → B → B
ifNo d then x else y = ifYes d then y else x

FromDec : ∀ {a} {P : Set a} → Dec P → Set a
FromDec {P = P} (yes _) = P
FromDec {P = P} (no  _) = ¬ P

fromDec : ∀ {a} {P : Set a} (d : Dec P) → FromDec d
fromDec (yes x) = x
fromDec (no  x) = x
