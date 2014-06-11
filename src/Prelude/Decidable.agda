
module Prelude.Decidable where

open import Prelude.Empty

data Dec {a} (P : Set a) : Set a where
  yes : P → Dec P
  no  : ¬ P → Dec P
