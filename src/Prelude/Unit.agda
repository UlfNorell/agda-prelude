
module Prelude.Unit where

open import Agda.Builtin.Unit public

record ⊤′ {a} : Set a where
  instance constructor tt

-- To keep changes from compat-2.4.0 to a minimum.
Unit = ⊤
pattern unit = tt
