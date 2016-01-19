
module Tactic.Reflection.Quote.Class where

open import Builtin.Reflection

record Quotable {a} (A : Set a) : Set a where
  field
    ` : A → Term

open Quotable {{...}} public

