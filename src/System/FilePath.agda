module System.FilePath where

open import Prelude.String
  
data Kind : Set where
  Rel : Kind
  Abs : Kind

abstract
  record Path (kind : Kind) : Set where
    constructor mkPath
    field
      path : String

  open import Prelude.Monoid
  open Path

  _//_ : ∀ {k} → Path k → Path Rel → Path k
  x // y = mkPath (path x <> "/" <> path y)

  _∙_ : ∀ {k} → Path k → String → Path k
  p ∙ ext = mkPath (path p <> "." <> ext)

  toString : ∀ {k} → Path k → String
  toString p = path p

  relative : String → Path Rel
  relative = mkPath

  absolute : String → Path Abs
  absolute = mkPath
