-- | NOTE: This module can only represent file paths which are valid strings.
-- On Linux, a file path may be an arbitrary sequence of bytes, but using anything
-- except utf8 for file paths is a terrible idea.
--
-- What should happen if we come across a non utf8 path from an untrusted source?
-- crash -> denial-of-service
-- ignore -> maybe security holes
--
-- Currently, the behaviour for non-textual file paths is undefined.
module System.FilePath where

open import Prelude.Unit
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
