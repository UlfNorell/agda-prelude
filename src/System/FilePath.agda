module System.FilePath where

open import Prelude.String
  
data Kind : Set where
  Rel : Kind
  Abs : Kind

data Target : Set where
  File : Target
  Dir : Target


abstract
  record Path (kind : Kind) (target : Target) : Set where
    constructor mkPath
    field
      path : String

  open import Prelude.Monoid
  open Path

  _/_ : ∀ {k t} → Path k Dir → Path Rel t → Path k t
  x / y = mkPath (path x <> "/" <> path y)

  _∙_ : ∀ {k} → Path k File → String → Path k File
  p ∙ ext = mkPath (path p <> "." <> ext)


  toString : ∀ {a b} → Path a b → String
  toString p = path p


  absoluteDir : String → Path Abs Dir
  absoluteDir = mkPath

  relativeDir : String → Path Rel Dir
  relativeDir = mkPath

  absoluteFile : String → Path Abs File
  absoluteFile = mkPath

  relativeFile : String → Path Rel File
  relativeFile = mkPath

  unsafeFromString : ∀ {k t} → String → Path k t
  unsafeFromString  = mkPath
