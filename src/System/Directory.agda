module System.Directory where

open import System.FilePath
open import Prelude
open import Container.Traversable

{-# IMPORT System.Directory #-}


private
  module Internal where
    postulate
      listContents : String → IO (List String)
      doesFileExist : String → IO Bool
    {-# COMPILED listContents System.Directory.getDirectoryContents #-}
    {-# COMPILED doesFileExist System.Directory.doesFileExist #-}


-- A path not indexed by target.
T-Path : (k : Kind) → Set
T-Path k = Σ Target (Path k)

abstract
  record BarePath (k : Kind) : Set where
    constructor mkBarePath
    field path : String

  listContents' : ∀ {k} → Path k Dir → IO (List (BarePath k))
  listContents' p = fmap (mkBarePath ∘ ((toString p <> "/") <>_)) <$> Internal.listContents (toString p)

  stat : ∀ {k} → BarePath k → IO (T-Path k)
  stat p = caseF Internal.doesFileExist (BarePath.path p) of (λ
    { false → Dir , (unsafeFromString (BarePath.path p))
    ; true → File , (unsafeFromString (BarePath.path p)) })


  listContents : ∀ {k} → Path k Dir → IO (List (T-Path k))
  listContents p = listContents' p >>= traverse stat
