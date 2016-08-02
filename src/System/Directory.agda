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


abstract

  listContents : ∀ {k} → Path k → IO (List (Path k))
  listContents p = fmap (p //_ ∘ relative) <$> Internal.listContents (toString p)
