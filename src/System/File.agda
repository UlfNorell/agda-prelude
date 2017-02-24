module System.File where

open import System.FilePath
open import Prelude.IO
open import Prelude.String
open import Prelude.Unit
open import Prelude.Function
open import Prelude.Bytes

{-# FOREIGN GHC import qualified Data.Text as Text #-}
{-# FOREIGN GHC import qualified Data.Text.IO as Text #-}
{-# FOREIGN GHC import qualified Data.ByteString as B #-}

private
  module Internal where
    StrFilePath : Set
    StrFilePath = String

    postulate
      readTextFile  : StrFilePath → IO String
      writeTextFile : StrFilePath → String → IO Unit

      readBinaryFile  : StrFilePath → IO Bytes
      writeBinaryFile : StrFilePath → Bytes → IO Unit

    {-# COMPILE GHC readTextFile    = Text.readFile  . Text.unpack #-}
    {-# COMPILE GHC writeTextFile   = Text.writeFile . Text.unpack #-}
    {-# COMPILE GHC readBinaryFile  = B.readFile     . Text.unpack #-}
    {-# COMPILE GHC writeBinaryFile = B.writeFile    . Text.unpack #-}

    {-# COMPILE UHC readTextFile  = UHC.Agda.Builtins.primReadFile  #-}
    {-# COMPILE UHC writeTextFile = UHC.Agda.Builtins.primWriteFile #-}

readTextFile : ∀ {k} → Path k → IO String
readTextFile = Internal.readTextFile ∘ toString

writeTextFile : ∀ {k} → Path k → String → IO Unit
writeTextFile = Internal.writeTextFile ∘ toString

readBinaryFile : ∀ {k} → Path k → IO Bytes
readBinaryFile = Internal.readBinaryFile ∘ toString

writeBinaryFile : ∀ {k} → Path k → Bytes → IO Unit
writeBinaryFile = Internal.writeBinaryFile ∘ toString
