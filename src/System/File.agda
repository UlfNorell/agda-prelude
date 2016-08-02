module System.File where

open import System.FilePath
open import Prelude.IO
open import Prelude.String
open import Prelude.Unit
open import Prelude.Function
open import Prelude.Bytes

{-# IMPORT Data.ByteString #-}

private
  module Internal where
    StrFilePath : Set
    StrFilePath = String
  
    postulate
      readTextFile  : StrFilePath → IO String
      writeTextFile : StrFilePath → String → IO Unit

      readBinaryFile  : StrFilePath → IO Bytes
      writeBinaryFile : StrFilePath → Bytes → IO Unit

    {-# COMPILED readTextFile  Data.Text.IO.readFile  . Data.Text.unpack #-}
    {-# COMPILED writeTextFile Data.Text.IO.writeFile . Data.Text.unpack #-}
    {-# COMPILED readBinaryFile Data.ByteString.readFile . Data.Text.unpack #-}
    {-# COMPILED writeBinaryFile Data.ByteString.writeFile . Data.Text.unpack #-}

    {-# COMPILED_UHC readTextFile  (UHC.Agda.Builtins.primReadFile) #-}
    {-# COMPILED_UHC writeTextFile (UHC.Agda.Builtins.primWriteFile) #-}

readTextFile : ∀ {k} → Path k → IO String
readTextFile = Internal.readTextFile ∘ toString

writeTextFile : ∀ {k} → Path k → String → IO Unit
writeTextFile = Internal.writeTextFile ∘ toString

readBinaryFile : ∀ {k} → Path k → IO Bytes
readBinaryFile = Internal.readBinaryFile ∘ toString

writeBinaryFile : ∀ {k} → Path k → Bytes → IO Unit
writeBinaryFile = Internal.writeBinaryFile ∘ toString
