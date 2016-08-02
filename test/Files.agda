module Files where

open import Prelude
open import System.File
open import System.FilePath
open import Prelude.Equality

fileIsEqual : ∀ {k} → Path k → Path k → IO Unit
fileIsEqual a b = _≟_ <$> readBinaryFile a <*> readBinaryFile b >>= λ x →
  if x then return unit else exitWith (Failure 1)
  where
    -- Move this to Prelude.Equality?
    _≟_ : ∀ {a} {A : Set a} → {{eq : Eq A}} → A → A → Bool
    x ≟ y = isYes (x == y)


main : IO ⊤
main =
  readTextFile fIn >>=
  writeTextFile fTxtOut >>
  readBinaryFile fIn >>=
  writeBinaryFile fBinOut >>
  fileIsEqual fIn fTxtOut >>
  fileIsEqual fIn fBinOut
  where
    fIn = relative "Files.agda"
    fTxtOut = relative "test_files_txt.out"
    fBinOut = relative "test_files_bin.out"

