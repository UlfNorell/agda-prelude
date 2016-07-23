module Files where

open import Prelude
open import System.Files
open import System.FilePath
open import Prelude.Equality

fileIsEqual : ∀ {a b} → Path a File → Path b File → IO Unit
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
    fIn = relativeFile "Files.agda"
    fTxtOut = relativeFile "test_files_txt.out"
    fBinOut = relativeFile "test_files_bin.out"

