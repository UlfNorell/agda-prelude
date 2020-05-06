{-

Constructing List ErrorPart from format strings. Supported formats

  %s : String
  %d : Nat
  %t : Term
  %n : Name
  %e : List ErrorPart

 Examples at the bottom.

-}
module Tactic.Reflection.Printf where

open import Prelude
open import Prelude.Variables
open import Builtin.Reflection

private

  data Format (A : Set) : Set where
    fmtLit  : A → Format A
    fmtStr  : Format A
    fmtNat  : Format A
    fmtTerm : Format A
    fmtName : Format A
    fmtErrs : Format A

  instance
    FunctorFormat : Functor Format
    FunctorFormat .fmap f (fmtLit x) = fmtLit (f x)
    FunctorFormat .fmap f fmtStr = fmtStr
    FunctorFormat .fmap f fmtNat = fmtNat
    FunctorFormat .fmap f fmtTerm = fmtTerm
    FunctorFormat .fmap f fmtName = fmtName
    FunctorFormat .fmap f fmtErrs = fmtErrs

  parseFormat : String → List (Format String)
  parseFormat = map (fmap packString) ∘ parse ∘ unpackString
    where
      cons : Char → List (Format (List Char)) → List (Format (List Char))
      cons c (fmtLit cs ∷ fs) = fmtLit (c ∷ cs) ∷ fs
      cons c fs = fmtLit [ c ] ∷ fs

      parse : List Char → List (Format (List Char))
      parse ('%' ∷ 's' ∷ fmt) = fmtStr  ∷ parse fmt
      parse ('%' ∷ 'd' ∷ fmt) = fmtNat  ∷ parse fmt
      parse ('%' ∷ 't' ∷ fmt) = fmtTerm ∷ parse fmt
      parse ('%' ∷ 'n' ∷ fmt) = fmtName ∷ parse fmt
      parse ('%' ∷ 'e' ∷ fmt) = fmtErrs ∷ parse fmt
      parse ('%' ∷ '%' ∷ fmt) = cons '%' (parse fmt)
      parse (c ∷ fmt)         = cons c (parse fmt)
      parse []                = []

  FormatErrorType : List (Format String) → Set ℓ → Set ℓ
  FormatErrorType [] Res = Res
  FormatErrorType (fmtLit _ ∷ fs) Res = FormatErrorType fs Res
  FormatErrorType (fmtStr   ∷ fs) Res = String         → FormatErrorType fs Res
  FormatErrorType (fmtNat   ∷ fs) Res = Nat            → FormatErrorType fs Res
  FormatErrorType (fmtTerm  ∷ fs) Res = Term           → FormatErrorType fs Res
  FormatErrorType (fmtName  ∷ fs) Res = Name           → FormatErrorType fs Res
  FormatErrorType (fmtErrs  ∷ fs) Res = List ErrorPart → FormatErrorType fs Res

-- Exported for library writers
formatError : (List ErrorPart → A) → (fmt : String) → FormatErrorType (parseFormat fmt) A
formatError {A = A} k = format [] ∘ parseFormat
  where
    format : List ErrorPart → (fmt : List (Format String)) → FormatErrorType fmt A
    format acc [] = k (reverse acc)
    format acc (fmtLit s ∷ fmt)   = format (strErr s        ∷ acc) fmt
    format acc (fmtStr   ∷ fmt) s = format (strErr s        ∷ acc) fmt
    format acc (fmtNat   ∷ fmt) n = format (strErr (show n) ∷ acc) fmt
    format acc (fmtTerm  ∷ fmt) t = format (termErr t       ∷ acc) fmt
    format acc (fmtName  ∷ fmt) x = format (nameErr x       ∷ acc) fmt
    format acc (fmtErrs  ∷ fmt) e = format (reverse e      ++ acc) fmt

-- Public API --

errorPartsFmt : (fmt : String) → FormatErrorType (parseFormat fmt) (List ErrorPart)
errorPartsFmt = formatError id

typeErrorFmt : (fmt : String) → FormatErrorType (parseFormat fmt) (TC A)
typeErrorFmt = formatError typeError

debugPrintFmt : String → Nat → (fmt : String) → FormatErrorType (parseFormat fmt) (TC ⊤)
debugPrintFmt tag lvl = formatError (debugPrint tag lvl)

-- Examples --

private

  _ : Name → Term → List ErrorPart
  _ = errorPartsFmt "%n : %t"

  _ : Name → Nat → Nat → TC A
  _ = typeErrorFmt "%n applied to %d arguments, expected %d"

  _ : Term → String → TC ⊤
  _ = debugPrintFmt "tactic.foo" 10 "solving %t with %s"
