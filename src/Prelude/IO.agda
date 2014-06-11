
module Prelude.IO where

open import Prelude.Function
open import Prelude.Functor
open import Prelude.Applicative
open import Prelude.Monad
open import Prelude.List
open import Prelude.String
open import Prelude.Char
open import Prelude.Unit
open import Prelude.Show

{-# IMPORT Agda.FFI #-}

postulate
  IO : ∀ {a} → Set a → Set a

{-# BUILTIN IO IO #-}
{-# COMPILED_TYPE IO Agda.FFI.AgdaIO #-}

postulate
  ioReturn : ∀ {a} {A : Set a} → A → IO A
  ioBind   : ∀ {a b} {A : Set a} {B : Set b} → IO A → (A → IO B) → IO B

{-# COMPILED ioReturn (\ _ _ -> return)    #-}
{-# COMPILED ioBind   (\ _ _ _ _ -> (>>=)) #-}

MonadIO : ∀ {a} → Monad {a} IO
MonadIO = record { return = ioReturn ; _>>=_ = ioBind }

FunctorIO : ∀ {a} → Functor {a} IO
FunctorIO = defaultMonadFunctor

ApplicativeIO : ∀ {a} → Applicative {a} IO
ApplicativeIO = defaultMonadApplicative

--- Terminal IO ---

postulate
  getChar  : IO Char
  putChar  : Char → IO ⊤
  putStr   : String → IO ⊤
  putStrLn : String → IO ⊤

{-# COMPILED getChar getChar   #-}
{-# COMPILED putChar putChar   #-}
{-# COMPILED putStr  putStr    #-}
{-# COMPILED putStrLn putStrLn #-}

print : ∀ {a} {A : Set a} {{ShowA : Show A}} → A → IO ⊤
print = putStrLn ∘ show

--- File IO ---

FilePath = String

postulate
  readFile  : FilePath → IO String
  writeFile : FilePath → String → IO ⊤

{-# COMPILED readFile  readFile  #-}
{-# COMPILED writeFile writeFile #-}
