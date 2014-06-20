
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
  IO : Set → Set

{-# BUILTIN IO IO #-}
{-# COMPILED_TYPE IO IO #-}

postulate
  ioReturn : ∀ {A : Set} → A → IO A
  ioBind   : ∀ {A B : Set} → IO A → (A → IO B) → IO B

{-# COMPILED ioReturn (\ _ -> return)    #-}
{-# COMPILED ioBind   (\ _ _ -> (>>=)) #-}

MonadIO : Monad IO
MonadIO = record { return = ioReturn ; _>>=_ = ioBind }

FunctorIO : Functor IO
FunctorIO = defaultMonadFunctor

ApplicativeIO : Applicative IO
ApplicativeIO = defaultMonadApplicative

--- Terminal IO ---

postulate
  getChar  : IO Char
  putChar  : Char → IO Unit
  putStr   : String → IO Unit
  putStrLn : String → IO Unit

{-# COMPILED getChar getChar   #-}
{-# COMPILED putChar putChar   #-}
{-# COMPILED putStr  putStr    #-}
{-# COMPILED putStrLn putStrLn #-}

print : ∀ {a} {A : Set a} {{ShowA : Show A}} → A → IO Unit
print = putStrLn ∘ show

--- File IO ---

FilePath = String

postulate
  readFile  : FilePath → IO String
  writeFile : FilePath → String → IO Unit

{-# COMPILED readFile  readFile  #-}
{-# COMPILED writeFile writeFile #-}

--- Command line arguments ---

{-# IMPORT System.Environment #-}

postulate
  getArgs : IO (List String)
  getProgName : IO String

{-# COMPILED getArgs System.Environment.getArgs #-}
{-# COMPILED getProgName System.Environment.getProgName #-}
