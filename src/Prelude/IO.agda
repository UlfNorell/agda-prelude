
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
open import Prelude.Nat

open import Agda.Builtin.IO public

postulate
  ioReturn : ∀ {a} {A : Set a} → A → IO A
  ioBind   : ∀ {a b} {A : Set a} {B : Set b} → IO A → (A → IO B) → IO B

{-# COMPILED ioReturn (\ _ _ -> return)    #-}
{-# COMPILED ioBind   (\ _ _ _ _ -> (>>=)) #-}

{-# COMPILED_UHC ioReturn (\ _ _ x -> UHC.Agda.Builtins.primReturn x) #-}
{-# COMPILED_UHC ioBind   (\ _ _ _ _ x y -> UHC.Agda.Builtins.primBind x y) #-}

ioMap : ∀ {a b} {A : Set a} {B : Set b} → (A → B) → IO A → IO B
ioMap f m = ioBind m λ x → ioReturn (f x)

instance
  FunctorIO : ∀ {a} → Functor {a} IO
  fmap {{FunctorIO}} = ioMap

  ApplicativeIO : ∀ {a} → Applicative {a} IO
  pure {{ApplicativeIO}} = ioReturn
  _<*>_ {{ApplicativeIO}} = monadAp ioBind
  super ApplicativeIO = it

  MonadIO : ∀ {a} → Monad {a} IO
  _>>=_ {{MonadIO}} = ioBind
  super MonadIO = it

  FunctorIO′ : ∀ {a b} → Functor′ {a} {b} IO
  fmap′ {{FunctorIO′}} = ioMap

  ApplicativeIO′ : ∀ {a b} → Applicative′ {a} {b} IO
  _<*>′_ {{ApplicativeIO′}} = monadAp′ ioBind
  super ApplicativeIO′ = it

  MonadIO′ : ∀ {a b} → Monad′ {a} {b} IO
  _>>=′_ {{MonadIO′}} = ioBind
  super MonadIO′ = it

--- Terminal IO ---

postulate
  getChar  : IO Char
  putChar  : Char → IO Unit
  putStr   : String → IO Unit
  putStrLn : String → IO Unit

{-# IMPORT Data.Text    #-}
{-# IMPORT Data.Text.IO #-}

{-# COMPILED getChar  getChar   #-}
{-# COMPILED putChar  putChar   #-}
{-# COMPILED putStr   Data.Text.IO.putStr   #-}
{-# COMPILED putStrLn Data.Text.IO.putStrLn #-}

{-# COMPILED_UHC putStr   (UHC.Agda.Builtins.primPutStr) #-}
{-# COMPILED_UHC putStrLn (UHC.Agda.Builtins.primPutStrLn) #-}

print : ∀ {a} {A : Set a} {{ShowA : Show A}} → A → IO Unit
print = putStrLn ∘ show

--- Command line arguments ---

{-# IMPORT System.Environment #-}

postulate
  getArgs : IO (List String)
  getProgName : IO String

{-# COMPILED getArgs     fmap (map Data.Text.pack) System.Environment.getArgs #-}
{-# COMPILED getProgName fmap Data.Text.pack System.Environment.getProgName   #-}

--- Misc ---

{-# IMPORT System.Exit #-}

data ExitCode : Set where
  Success : ExitCode
  -- TODO we probably should also enforce an upper limit?
  Failure : (n : Nat) → {p : NonZero n} → ExitCode

private
  {-# HASKELL exitWith' x = System.Exit.exitWith (if x == 0 then System.Exit.ExitSuccess else System.Exit.ExitFailure $ fromInteger x) #-}

  postulate
    exitWith' : Nat → IO Unit
  {-# COMPILED exitWith' exitWith' #-}

exitWith : ExitCode → IO Unit
exitWith Success = exitWith' 0
exitWith (Failure i) = exitWith' i
