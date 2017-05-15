
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

{-# COMPILE GHC ioReturn = (\ _ _ -> return)    #-}
{-# COMPILE GHC ioBind =   (\ _ _ _ _ -> (>>=)) #-}

{-# COMPILE UHC ioReturn = (\ _ _ x -> UHC.Agda.Builtins.primReturn x) #-}
{-# COMPILE UHC ioBind =   (\ _ _ _ _ x y -> UHC.Agda.Builtins.primBind x y) #-}

ioMap : ∀ {a b} {A : Set a} {B : Set b} → (A → B) → IO A → IO B
ioMap f m = ioBind m λ x → ioReturn (f x)

instance
  FunctorIO : ∀ {a} → Functor {a} IO
  fmap {{FunctorIO}} = ioMap

  ApplicativeIO : ∀ {a} → Applicative {a} IO
  pure {{ApplicativeIO}} = ioReturn
  _<*>_ {{ApplicativeIO}} = monadAp ioBind

  MonadIO : ∀ {a} → Monad {a} IO
  _>>=_ {{MonadIO}} = ioBind

  FunctorIO′ : ∀ {a b} → Functor′ {a} {b} IO
  fmap′ {{FunctorIO′}} = ioMap

  ApplicativeIO′ : ∀ {a b} → Applicative′ {a} {b} IO
  _<*>′_ {{ApplicativeIO′}} = monadAp′ ioBind

  MonadIO′ : ∀ {a b} → Monad′ {a} {b} IO
  _>>=′_ {{MonadIO′}} = ioBind

--- Terminal IO ---

postulate
  getChar  : IO Char
  putChar  : Char → IO Unit
  putStr   : String → IO Unit
  putStrLn : String → IO Unit

{-# FOREIGN GHC import qualified Data.Text    as Text #-}
{-# FOREIGN GHC import qualified Data.Text.IO as Text #-}

{-# COMPILE GHC getChar =  getChar   #-}
{-# COMPILE GHC putChar =  putChar   #-}
{-# COMPILE GHC putStr =   Text.putStr   #-}
{-# COMPILE GHC putStrLn = Text.putStrLn #-}

{-# COMPILE UHC putStr =   (UHC.Agda.Builtins.primPutStr) #-}
{-# COMPILE UHC putStrLn = (UHC.Agda.Builtins.primPutStrLn) #-}

print : ∀ {a} {A : Set a} {{ShowA : Show A}} → A → IO Unit
print = putStrLn ∘ show

--- Command line arguments ---

{-# FOREIGN GHC import System.Environment (getArgs, getProgName) #-}

postulate
  getArgs : IO (List String)
  getProgName : IO String

{-# COMPILE GHC getArgs =     fmap (map Text.pack) getArgs #-}
{-# COMPILE GHC getProgName = fmap Text.pack getProgName   #-}

--- Misc ---

{-# FOREIGN GHC import System.Exit #-}

data ExitCode : Set where
  Success : ExitCode
  -- TODO we probably should also enforce an upper limit?
  Failure : (n : Nat) → {p : NonZero n} → ExitCode

private
  {-# FOREIGN GHC exitWith' x = exitWith (if x == 0 then ExitSuccess else ExitFailure $ fromInteger x) #-}

  postulate
    exitWith' : ∀ {a} {A : Set a} → Nat → IO A
  {-# COMPILE GHC exitWith' = \ _ _ -> exitWith' #-}

exitWith : ∀ {a} {A : Set a} → ExitCode → IO A
exitWith Success = exitWith' 0
exitWith (Failure i) = exitWith' i
