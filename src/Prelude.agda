module Prelude where

open import Agda.Primitive      public

open import Prelude.Unit        public
open import Prelude.Empty       public
open import Prelude.Function    public
open import Prelude.Char        public
open import Prelude.String      public
open import Prelude.Bool        public
open import Prelude.Nat         public
open import Prelude.Word        public
open import Prelude.Int         public
open import Prelude.Bytes       public
open import Prelude.Product     public
open import Prelude.Sum         public
open import Prelude.List        public
open import Prelude.Maybe       public
open import Prelude.Fin         public
open import Prelude.Vec         public
open import Prelude.Semiring    public
open import Prelude.Number      public
open import Prelude.Fractional  public
open import Prelude.Erased      public
open import Prelude.Strict      public

open import Prelude.Semigroup   public
open import Prelude.Monoid      public
open import Prelude.Equality    public
open import Prelude.Decidable   public
open import Prelude.Functor     public
open import Prelude.Applicative public
open import Prelude.Alternative public
open import Prelude.Monad       public
open import Prelude.Show        public
open import Prelude.Ord         public
open import Prelude.Ord.Reasoning public
open import Prelude.Smashed     public

open import Prelude.IO          public

open import Prelude.Equality.Unsafe  public using (eraseEquality)
open import Prelude.Equality.Inspect public
