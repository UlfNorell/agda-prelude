
module Prelude.Monad where

open import Agda.Primitive
open import Prelude.Function
open import Prelude.Functor
open import Prelude.Unit
open import Prelude.Applicative

open import Prelude.Monad.Indexed {I = ⊤} as Indexed

Monad : ∀ {a b} (M : Set a → Set b) → Set (lsuc a ⊔ b)
Monad M = Indexed.IMonad (λ _ _ → M)

Monad′ : ∀ {a b} (M : ∀ {a} → Set a → Set a) → Set (lsuc (a ⊔ b))
Monad′ {a} {b} M = Indexed.IMonad′ {a = a} {b = b} (λ _ _ → M)

open Indexed public hiding (IMonad; IMonad′)

monadAp : ∀ {a b} {A B : Set a} {M : Set a → Set b}
            {{_ : Functor M}} →
            (M (A → B) → ((A → B) → M B) → M B) →
            M (A → B) → M A → M B
monadAp _>>=_ mf mx = mf >>= λ f → fmap f mx

monadAp′ : ∀ {a b} {A : Set a} {B : Set b} {M : ∀ {a} → Set a → Set a}
             {{_ : Functor′ {a} {b} M}} →
            (M (A → B) → ((A → B) → M B) → M B) →
            M (A → B) → M A → M B
monadAp′ _>>=_ mf mx = mf >>= λ f → fmap′ f mx

infixr 0 caseM_of_
caseM_of_ = _>>=_
