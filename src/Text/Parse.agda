
module Text.Parse {t} (Tok : Set t) where

open import Prelude
open import Data.Monoid

private
  data P′ {a} (A : Set a) : Set (a ⊔ t) where
    symbolBind : (Tok → P′ A) → P′ A
    fail′ : P′ A
    returnPlus : A → P′ A → P′ A

  _+++′_ : ∀ {a} {A : Set a} → P′ A → P′ A → P′ A
  symbolBind f   +++′ symbolBind g   = symbolBind λ x → f x +++′ g x
  fail′          +++′ q              = q
  p              +++′ fail′          = p
  returnPlus x p +++′ q              = returnPlus x (p +++′ q)
  p              +++′ returnPlus x q = returnPlus x (p +++′ q)

  parse′ : ∀ {a} {A : Set a} → P′ A → List Tok → List (A × List Tok)
  parse′ (symbolBind _) [] = []
  parse′ (symbolBind f) (c ∷ s) = parse′ (f c) s
  parse′ (returnPlus x p) s = (x , s) ∷ parse′ p s
  parse′ fail′ xs = []

record P {a} (A : Set a) : Set (lsuc a ⊔ t) where
  constructor mkP
  field
    unP : {B : Set a} → (A → P′ B) → P′ B

open P

symbol : P Tok
symbol = mkP symbolBind

fail : ∀ {a} {A : Set a} → P A
fail = mkP λ _ → fail′

infixr 2 _+++_
_+++_ : ∀ {a} {A : Set a} → P A → P A → P A
p +++ q = mkP λ k → unP p k +++′ unP q k

private
  ret : ∀ {a} {A : Set a} → A → P A
  ret x = mkP λ k → k x

  bind : ∀ {a} {A B : Set a} → P A → (A → P B) → P B
  bind p f = mkP λ k → unP p (λ x → unP (f x) k)

parse : ∀ {a} {A : Set a} → P A → List Tok → List (A × List Tok)
parse p = parse′ (unP p (λ x → returnPlus x fail′))

parse! : ∀ {a} {A : Set a} → P A → List Tok → Maybe A
parse! p s with filter (null ∘ snd) (parse p s)
... | []          = nothing
... | (x , _) ∷ _ = just x

--- Instances ---

MonadP : ∀ {a} → Monad {a} P
MonadP = record { return = ret ; _>>=_ = bind }

ApplicativeP : ∀ {a} → Applicative {a} P
ApplicativeP = defaultMonadApplicative

FunctorP : ∀ {a} → Functor {a} P
FunctorP = defaultMonadFunctor

MonoidP : ∀ {a} {A : Set a} → Monoid (P A)
MonoidP = record { mempty = fail ; _<>_ = _+++_ }

--- Derived combinators ---

sat : (p : Tok → Bool) → P (Σ Tok (IsTrue ∘ p))
sat p = symbol >>= match
  where
    -- Inlining 'match' gives internal error!
    match : Tok → P (Σ Tok (IsTrue ∘ p))
    match t = if′ p t then (λ {{prf}} → return (t , prf)) else fail
    -- match t = if′ p t then return (t , ⋯) else fail  -- instance search takes a long time here!

sat! : (Tok → Bool) →  P Tok
sat! p = fst <$> sat p

this : {{EqTok : Eq Tok}} → Tok → P Tok
this t = sat! (isYes ∘ _==_ t)

{-# NO_TERMINATION_CHECK #-}
many many₁ : ∀ {a} {A : Set a} → P A → P (List A)
many  p = return [] +++ many₁ p
many₁ p = _∷_ <$> p <*> many p
