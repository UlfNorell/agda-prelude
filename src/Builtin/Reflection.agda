
module Builtin.Reflection where

open import Prelude hiding (abs)
open import Prelude.Equality.Unsafe
open import Builtin.Float
open import Container.Traversable
open import Control.Monad.Zero
open import Prelude.Variables

open import Agda.Builtin.Reflection as Builtin
open Builtin public
  hiding ( primQNameEquality
         ; primQNameLess
         ; primShowQName
         ; primMetaEquality
         ; primMetaLess
         ; primShowMeta )

--- Names ---

instance
  ShowName : Show Name
  showsPrec {{ShowName}} _ x = showString (primShowQName x)

instance
  EqName : Eq Name
  _==_ {{EqName}} x y with primQNameEquality x y
  ... | true  = yes unsafeEqual
  ... | false = no unsafeNotEqual

data LessName (x y : Name) : Set where
  less-name : primQNameLess x y ≡ true → LessName x y

private
  cmpName : ∀ x y → Comparison LessName x y
  cmpName x y with inspect (primQNameLess x y)
  ... | true  with≡ eq = less (less-name eq)
  ... | false with≡ _  with inspect (primQNameLess y x)
  ...   | true with≡ eq = greater (less-name eq)
  ...   | false with≡ _ = equal unsafeEqual

instance
  OrdName : Ord Name
  OrdName = defaultOrd cmpName

  OrdLawsName : Ord/Laws Name
  Ord/Laws.super OrdLawsName    = it
  less-antirefl {{OrdLawsName}} (less-name eq) = unsafeNotEqual eq
  less-trans    {{OrdLawsName}} (less-name _)  (less-name _)   = less-name unsafeEqual

--- Meta variables ---

instance
  ShowMeta : Show Meta
  showsPrec {{ShowMeta}} _ x = showString (primShowMeta x)

instance
  EqMeta : Eq Meta
  _==_ {{EqMeta}} x y with primMetaEquality x y
  ... | true  = yes unsafeEqual
  ... | false = no  unsafeNotEqual

data LessMeta (x y : Meta) : Set where
  less-meta : primMetaLess x y ≡ true → LessMeta x y

private
  cmpMeta : ∀ x y → Comparison LessMeta x y
  cmpMeta x y with inspect (primMetaLess x y)
  ... | true  with≡ eq = less (less-meta eq)
  ... | false with≡ _  with inspect (primMetaLess y x)
  ...   | true with≡ eq = greater (less-meta eq)
  ...   | false with≡ _ = equal unsafeEqual

instance
  OrdMeta : Ord Meta
  OrdMeta = defaultOrd cmpMeta

  OrdLawsMeta : Ord/Laws Meta
  Ord/Laws.super OrdLawsMeta = it
  less-antirefl {{OrdLawsMeta}} (less-meta eq) = unsafeNotEqual eq
  less-trans    {{OrdLawsMeta}} (less-meta _)  (less-meta _)   = less-meta unsafeEqual

--- Literals ---

instance
  ShowLiteral : Show Literal
  showsPrec {{ShowLiteral}} _ (nat n)    = shows n
  showsPrec {{ShowLiteral}} _ (word64 n) = shows n
  showsPrec {{ShowLiteral}} _ (float x)  = shows x
  showsPrec {{ShowLiteral}} _ (char c)   = shows c
  showsPrec {{ShowLiteral}} _ (string s) = shows s
  showsPrec {{ShowLiteral}} _ (name x)   = shows x
  showsPrec {{ShowLiteral}} _ (meta x)   = shows x

--- Terms ---

pattern vArg x = arg (arg-info visible relevant) x
pattern hArg x = arg (arg-info hidden relevant) x
pattern iArg x = arg (arg-info instance′ relevant) x

unArg : Arg A → A
unArg (arg _ x) = x

getArgInfo : Arg A → ArgInfo
getArgInfo (arg i _) = i

getVisibility : Arg A → Visibility
getVisibility (arg (arg-info v _) _) = v

getRelevance : Arg A → Relevance
getRelevance (arg (arg-info _ r) _) = r

isVisible : Arg A → Bool
isVisible (arg (arg-info visible _) _) = true
isVisible _ = false

instance
  FunctorArg : Functor {a = ℓ} Arg
  fmap {{FunctorArg}} f (arg i x) = arg i (f x)

  TraversableArg : Traversable {a = ℓ} Arg
  traverse {{TraversableArg}} f (arg i x) = ⦇ (arg i) (f x) ⦈

unAbs : Abs A → A
unAbs (abs _ x) = x

instance
  FunctorAbs : Functor {a = ℓ} Abs
  fmap {{FunctorAbs}} f (abs s x) = abs s (f x)

  TraversableAbs : Traversable {a = ℓ} Abs
  traverse {{TraversableAbs}} f (abs s x) = ⦇ (abs s) (f x) ⦈

absurd-lam : Term
absurd-lam = pat-lam (absurd-clause (("()" , vArg unknown) ∷ []) (vArg (absurd 0) ∷ []) ∷ []) []

--- TC monad ---

mapTC : (A → B) → TC A → TC B
mapTC f m = bindTC m λ x → returnTC (f x)

instance
  FunctorTC : Functor {ℓ} TC
  fmap {{FunctorTC}} = mapTC

  ApplicativeTC : Applicative {ℓ} TC
  pure  {{ApplicativeTC}} = returnTC
  _<*>_ {{ApplicativeTC}} = monadAp bindTC

  MonadTC : Monad {ℓ} TC
  _>>=_  {{MonadTC}} = bindTC

  FunctorTC′ : Functor′ {ℓ₁} {ℓ₂} TC
  fmap′ {{FunctorTC′}} = mapTC

  ApplicativeTC′ : Applicative′ {ℓ₁} {ℓ₂} TC
  _<*>′_ {{ApplicativeTC′}} = monadAp′ bindTC

  MonadTC′ : Monad′ {ℓ₁} {ℓ₂} TC
  _>>=′_ {{MonadTC′}} = bindTC

  FunctorZeroTC : FunctorZero {ℓ} TC
  empty {{FunctorZeroTC}} = typeError []

  AlternativeTC : Alternative {ℓ} TC
  _<|>_ {{AlternativeTC}} = catchTC

Tactic = Term → TC ⊤

give : Term → Tactic
give v = λ hole → unify hole v

define : Arg Name → Type → List Clause → TC ⊤
define f a cs = declareDef f a >> defineFun (unArg f) cs

newMeta : Type → TC Term
newMeta = checkType unknown

newMeta! : TC Term
newMeta! = newMeta unknown

typeErrorS : ∀ {a} {A : Set a} → String → TC A
typeErrorS s = typeError (strErr s ∷ [])

blockOnMeta! : ∀ {a} {A : Set a} → Meta → TC A
blockOnMeta! x = commitTC >>=′ λ _ → blockOnMeta x

inferNormalisedType : Term → TC Type
inferNormalisedType t = withNormalisation true (inferType t)

--- Convenient wrappers ---

-- Zero for non-datatypes
getParameters : Name → TC Nat
getParameters d =
  caseM getDefinition d of λ
  { (data-type n _) → pure n
  ; _ → pure 0 }

getConstructors : Name → TC (List Name)
getConstructors d =
  caseM getDefinition d of λ
  { (data-type _ cs) → pure cs
  ; (record-type c _) → pure (c ∷ [])
  ; _ → typeError (strErr "Cannot get constructors of non-data or record type" ∷ nameErr d ∷ [])
  }

getClauses : Name → TC (List Clause)
getClauses d =
  caseM getDefinition d of λ
  { (function cs) → pure cs
  ; _ → typeError (strErr "Cannot get constructors of non-function type" ∷ nameErr d ∷ [])
  }

-- Get the constructor of a record type (or single-constructor data type)
recordConstructor : Name → TC Name
recordConstructor r =
  caseM getConstructors r of λ
  { (c ∷ []) → pure c
  ; _ → typeError $ strErr "Cannot get constructor of non-record type" ∷ nameErr r ∷ [] }

-- Injectivity of constructors

arg-inj₁ : ∀ {i i′} {x x′ : A} → arg i x ≡ arg i′ x′ → i ≡ i′
arg-inj₁ refl = refl

arg-inj₂ : ∀ {i i′} {x x′ : A} → arg i x ≡ arg i′ x′ → x ≡ x′
arg-inj₂ refl = refl

arg-info-inj₁ : ∀ {v v′ r r′} → arg-info v r ≡ arg-info v′ r′ → v ≡ v′
arg-info-inj₁ refl = refl

arg-info-inj₂ : ∀ {v v′ r r′} → arg-info v r ≡ arg-info v′ r′ → r ≡ r′
arg-info-inj₂ refl = refl

abs-inj₁ : ∀ {s s′} {x x′ : A} → abs s x ≡ abs s′ x′ → s ≡ s′
abs-inj₁ refl = refl

abs-inj₂ : ∀ {s s′} {x x′ : A} → abs s x ≡ abs s′ x′ → x ≡ x′
abs-inj₂ refl = refl

--- Terms ---

var-inj₁ : ∀ {x x′ args args′} → Term.var x args ≡ var x′ args′ → x ≡ x′
var-inj₁ refl = refl

var-inj₂ : ∀ {x x′ args args′} → Term.var x args ≡ var x′ args′ → args ≡ args′
var-inj₂ refl = refl

con-inj₁ : ∀ {c c′ args args′} → Term.con c args ≡ con c′ args′ → c ≡ c′
con-inj₁ refl = refl

con-inj₂ : ∀ {c c′ args args′} → Term.con c args ≡ con c′ args′ → args ≡ args′
con-inj₂ refl = refl

def-inj₁ : ∀ {f f′ args args′} → def f args ≡ def f′ args′ → f ≡ f′
def-inj₁ refl = refl

def-inj₂ : ∀ {f f′ args args′} → def f args ≡ def f′ args′ → args ≡ args′
def-inj₂ refl = refl

meta-inj₁ : ∀ {f f′ args args′} → Term.meta f args ≡ meta f′ args′ → f ≡ f′
meta-inj₁ refl = refl

meta-inj₂ : ∀ {f f′ args args′} → Term.meta f args ≡ meta f′ args′ → args ≡ args′
meta-inj₂ refl = refl

lam-inj₁ : ∀ {v v′ t t′} → lam v t ≡ lam v′ t′ → v ≡ v′
lam-inj₁ refl = refl

lam-inj₂ : ∀ {v v′ t t′} → lam v t ≡ lam v′ t′ → t ≡ t′
lam-inj₂ refl = refl

pat-lam-inj₁ : ∀ {v v′ t t′} → pat-lam v t ≡ pat-lam v′ t′ → v ≡ v′
pat-lam-inj₁ refl = refl

pat-lam-inj₂ : ∀ {v v′ t t′} → pat-lam v t ≡ pat-lam v′ t′ → t ≡ t′
pat-lam-inj₂ refl = refl

pi-inj₁ : ∀ {t₁ t₁′ t₂ t₂′} → pi t₁ t₂ ≡ pi t₁′ t₂′ → t₁ ≡ t₁′
pi-inj₁ refl = refl

pi-inj₂ : ∀ {t₁ t₁′ t₂ t₂′} → pi t₁ t₂ ≡ pi t₁′ t₂′ → t₂ ≡ t₂′
pi-inj₂ refl = refl

sort-inj : ∀ {x y} → agda-sort x ≡ agda-sort y → x ≡ y
sort-inj refl = refl

lit-inj : ∀ {x y} → Term.lit x ≡ lit y → x ≡ y
lit-inj refl = refl

--- Sorts ---

set-inj : ∀ {x y} → set x ≡ set y → x ≡ y
set-inj refl = refl

slit-inj : ∀ {x y} → Sort.lit x ≡ lit y → x ≡ y
slit-inj refl = refl

--- Patterns ---

pcon-inj₁ : ∀ {x y z w} → Pattern.con x y ≡ con z w → x ≡ z
pcon-inj₁ refl = refl

pcon-inj₂ : ∀ {x y z w} → Pattern.con x y ≡ con z w → y ≡ w
pcon-inj₂ refl = refl

pvar-inj : ∀ {x y} → Pattern.var x ≡ var y → x ≡ y
pvar-inj refl = refl

pdot-inj : ∀ {x y} → Pattern.dot x ≡ dot y → x ≡ y
pdot-inj refl = refl

plit-inj : ∀ {x y} → Pattern.lit x ≡ lit y → x ≡ y
plit-inj refl = refl

proj-inj : ∀ {x y} → Pattern.proj x ≡ proj y → x ≡ y
proj-inj refl = refl

absurd-inj : ∀ {x y} → absurd x ≡ absurd y → x ≡ y
absurd-inj refl = refl

--- Clauses ---

clause-inj₁ : ∀ {x y z u v w} → clause x y z ≡ clause u v w → x ≡ u
clause-inj₁ refl = refl

clause-inj₂ : ∀ {x y z u v w} → clause x y z ≡ clause u v w → y ≡ v
clause-inj₂ refl = refl

clause-inj₃ : ∀ {x y z u v w} → clause x y z ≡ clause u v w → z ≡ w
clause-inj₃ refl = refl

absurd-clause-inj₁ : ∀ {x y z w} → absurd-clause x y ≡ absurd-clause z w → x ≡ z
absurd-clause-inj₁ refl = refl

absurd-clause-inj₂ : ∀ {x y z w} → absurd-clause x y ≡ absurd-clause z w → y ≡ w
absurd-clause-inj₂ refl = refl

--- Literals ---

nat-inj : ∀ {x y} → nat x ≡ nat y → x ≡ y
nat-inj refl = refl

word64-inj : ∀ {x y} → word64 x ≡ word64 y → x ≡ y
word64-inj refl = refl

float-inj : ∀ {x y} → float x ≡ float y → x ≡ y
float-inj refl = refl

char-inj : ∀ {x y} → char x ≡ char y → x ≡ y
char-inj refl = refl

string-inj : ∀ {x y} → string x ≡ string y → x ≡ y
string-inj refl = refl

name-inj : ∀ {x y} → name x ≡ name y → x ≡ y
name-inj refl = refl

meta-inj : ∀ {x y} → Literal.meta x ≡ meta y → x ≡ y
meta-inj refl = refl
