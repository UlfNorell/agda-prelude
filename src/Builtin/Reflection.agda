
module Builtin.Reflection where

open import Prelude
open import Prelude.Equality.Unsafe
open import Builtin.Float
open import Data.Traversable

------------------------------------------------------------------------
-- Names

-- Names.

postulate Name : Set

{-# BUILTIN QNAME Name #-}

private
  primitive
    primQNameEquality : Name → Name → Bool
    primQNameLess : Name → Name → Bool
    primShowQName : Name → String

-- Show instance --

instance
  ShowName : Show Name
  ShowName = record { showsPrec = λ _ x → showString (primShowQName x) }

-- Eq instance --

private
  eqName : (x y : Name) → Dec (x ≡ y)
  eqName x y with primQNameEquality x y
  ... | true  = yes unsafeEqual
  ... | false = no  unsafeNotEqual

instance
  EqName : Eq Name
  EqName = record { _==_ = eqName }

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

------------------------------------------------------------------------
-- Meta-variables

postulate Meta : Set

{-# BUILTIN AGDAMETA Meta #-}

private
  primitive
    primMetaEquality : Meta → Meta → Bool
    primMetaLess : Meta → Meta → Bool

-- Show instance --

instance
  ShowMeta : Show Meta
  showsPrec {{ShowMeta}} _ _ = showString "_"

-- Eq instance --

private
  eqMeta : (x y : Meta) → Dec (x ≡ y)
  eqMeta x y with primMetaEquality x y
  ... | true  = yes unsafeEqual
  ... | false = no  unsafeNotEqual

instance
  EqMeta : Eq Meta
  EqMeta = record { _==_ = eqMeta }

data LessMeta (x y : Meta) : Set where
  less-name : primMetaLess x y ≡ true → LessMeta x y

private
  cmpMeta : ∀ x y → Comparison LessMeta x y
  cmpMeta x y with inspect (primMetaLess x y)
  ... | true  with≡ eq = less (less-name eq)
  ... | false with≡ _  with inspect (primMetaLess y x)
  ...   | true with≡ eq = greater (less-name eq)
  ...   | false with≡ _ = equal unsafeEqual

instance
  OrdMeta : Ord Meta
  OrdMeta = defaultOrd cmpMeta

------------------------------------------------------------------------
-- Terms

-- Is the argument visible (explicit), hidden (implicit), or an
-- instance argument?

data Visibility : Set where
  visible hidden instance′ : Visibility

{-# BUILTIN HIDING   Visibility #-}
{-# BUILTIN VISIBLE  visible    #-}
{-# BUILTIN HIDDEN   hidden     #-}
{-# BUILTIN INSTANCE instance′   #-}

-- Arguments can be relevant or irrelevant.

data Relevance : Set where
  relevant irrelevant : Relevance

{-# BUILTIN RELEVANCE  Relevance  #-}
{-# BUILTIN RELEVANT   relevant   #-}
{-# BUILTIN IRRELEVANT irrelevant #-}

-- Arguments.

data ArgInfo : Set where
  arg-info : (v : Visibility) (r : Relevance) → ArgInfo

data Arg (A : Set) : Set where
  arg : (i : ArgInfo) (x : A) → Arg A

pattern vArg x = arg (arg-info visible relevant) x
pattern hArg x = arg (arg-info hidden relevant) x
pattern iArg x = arg (arg-info instance′ relevant) x

{-# BUILTIN ARGINFO    ArgInfo #-}
{-# BUILTIN ARGARGINFO arg-info #-}
{-# BUILTIN ARG        Arg      #-}
{-# BUILTIN ARGARG     arg      #-}

unArg : ∀ {A} → Arg A → A
unArg (arg _ x) = x

instance
  FunctorArg : Functor Arg
  FunctorArg = record { fmap = λ { f (arg i x) → arg i (f x) } }

  TraversableArg : Traversable Arg
  TraversableArg = record { traverse = λ { f (arg i x) → pure (arg i) <*> f x } }

-- Name abstraction.

data Abs (A : Set) : Set where
  abs : (s : String) (x : A) → Abs A

{-# BUILTIN ABS        Abs      #-}
{-# BUILTIN ABSABS     abs      #-}

instance
  FunctorAbs : Functor Abs
  FunctorAbs = record { fmap = λ { f (abs s x) → abs s (f x) } }

  TraversableAbs : Traversable Abs
  TraversableAbs = record { traverse = λ { f (abs s x) → pure (abs s) <*> f x } }

-- Literals.

data Literal : Set where
  nat    : Nat    → Literal
  float  : Float  → Literal
  char   : Char   → Literal
  string : String → Literal
  name   : Name   → Literal

{-# BUILTIN AGDALITERAL   Literal #-}
{-# BUILTIN AGDALITNAT    nat #-}
{-# BUILTIN AGDALITFLOAT  float #-}
{-# BUILTIN AGDALITCHAR   char #-}
{-# BUILTIN AGDALITSTRING string #-}
{-# BUILTIN AGDALITQNAME  name #-}

-- Terms.

mutual
  data Term : Set where
    var           : (x : Nat) (args : List (Arg Term)) → Term
    con           : (c : Name) (args : List (Arg Term)) → Term
    def           : (f : Name) (args : List (Arg Term)) → Term
    lam           : (v : Visibility) (t : Abs Term) → Term
    pat-lam       : (cs : List Clause) (args : List (Arg Term)) → Term
    pi            : (a : Arg Type) (b : Abs Type) → Term
    agda-sort     : (s : Sort) → Term
    lit           : (l : Literal) → Term
    meta          : (x : Meta) → List (Arg Term) → Term
    unknown       : Term

  data Type : Set where
    el : (s : Sort) (t : Term) → Type

  data Sort : Set where
    set     : (t : Term) → Sort
    lit     : (n : Nat) → Sort
    unknown : Sort

  data Pattern : Set where
    con    : Name → List (Arg Pattern) → Pattern
    dot    : Pattern
    var    : (s : String) → Pattern
    lit    : Literal → Pattern
    proj   : Name → Pattern
    absurd : Pattern

  data Clause : Set where
    clause : List (Arg Pattern) → Term → Clause
    absurd-clause : List (Arg Pattern) → Clause

unEl : Type → Term
unEl (el _ v) = v

absurd-lam : Term
absurd-lam = pat-lam (absurd-clause (vArg absurd ∷ []) ∷ []) []

{-# BUILTIN AGDASORT            Sort    #-}
{-# BUILTIN AGDATYPE            Type    #-}
{-# BUILTIN AGDATERM            Term    #-}
{-# BUILTIN AGDAPATTERN   Pattern #-}
{-# BUILTIN AGDACLAUSE       Clause        #-}

{-# BUILTIN AGDATERMVAR         var     #-}
{-# BUILTIN AGDATERMCON         con     #-}
{-# BUILTIN AGDATERMDEF         def     #-}
{-# BUILTIN AGDATERMMETA        meta    #-}
{-# BUILTIN AGDATERMLAM         lam     #-}
{-# BUILTIN AGDATERMEXTLAM      pat-lam #-}
{-# BUILTIN AGDATERMPI          pi      #-}
{-# BUILTIN AGDATERMSORT        agda-sort #-}
{-# BUILTIN AGDATERMLIT         lit     #-}
{-# BUILTIN AGDATERMUNSUPPORTED unknown #-}
{-# BUILTIN AGDATYPEEL          el      #-}
{-# BUILTIN AGDASORTSET         set     #-}
{-# BUILTIN AGDASORTLIT         lit     #-}
{-# BUILTIN AGDASORTUNSUPPORTED unknown #-}

{-# BUILTIN AGDAPATCON    con     #-}
{-# BUILTIN AGDAPATDOT    dot     #-}
{-# BUILTIN AGDAPATVAR    var     #-}
{-# BUILTIN AGDAPATLIT    lit     #-}
{-# BUILTIN AGDAPATPROJ   proj    #-}
{-# BUILTIN AGDAPATABSURD absurd  #-}

{-# BUILTIN AGDACLAUSECLAUSE clause        #-}
{-# BUILTIN AGDACLAUSEABSURD absurd-clause #-}

------------------------------------------------------------------------
-- Definitions

data Function : Set where
  fun-def : Type → List Clause → Function

{-# BUILTIN AGDAFUNDEF    Function #-}
{-# BUILTIN AGDAFUNDEFCON fun-def #-}

postulate
  DataType : Set
  Record   : Set

{-# BUILTIN AGDADATADEF   DataType #-}
{-# BUILTIN AGDARECORDDEF Record    #-}

-- Definitions.

private
  data Def : Set where
    function     : Function  → Def
    data-type    : DataType → Def
    record′      : Record    → Def
    constructor′ : Def
    axiom        : Def
    primitive′   : Def

{-# BUILTIN AGDADEFINITION                Def   #-}
{-# BUILTIN AGDADEFINITIONFUNDEF          function     #-}
{-# BUILTIN AGDADEFINITIONDATADEF         data-type    #-}
{-# BUILTIN AGDADEFINITIONRECORDDEF       record′      #-}
{-# BUILTIN AGDADEFINITIONDATACONSTRUCTOR constructor′ #-}
{-# BUILTIN AGDADEFINITIONPOSTULATE       axiom        #-}
{-# BUILTIN AGDADEFINITIONPRIMITIVE       primitive′   #-}

------------------------------------------------------------------------
-- TC monad

postulate
  TC         : ∀ {a} → Set a → Set a
  returnTC   : ∀ {a} {A : Set a} → A → TC A
  bindTC     : ∀ {a b} {A : Set a} {B : Set b} → TC A → (A → TC B) → TC B
  unify      : Term → Term → TC ⊤
  newMeta    : Type → TC Term
  typeError  : ∀ {a} {A : Set a} → String → TC A
  inferType  : Term → TC Type
  checkType  : Term → Type → TC Term
  normalise  : Term → TC Term
  catchTC    : ∀ {a} {A : Set a} → TC A → TC A → TC A
  getContext : TC (List (Arg Type))
  extendContext : ∀ {a} {A : Set a} → Arg Type → TC A → TC A
  inContext     : ∀ {a} {A : Set a} → List (Arg Type) → TC A → TC A
  freshName  : String → TC Name
  declareDef : Name → Type → TC ⊤
  defineFun  : Name → List Clause → TC ⊤
  getType    : Name → TC Type
  getDef     : Name → TC Def
  numberOfParameters : DataType → TC Nat
  getConstructors    : DataType  → TC (List Name)
  blockOnMeta : ∀ {a} {A : Set a} → Meta → TC A

{-# BUILTIN AGDATCM           TC         #-}
{-# BUILTIN AGDATCMRETURN     returnTC   #-}
{-# BUILTIN AGDATCMBIND       bindTC     #-}
{-# BUILTIN AGDATCMUNIFY      unify      #-}
{-# BUILTIN AGDATCMNEWMETA    newMeta    #-}
{-# BUILTIN AGDATCMTYPEERROR  typeError  #-}
{-# BUILTIN AGDATCMINFERTYPE  inferType  #-}
{-# BUILTIN AGDATCMCHECKTYPE  checkType  #-}
{-# BUILTIN AGDATCMNORMALISE  normalise  #-}
{-# BUILTIN AGDATCMCATCHERROR catchTC    #-}
{-# BUILTIN AGDATCMGETCONTEXT getContext #-}
{-# BUILTIN AGDATCMEXTENDCONTEXT extendContext #-}
{-# BUILTIN AGDATCMINCONTEXT  inContext #-}
{-# BUILTIN AGDATCMFRESHNAME  freshName #-}
{-# BUILTIN AGDATCMDECLAREDEF declareDef #-}
{-# BUILTIN AGDATCMDEFINEFUN  defineFun #-}
{-# BUILTIN AGDATCMGETTYPE getType #-}
{-# BUILTIN AGDATCMGETDEFINITION getDef #-}
{-# BUILTIN AGDATCMNUMBEROFPARAMETERS numberOfParameters #-}
{-# BUILTIN AGDATCMGETCONSTRUCTORS getConstructors #-}
{-# BUILTIN AGDATCMBLOCKONMETA blockOnMeta #-}

instance
  MonadTC : ∀ {a} → Monad {a} TC
  return {{MonadTC}} = returnTC
  _>>=_  {{MonadTC}} = bindTC

  ApplicativeTC : ∀ {a} → Applicative {a} TC
  ApplicativeTC = defaultMonadApplicative

  FunctorTC : ∀ {a} → Functor {a} TC
  FunctorTC = defaultMonadFunctor

  PMonadTC : ∀ {a b} → PMonad {a} {b} TC
  _>>=′_ {{PMonadTC}} = bindTC

Tactic = Term → TC ⊤

give : Term → Tactic
give v = λ hole → unify hole v

define : Name → Function → TC ⊤
define f (fun-def a cs) = declareDef f a >> defineFun f cs

------------------------------------------------------------------------
-- Convenient wrappers

data Definition : Set where
  function    : Function  → Definition
  data-type   : (pars : Nat) (cs : List Name) → Definition
  record-type : Record → Definition
  data-cons   : (d : Name) → Definition
  axiom       : Definition
  prim-fun    : Definition

private
  data BadConstructorType : Set where

  bad = quote BadConstructorType

  conData : Name → TC Name
  conData = λ c → getTData <$> getType c
    where
      getTData : Type → Name
      getData : Term → Name
      getData (def d _)        = d
      getData (pi a (abs _ b)) = getTData b
      getData _         = bad
      getTData (el _ b) = getData b

  makeDef : Name → Def → TC Definition
  makeDef _ (function x)  = pure (function x)
  makeDef _ (data-type x) = data-type <$> numberOfParameters x <*> getConstructors x
  makeDef _ axiom         = pure axiom
  makeDef _ (record′ x)   = pure (record-type x)
  makeDef c constructor′  = data-cons <$> conData c
  makeDef _ primitive′    = pure prim-fun

getDefinition : Name → TC Definition
getDefinition f = makeDef f =<< getDef f

-- Zero for non-datatypes
getParameters : Name → TC Nat
getParameters d =
  getDef d >>= λ
  { (data-type d) → numberOfParameters d
  ; _ → pure 0 }

-- Injectivity of constructors

arg-inj₁ : ∀ {A i i′} {x x′ : A} → arg i x ≡ arg i′ x′ → i ≡ i′
arg-inj₁ refl = refl

arg-inj₂ : ∀ {A i i′} {x x′ : A} → arg i x ≡ arg i′ x′ → x ≡ x′
arg-inj₂ refl = refl

arg-info-inj₁ : ∀ {v v′ r r′} → arg-info v r ≡ arg-info v′ r′ → v ≡ v′
arg-info-inj₁ refl = refl

arg-info-inj₂ : ∀ {v v′ r r′} → arg-info v r ≡ arg-info v′ r′ → r ≡ r′
arg-info-inj₂ refl = refl

abs-inj₁ : ∀ {A s s′} {x x′ : A} → abs s x ≡ abs s′ x′ → s ≡ s′
abs-inj₁ refl = refl

abs-inj₂ : ∀ {A s s′} {x x′ : A} → abs s x ≡ abs s′ x′ → x ≡ x′
abs-inj₂ refl = refl

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

meta-inj₁ : ∀ {f f′ args args′} → meta f args ≡ meta f′ args′ → f ≡ f′
meta-inj₁ refl = refl

meta-inj₂ : ∀ {f f′ args args′} → meta f args ≡ meta f′ args′ → args ≡ args′
meta-inj₂ refl = refl

lam-inj₁ : ∀ {v v′ t t′} → lam v t ≡ lam v′ t′ → v ≡ v′
lam-inj₁ refl = refl

lam-inj₂ : ∀ {v v′ t t′} → lam v t ≡ lam v′ t′ → t ≡ t′
lam-inj₂ refl = refl

pi-inj₁ : ∀ {t₁ t₁′ t₂ t₂′} → pi t₁ t₂ ≡ pi t₁′ t₂′ → t₁ ≡ t₁′
pi-inj₁ refl = refl

pi-inj₂ : ∀ {t₁ t₁′ t₂ t₂′} → pi t₁ t₂ ≡ pi t₁′ t₂′ → t₂ ≡ t₂′
pi-inj₂ refl = refl

sort-inj : ∀ {x y} → agda-sort x ≡ agda-sort y → x ≡ y
sort-inj refl = refl

lit-inj : ∀ {x y} → Term.lit x ≡ lit y → x ≡ y
lit-inj refl = refl

set-inj : ∀ {x y} → set x ≡ set y → x ≡ y
set-inj refl = refl

slit-inj : ∀ {x y} → Sort.lit x ≡ lit y → x ≡ y
slit-inj refl = refl

el-inj₁ : ∀ {s s′ t t′} → el s t ≡ el s′ t′ → s ≡ s′
el-inj₁ refl = refl

el-inj₂ : ∀ {s s′ t t′} → el s t ≡ el s′ t′ → t ≡ t′
el-inj₂ refl = refl

nat-inj : ∀ {x y} → nat x ≡ nat y → x ≡ y
nat-inj refl = refl

float-inj : ∀ {x y} → float x ≡ float y → x ≡ y
float-inj refl = refl

char-inj : ∀ {x y} → char x ≡ char y → x ≡ y
char-inj refl = refl

string-inj : ∀ {x y} → string x ≡ string y → x ≡ y
string-inj refl = refl

name-inj : ∀ {x y} → name x ≡ name y → x ≡ y
name-inj refl = refl
