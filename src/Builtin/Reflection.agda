
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
  primitive primQNameEquality : Name → Name → Bool

-- Eq instance --

private
  eqName : (x y : Name) → Dec (x ≡ y)
  eqName x y with primQNameEquality x y
  ... | true  = yes unsafeEqual
  ... | false = no  unsafeNotEqual

instance
  EqName : Eq Name
  EqName = record { _==_ = eqName }

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
    sort          : (s : Sort) → Term
    lit           : (l : Literal) → Term
    quote-goal    : (t : Abs Term) → Term
    quote-term    : (t : Term) → Term
    quote-context : Term
    unquote-term  : (t : Term) (args : List (Arg Term)) → Term
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
{-# BUILTIN AGDATERMLAM         lam     #-}
{-# BUILTIN AGDATERMEXTLAM      pat-lam #-}
{-# BUILTIN AGDATERMPI          pi      #-}
{-# BUILTIN AGDATERMSORT        sort    #-}
{-# BUILTIN AGDATERMLIT         lit     #-}
{-# BUILTIN AGDATERMQUOTETERM    quote-term    #-}
{-# BUILTIN AGDATERMQUOTEGOAL    quote-goal    #-}
{-# BUILTIN AGDATERMQUOTECONTEXT quote-context #-}
{-# BUILTIN AGDATERMUNQUOTE      unquote-term  #-}
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

data Definition : Set where
  function    : Function  → Definition
  data-type   : (pars : Nat) (cs : List Name) → Definition
  record-type : Record → Definition
  data-cons   : (d : Name) → Definition
  axiom       : Definition
  prim-fun    : Definition

private
  primitive
    primQNameType        : Name → Type
    primQNameDefinition  : Name → Def
    primDataConstructors : DataType → List Name
    primDataNumberOfParameters : DataType → Nat

private
  data BadConstructorType : Set where

  bad = quote BadConstructorType

  conData : Name → Name
  conData = getTData ∘ primQNameType
    where
      getTData : Type → Name
      getData : Term → Name
      getData (def d _)        = d
      getData (pi a (abs _ b)) = getTData b
      getData _         = bad
      getTData (el _ b) = getData b

  makeDef : Name → Def → Definition
  makeDef _ (function x)  = function x
  makeDef _ (data-type x) = data-type (primDataNumberOfParameters x) (primDataConstructors x)
  makeDef _ axiom         = axiom
  makeDef _ (record′ x)   = record-type x
  makeDef c constructor′  = data-cons (conData c)
  makeDef _ primitive′    = prim-fun

-- The type of the thing with the given name.

typeOf : Name → Type
typeOf = primQNameType

-- The definition of the thing with the given name.

definitionOf : Name → Definition
definitionOf x = makeDef x (primQNameDefinition x)

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

lam-inj₁ : ∀ {v v′ t t′} → lam v t ≡ lam v′ t′ → v ≡ v′
lam-inj₁ refl = refl

lam-inj₂ : ∀ {v v′ t t′} → lam v t ≡ lam v′ t′ → t ≡ t′
lam-inj₂ refl = refl

pi-inj₁ : ∀ {t₁ t₁′ t₂ t₂′} → pi t₁ t₂ ≡ pi t₁′ t₂′ → t₁ ≡ t₁′
pi-inj₁ refl = refl

pi-inj₂ : ∀ {t₁ t₁′ t₂ t₂′} → pi t₁ t₂ ≡ pi t₁′ t₂′ → t₂ ≡ t₂′
pi-inj₂ refl = refl

sort-inj : ∀ {x y} → sort x ≡ sort y → x ≡ y
sort-inj refl = refl

lit-inj : ∀ {x y} → Term.lit x ≡ lit y → x ≡ y
lit-inj refl = refl

quote-goal-inj : ∀ {x y} → quote-goal x ≡ quote-goal y → x ≡ y
quote-goal-inj refl = refl

quote-term-inj : ∀ {x y} → quote-term x ≡ quote-term y → x ≡ y
quote-term-inj refl = refl

unquote-term-inj : ∀ {x y} → unquote-term x ≡ unquote-term y → x ≡ y
unquote-term-inj refl = refl

unquote-term-inj₁ : ∀ {x y z w} → unquote-term x z ≡ unquote-term y w → x ≡ y
unquote-term-inj₁ refl = refl

unquote-term-inj₂ : ∀ {x y z w} → unquote-term x z ≡ unquote-term y w → z ≡ w
unquote-term-inj₂ refl = refl

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
