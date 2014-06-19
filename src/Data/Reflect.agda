
module Data.Reflect where

open import Prelude
open import Prelude.Equality.Unsafe

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

EqName : Eq Name
EqName = record { _==_ = eqName }

------------------------------------------------------------------------
-- Terms

-- Is the argument visible (explicit), hidden (implicit), or an
-- instance argument?

data Visibility : Set where
  visible hidden instance : Visibility

{-# BUILTIN HIDING   Visibility #-}
{-# BUILTIN VISIBLE  visible    #-}
{-# BUILTIN HIDDEN   hidden     #-}
{-# BUILTIN INSTANCE instance   #-}

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

{-# BUILTIN ARGINFO    ArgInfo #-}
{-# BUILTIN ARGARGINFO arg-info #-}
{-# BUILTIN ARG        Arg      #-}
{-# BUILTIN ARGARG     arg      #-}

unArg : ∀ {A} → Arg A → A
unArg (arg _ x) = x

-- Terms.

mutual
  data Term : Set where
    -- Variable applied to arguments.
    var     : (x : Nat) (args : List (Arg Term)) → Term
    -- Constructor applied to arguments.
    con     : (c : Name) (args : List (Arg Term)) → Term
    -- Identifier applied to arguments.
    def     : (f : Name) (args : List (Arg Term)) → Term
    -- Different kinds of λ-abstraction.
    lam     : (v : Visibility) (t : Term) → Term
    -- Pi-type.
    pi      : (t₁ : Arg Type) (t₂ : Type) → Term
    -- A sort.
    sort    : Sort → Term
    -- Anything else.
    unknown : Term

  data Type : Set where
    el : (s : Sort) (t : Term) → Type

  data Sort : Set where
    -- A Set of a given (possibly neutral) level.
    set     : (t : Term) → Sort
    -- A Set of a given concrete level.
    lit     : (n : Nat) → Sort
    -- Anything else.
    unknown : Sort

{-# BUILTIN AGDASORT            Sort    #-}
{-# BUILTIN AGDATYPE            Type    #-}
{-# BUILTIN AGDATERM            Term    #-}
{-# BUILTIN AGDATERMVAR         var     #-}
{-# BUILTIN AGDATERMCON         con     #-}
{-# BUILTIN AGDATERMDEF         def     #-}
{-# BUILTIN AGDATERMLAM         lam     #-}
{-# BUILTIN AGDATERMPI          pi      #-}
{-# BUILTIN AGDATERMSORT        sort    #-}
{-# BUILTIN AGDATERMUNSUPPORTED unknown #-}
{-# BUILTIN AGDATYPEEL          el      #-}
{-# BUILTIN AGDASORTSET         set     #-}
{-# BUILTIN AGDASORTLIT         lit     #-}
{-# BUILTIN AGDASORTUNSUPPORTED unknown #-}

------------------------------------------------------------------------
-- Definitions

postulate
  -- Function definition.
  Function  : Set
  -- Data type definition.
  DataType : Set
  -- Record type definition.
  Record    : Set

{-# BUILTIN AGDAFUNDEF    Function  #-}
{-# BUILTIN AGDADATADEF   DataType #-}
{-# BUILTIN AGDARECORDDEF Record    #-}

-- Definitions.

data Definition : Set where
  function     : Function  → Definition
  data-type    : DataType → Definition
  record′      : Record    → Definition
  constructor′ : Definition
  axiom        : Definition
  primitive′   : Definition

{-# BUILTIN AGDADEFINITION                Definition   #-}
{-# BUILTIN AGDADEFINITIONFUNDEF          function     #-}
{-# BUILTIN AGDADEFINITIONDATADEF         data-type    #-}
{-# BUILTIN AGDADEFINITIONRECORDDEF       record′      #-}
{-# BUILTIN AGDADEFINITIONDATACONSTRUCTOR constructor′ #-}
{-# BUILTIN AGDADEFINITIONPOSTULATE       axiom        #-}
{-# BUILTIN AGDADEFINITIONPRIMITIVE       primitive′   #-}

private
  primitive
    primQNameType        : Name → Type
    primQNameDefinition  : Name → Definition
    primDataConstructors : DataType → List Name

-- The type of the thing with the given name.

typeOf : Name → Type
typeOf = primQNameType

-- The definition of the thing with the given name.

definitionOf : Name → Definition
definitionOf = primQNameDefinition

-- The constructors of the given data type.

constructorsOf : DataType → List Name
constructorsOf = primDataConstructors

------------------------------------------------------------------------
-- Term equality is decidable

-- Injectivity of constructors

arg-inj₁ : ∀ {A i i′} {x x′ : A} → arg i x ≡ arg i′ x′ → i ≡ i′
arg-inj₁ refl = refl

arg-inj₂ : ∀ {A i i′} {x x′ : A} → arg i x ≡ arg i′ x′ → x ≡ x′
arg-inj₂ refl = refl

arg-info-inj₁ : ∀ {v v′ r r′} → arg-info v r ≡ arg-info v′ r′ → v ≡ v′
arg-info-inj₁ refl = refl

arg-info-inj₂ : ∀ {v v′ r r′} → arg-info v r ≡ arg-info v′ r′ → r ≡ r′
arg-info-inj₂ refl = refl

var-inj₁ : ∀ {x x′ args args′} → var x args ≡ var x′ args′ → x ≡ x′
var-inj₁ refl = refl

var-inj₂ : ∀ {x x′ args args′} → var x args ≡ var x′ args′ → args ≡ args′
var-inj₂ refl = refl

con-inj₁ : ∀ {c c′ args args′} → con c args ≡ con c′ args′ → c ≡ c′
con-inj₁ refl = refl

con-inj₂ : ∀ {c c′ args args′} → con c args ≡ con c′ args′ → args ≡ args′
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

set-inj : ∀ {x y} → set x ≡ set y → x ≡ y
set-inj refl = refl

lit-inj : ∀ {x y} → lit x ≡ lit y → x ≡ y
lit-inj refl = refl

el-inj₁ : ∀ {s s′ t t′} → el s t ≡ el s′ t′ → s ≡ s′
el-inj₁ refl = refl

el-inj₂ : ∀ {s s′ t t′} → el s t ≡ el s′ t′ → t ≡ t′
el-inj₂ refl = refl

EqVisibility : Eq Visibility
EqVisibility = record { _==_ = eqVis }
  where
    eqVis : ∀ x y → Dec (x ≡ y)
    eqVis visible  visible  = yes refl
    eqVis visible  hidden   = no (λ ())
    eqVis visible  instance = no (λ ())
    eqVis hidden   visible  = no (λ ())
    eqVis hidden   hidden   = yes refl
    eqVis hidden   instance = no (λ ())
    eqVis instance visible  = no (λ ())
    eqVis instance hidden   = no (λ ())
    eqVis instance instance = yes refl

EqRelevance : Eq Relevance
EqRelevance = record { _==_ = eqRel }
  where
    eqRel : ∀ x y → Dec (x ≡ y)
    eqRel relevant   relevant   = yes refl
    eqRel relevant   irrelevant = no (λ ())
    eqRel irrelevant relevant   = no (λ ())
    eqRel irrelevant irrelevant = yes refl

EqArgInfo : Eq ArgInfo
EqArgInfo = record { _==_ = eqArgInfo }
  where
    eqArgInfo : ∀ x y → Dec (x ≡ y)
    eqArgInfo (arg-info v r) (arg-info v₁ r₁) =
      decEq₂ arg-info-inj₁ arg-info-inj₂ (v == v₁) (r == r₁)

EqArg : ∀ {A} {{EqA : Eq A}} → Eq (Arg A)
EqArg = record { _==_ = eqArg }
  where
    eqArg : ∀ x y → Dec (x ≡ y)
    eqArg (arg i x) (arg i₁ x₁) = decEq₂ arg-inj₁ arg-inj₂ (i == i₁) (x == x₁)

private
  eqSort : (x y : Sort) → Dec (x ≡ y)
  eqTerm : (x y : Term) → Dec (x ≡ y)
  eqType : (x y : Type) → Dec (x ≡ y)

  eqArgType : (x y : Arg Type) → Dec (x ≡ y)
  eqArgType (arg i x) (arg i₁ x₁) = decEq₂ arg-inj₁ arg-inj₂ (i == i₁) (eqType x x₁)

  eqArgTerm : (x y : Arg Term) → Dec (x ≡ y)
  eqArgTerm (arg i x) (arg i₁ x₁) = decEq₂ arg-inj₁ arg-inj₂ (i == i₁) (eqTerm x x₁)

  eqArgs : (x y : List (Arg Term)) → Dec (x ≡ y)
  eqArgs [] [] = yes refl
  eqArgs [] (x ∷ xs) = no λ ()
  eqArgs (x ∷ xs) [] = no λ ()
  eqArgs (x ∷ xs) (y ∷ ys) = decEq₂ cons-inj-head cons-inj-tail (eqArgTerm x y) (eqArgs xs ys)

  eqTerm (var x args) (var x₁ args₁) = decEq₂ var-inj₁ var-inj₂ (x == x₁) (eqArgs args args₁)
  eqTerm (con c args) (con c₁ args₁) = decEq₂ con-inj₁ con-inj₂ (c == c₁) (eqArgs args args₁)
  eqTerm (def f args) (def f₁ args₁) = decEq₂ def-inj₁ def-inj₂ (f == f₁) (eqArgs args args₁)
  eqTerm (lam v x) (lam v₁ y) = decEq₂ lam-inj₁ lam-inj₂ (v == v₁) (eqTerm x y)
  eqTerm (pi t₁ t₂) (pi t₃ t₄) = decEq₂ pi-inj₁ pi-inj₂ (eqArgType t₁ t₃) (eqType t₂ t₄)
  eqTerm (sort x) (sort x₁) = decEq₁ sort-inj (eqSort x x₁)
  eqTerm unknown unknown = yes refl

  eqTerm (var x args) (con c args₁) = no λ ()
  eqTerm (var x args) (def f args₁) = no λ ()
  eqTerm (var x args) (lam v y) = no λ ()
  eqTerm (var x args) (pi t₁ t₂) = no λ ()
  eqTerm (var x args) (sort x₁) = no λ ()
  eqTerm (var x args) unknown = no λ ()
  eqTerm (con c args) (var x args₁) = no λ ()
  eqTerm (con c args) (def f args₁) = no λ ()
  eqTerm (con c args) (lam v y) = no λ ()
  eqTerm (con c args) (pi t₁ t₂) = no λ ()
  eqTerm (con c args) (sort x) = no λ ()
  eqTerm (con c args) unknown = no λ ()
  eqTerm (def f args) (var x args₁) = no λ ()
  eqTerm (def f args) (con c args₁) = no λ ()
  eqTerm (def f args) (lam v y) = no λ ()
  eqTerm (def f args) (pi t₁ t₂) = no λ ()
  eqTerm (def f args) (sort x) = no λ ()
  eqTerm (def f args) unknown = no λ ()
  eqTerm (lam v x) (var x₁ args) = no λ ()
  eqTerm (lam v x) (con c args) = no λ ()
  eqTerm (lam v x) (def f args) = no λ ()
  eqTerm (lam v x) (pi t₁ t₂) = no λ ()
  eqTerm (lam v x) (sort x₁) = no λ ()
  eqTerm (lam v x) unknown = no λ ()
  eqTerm (pi t₁ t₂) (var x args) = no λ ()
  eqTerm (pi t₁ t₂) (con c args) = no λ ()
  eqTerm (pi t₁ t₂) (def f args) = no λ ()
  eqTerm (pi t₁ t₂) (lam v y) = no λ ()
  eqTerm (pi t₁ t₂) (sort x) = no λ ()
  eqTerm (pi t₁ t₂) unknown = no λ ()
  eqTerm (sort x) (var x₁ args) = no λ ()
  eqTerm (sort x) (con c args) = no λ ()
  eqTerm (sort x) (def f args) = no λ ()
  eqTerm (sort x) (lam v y) = no λ ()
  eqTerm (sort x) (pi t₁ t₂) = no λ ()
  eqTerm (sort x) unknown = no λ ()
  eqTerm unknown (var x args) = no λ ()
  eqTerm unknown (con c args) = no λ ()
  eqTerm unknown (def f args) = no λ ()
  eqTerm unknown (lam v y) = no λ ()
  eqTerm unknown (pi t₁ t₂) = no λ ()
  eqTerm unknown (sort x) = no λ ()

  eqSort (set t) (set t₁) = decEq₁ set-inj (eqTerm t t₁)
  eqSort (lit n) (lit n₁) = decEq₁ lit-inj (n == n₁)
  eqSort unknown unknown = yes refl
  eqSort (set t) (lit n) = no λ ()
  eqSort (set t) unknown = no λ ()
  eqSort (lit n) (set t) = no λ ()
  eqSort (lit n) unknown = no λ ()
  eqSort unknown (set t) = no λ ()
  eqSort unknown (lit n) = no λ ()

  eqType (el s t) (el s₁ t₁) = decEq₂ el-inj₁ el-inj₂ (eqSort s s₁) (eqTerm t t₁)

EqArgs : Eq (List (Arg Term))
EqArgs = EqList {{EqA = EqArg {{EqA = record { _==_ = eqTerm }}}}}

EqArgType : Eq (Arg Type)
EqArgType = EqArg {{EqA = record { _==_ = eqType }}}

EqType : Eq Type
EqType = record { _==_ = eqType }

EqTerm : Eq Term
EqTerm = record { _==_ = eqTerm }
