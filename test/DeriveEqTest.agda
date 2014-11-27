open import Prelude
open import Data.List
open import Tactic.Deriving.Eq

module DeriveEqTest where

  module Test₀ where

    eqVec : unquote (deriveEqType (quote Vec))
    unquoteDef eqVec = deriveEqDef (quote Vec)

  module Test₁ where

    data D (A : Set) (B : A → Set) : Set where
      c : (x : A) → B x → D A B

    eqD : {A : Set} {B : A → Set} {{_ : Eq A}} {{_ : {x : A} → Eq (B x)}}
          (p q : D A B) → Dec (p ≡ q)
    unquoteDef eqD = deriveEqDef (quote D)
  
  module Test₂ where

    data D (A B : Set) (C : A → B → Set)  : B → Set where
      c : (x : A)(y : B)(z : C x y) → D A B C y

    eqD : {A B : Set} {C : A → B → Set} {{_ : Eq A}} {{_ : Eq B}} {{_ : ∀ {x y} → Eq (C x y)}} →
          ∀ {x} (p q : D A B C x) → Dec (p ≡ q)
    unquoteDef eqD = deriveEqDef (quote D)

  module Test₃ where

    data Test : Set where
      test : {x : Nat} → Vec Nat x → Test

    instance EqTest : Eq Test
    EqTest = record { _==_ = eqTest }
      where
        eqTest : (p q : Test) → Dec (p ≡ q)
        unquoteDef eqTest = deriveEqDef (quote Test)

  module Test₄ where

    data Test : Nat → Set where
      test : (x : Nat) → Test x

    instance EqTest : ∀ {n} → Eq (Test n)
    EqTest = record { _==_ = eqTest }
      where
        eqTest : ∀ {n} (p q : Test n) → Dec (p ≡ q)
        unquoteDef eqTest = deriveEqDef (quote Test)

  module Test₅ where

    data Test (B : Nat → Set) : Set where
      test : B zero → Test B

    instance EqTest : ∀ {B} {{_ : ∀ {x} → Eq (B x)}} → Eq (Test B)
    EqTest = record{ _==_ = eqTest }
      where
        eqTest : ∀ {B} {{_ : ∀ {x} → Eq (B x)}} (p q : Test B) → Dec (p ≡ q)
        unquoteDef eqTest = deriveEqDef (quote Test)

  module Test₆ where

    instance EqAny : ∀ {a} {A : Set a} {{_ : Eq A}}
                       {b} {P : A → Set b} {{_ : ∀ {x} → Eq (P x)}}
                       {xs : List A} → Eq (Any P xs)
    EqAny {{EqA}} {{EqP}} = record{ _==_ = eqAny {{EqA}} {{EqP}} }
      where
        {-# TERMINATING #-}
        eqAny : ∀ {a b} {A : Set a} {{_ : Eq A}} {P : A → Set b} {{_ : ∀ {x} → Eq (P x)}}
          {xs} (ps qs : Any P xs) → Dec (ps ≡ qs)
        unquoteDef eqAny = deriveEqDef (quote Any)

    instance EqId : ∀ {a} {A : Set a} {{_ : Eq A}} {x y : A} → Eq (x ≡ y)
    EqId = record { _==_ = eqId }
      where
        eqId : ∀ {a} {A : Set a} {{_ : Eq A}} {x y : A} (e₁ e₂ : x ≡ y) → Dec (e₁ ≡ e₂)
        unquoteDef eqId = deriveEqDef (quote _≡_)

    data Test (A : Set) (xs : List A) (x : A) : Set where
      test : x ∈ xs → Test A xs x

    instance EqTest : ∀ {A xs x} {{_ : Eq A}} → Eq (Test A xs x)
    EqTest = record{ _==_ = eqTest }
      where
        eqTest : ∀ {A xs x} {{_ : Eq A}} → (p q : Test A xs x) → Dec (p ≡ q)
        unquoteDef eqTest = deriveEqDef (quote Test)
