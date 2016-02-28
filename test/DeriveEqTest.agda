open import Prelude
open import Container.List
open import Tactic.Deriving.Eq
open import Tactic.Reflection

module DeriveEqTest where

  module Test₀ where

    eqVec : deriveEqType Vec
    unquoteDef eqVec = deriveEqDef eqVec (quote Vec)

  module Test₁ where

    data D (A : Set) (B : A → Set) : Set where
      c : (x : A) → B x → D A B

    eqD : {A : Set} {B : A → Set} {{_ : Eq A}} {{_ : {x : A} → Eq (B x)}}
          (p q : D A B) → Dec (p ≡ q)
    unquoteDef eqD = deriveEqDef eqD (quote D)

  module Test₂ where

    data D (A B : Set) (C : A → B → Set)  : B → Set where
      c : (x : A)(y : B)(z : C x y) → D A B C y

    eqD : {A B : Set} {C : A → B → Set} {{_ : Eq A}} {{_ : Eq B}} {{_ : ∀ {x y} → Eq (C x y)}} →
          ∀ {x} (p q : D A B C x) → Dec (p ≡ q)
    unquoteDef eqD = deriveEqDef eqD (quote D)

  module Test₃ where

    data Test : Set where
      test : {x : Nat} → Vec Nat x → Test

    instance EqTest : Eq Test
    EqTest = record { _==_ = eqTest }
      where
        eqTest : (p q : Test) → Dec (p ≡ q)
        unquoteDef eqTest = deriveEqDef eqTest (quote Test)

  module Test₄ where

    data Test : Nat → Set where
      test : (x : Nat) → Test x

    unquoteDecl EqTest = deriveEq EqTest (quote Test)

  module Test₅ where

    data Test (B : Nat → Set) : Set where
      test : B zero → Test B

    unquoteDecl EqTest = deriveEq EqTest (quote Test)

    prf : (x y : Test (Vec Nat)) → Dec (x ≡ y)
    prf x y = x == y

  module Test₆ where

    instance  EqAny : ∀ {a} {A : Set a} {{_ : Eq A}}
                        {b} {P : A → Set b} {{_ : ∀ {x} → Eq (P x)}}
                        {xs : List A} → Eq (Any P xs)
    unquoteDef EqAny = defineEqInstance EqAny (quote Any)

    unquoteDecl EqId = deriveEq EqId (quote _≡_)

    data Test (A : Set) (xs : List A) (x : A) : Set where
      test : x ∈ xs → Test A xs x

    unquoteDecl EqTest = deriveEq EqTest (quote Test)

  module Issue-#2 where

    data Test : Set where
      test : {x : Nat} → Vec Nat x → Test

    unquoteDecl EqTest = deriveEq EqTest (quote Test)
