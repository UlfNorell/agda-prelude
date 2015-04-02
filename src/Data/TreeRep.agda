
module Data.TreeRep where

open import Prelude
open import Builtin.Reflection
open import Builtin.Float

data Leaf : Set where
  char   : Char → Leaf
  string : String → Leaf
  float  : Float → Leaf
  name   : Name → Leaf

data TreeRep : Set where
  leaf : Leaf → TreeRep
  node : Nat → List (TreeRep) → TreeRep

private
  leaf-char-inj : ∀ {x y} → Leaf.char x ≡ char y → x ≡ y
  leaf-char-inj refl = refl

  leaf-string-inj : ∀ {x y} → Leaf.string x ≡ string y → x ≡ y
  leaf-string-inj refl = refl

  leaf-float-inj : ∀ {x y} → Leaf.float x ≡ float y → x ≡ y
  leaf-float-inj refl = refl

  leaf-name-inj : ∀ {x y} → Leaf.name x ≡ name y → x ≡ y
  leaf-name-inj refl = refl

  leaf-inj : ∀ {x y} → leaf x ≡ leaf y → x ≡ y
  leaf-inj refl = refl

  node-inj₁ : ∀ {x y z w} → node x z ≡ node y w → x ≡ y
  node-inj₁ refl = refl

  node-inj₂ : ∀ {x y z w} → node x z ≡ node y w → z ≡ w
  node-inj₂ refl = refl

  eq-leaf : (x y : Leaf) → Dec (x ≡ y)
  eq-leaf (char x) (char x₁) = decEq₁ leaf-char-inj (x == x₁)
  eq-leaf (string x) (string x₁) = decEq₁ leaf-string-inj (x == x₁)
  eq-leaf (float x) (float x₁) = decEq₁ leaf-float-inj (x == x₁)
  eq-leaf (name x) (name x₁) = decEq₁ leaf-name-inj (x == x₁)
  eq-leaf (char x) (string x₁) = no λ()
  eq-leaf (char x) (float x₁) = no λ()
  eq-leaf (char x) (name x₁) = no λ()
  eq-leaf (string x) (char x₁) = no λ()
  eq-leaf (string x) (float x₁) = no λ()
  eq-leaf (string x) (name x₁) = no λ()
  eq-leaf (float x) (char x₁) = no λ()
  eq-leaf (float x) (string x₁) = no λ()
  eq-leaf (float x) (name x₁) = no λ()
  eq-leaf (name x) (char x₁) = no λ()
  eq-leaf (name x) (string x₁) = no λ()
  eq-leaf (name x) (float x₁) = no λ()

instance
  EqLeaf : Eq Leaf
  EqLeaf = record { _==_ = eq-leaf }

private
  eq-tree  : (x y : TreeRep) → Dec (x ≡ y)
  eq-trees : (xs ys : List TreeRep) → Dec (xs ≡ ys)

  eq-tree (leaf x) (leaf x₁) = decEq₁ leaf-inj (x == x₁)
  eq-tree (leaf x) (node x₁ x₂) = no λ()
  eq-tree (node x x₁) (leaf x₂) = no λ()
  eq-tree (node x xs) (node y ys) = decEq₂ node-inj₁ node-inj₂ (x == y) (eq-trees xs ys)

  eq-trees [] [] = yes refl
  eq-trees [] (x ∷ ys) = no λ()
  eq-trees (x ∷ xs) [] = no λ()
  eq-trees (x ∷ xs) (y ∷ ys) = decEq₂ cons-inj-head cons-inj-tail (eq-tree x y) (eq-trees xs ys)

instance
  EqTree : Eq TreeRep
  EqTree = record { _==_ = eq-tree }

record TreeEncoding {a} (A : Set a) : Set a where
  field
    treeEncode : A → TreeRep
    treeDecode : TreeRep → Maybe A
    isTreeEmbedding : ∀ x → treeDecode (treeEncode x) ≡ just x

open TreeEncoding {{...}} public

module _ {a} {A : Set a} {{_ : TreeEncoding A}} where
  private
    encode-injective : (x y : A) → treeEncode x ≡ treeEncode y → x ≡ y
    encode-injective x y eq = eraseEquality $ just-inj $
      isTreeEmbedding x ʳ⟨≡⟩ cong treeDecode eq ⟨≡⟩ isTreeEmbedding y

    decTreeEq : (x y : A) → Dec (x ≡ y)
    decTreeEq x y with treeEncode x == treeEncode y
    decTreeEq x y | yes eq = yes (encode-injective x y eq)
    decTreeEq x y | no !eq = no λ x=y → !eq (cong treeEncode x=y)

  EqByTreeEncoding : Eq A
  EqByTreeEncoding = record { _==_ = decTreeEq }

--- Example ---

private
  data TestData : Set where
    cA : TestData → TestData
    cB : TestData → TestData → TestData
    cC : TestData
    cD : TestData → TestData → TestData

  private
    encodeTest : TestData → TreeRep
    encodeTest (cA x)   = node 0 (encodeTest x ∷ [])
    encodeTest (cB x y) = node 1 (encodeTest x ∷ encodeTest y ∷ [])
    encodeTest cC       = node 2 []
    encodeTest (cD x y) = node 3 (encodeTest x ∷ encodeTest y ∷ [])

    decodeTest : TreeRep → Maybe TestData
    decodeTest (leaf _) = nothing
    decodeTest (node 0 (x ∷ []))     = cA <$> decodeTest x
    decodeTest (node 1 (x ∷ y ∷ [])) = cB <$> decodeTest x <*> decodeTest y
    decodeTest (node 2 [])           = just cC
    decodeTest (node 3 (x ∷ y ∷ [])) = cD <$> decodeTest x <*> decodeTest y 
    decodeTest _ = nothing

    embeddingTest : ∀ x → decodeTest (encodeTest x) ≡ just x
    embeddingTest (cA x)   = cA =$= embeddingTest x
    embeddingTest (cB x y) = cB =$= embeddingTest x =*= embeddingTest y
    embeddingTest cC       = refl
    embeddingTest (cD x y) = cD =$= embeddingTest x =*= embeddingTest y

  instance
    EncodeTest : TreeEncoding TestData
    EncodeTest = record { treeEncode      = encodeTest
                        ; treeDecode      = decodeTest
                        ; isTreeEmbedding = embeddingTest }

    EqTest : Eq TestData
    EqTest = EqByTreeEncoding
