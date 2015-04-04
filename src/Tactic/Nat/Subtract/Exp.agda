
module Tactic.Nat.Subtract.Exp where

open import Prelude
open import Tactic.Nat.Exp
open import Tactic.Nat.NF
open import Data.Bag
open import Data.TreeRep

infixl 6 _⟨+⟩_ _⟨-⟩_
infixl 7 _⟨*⟩_

data SubExp : Set where
  var : (x : Var) → SubExp
  lit : (n : Nat) → SubExp
  _⟨+⟩_ _⟨-⟩_ _⟨*⟩_ : (a b : SubExp) → SubExp

⟦_⟧se : SubExp → Env Var → Nat
⟦ var x ⟧se    ρ = ρ x
⟦ lit n ⟧se    ρ = n
⟦ e₁ ⟨+⟩ e₂ ⟧se ρ = ⟦ e₁ ⟧se ρ + ⟦ e₂ ⟧se ρ
⟦ e₁ ⟨-⟩ e₂ ⟧se ρ = ⟦ e₁ ⟧se ρ - ⟦ e₂ ⟧se ρ
⟦ e₁ ⟨*⟩ e₂ ⟧se ρ = ⟦ e₁ ⟧se ρ * ⟦ e₂ ⟧se ρ

data SubAtom : Set

SubNF : Set
SubNF = NF SubAtom

data SubAtom where
  var   : Var → SubAtom
  _⟨-⟩_  : (a b : SubNF) → SubAtom

⟦_⟧sn : SubNF → Env Var → Nat
⟦_⟧st : Tm SubAtom → Env Var → Nat
⟦_⟧sa : SubAtom → Env Var → Nat

⟦ var x ⟧sa ρ = ρ x
⟦ a ⟨-⟩ b ⟧sa ρ = ⟦ a ⟧sn ρ - ⟦ b ⟧sn ρ

⟦ []     ⟧st ρ = 1
⟦ t ∷ ts ⟧st ρ = ⟦ t ⟧sa ρ * ⟦ ts ⟧st ρ

⟦ []           ⟧sn ρ = 0
⟦ (k , ts) ∷ n ⟧sn ρ = k * ⟦ ts ⟧st ρ + ⟦ n ⟧sn ρ

instance
  EncodeSubAtom : TreeEncoding SubAtom
  EncodeSubAtom = treeEncoding enc dec emb
    where
      enc    : SubAtom    → TreeRep
      encNF  : SubNF      → TreeRep
      encNFs : SubNF      → List TreeRep
      encTm  : Tm SubAtom → List TreeRep

      enc (var x)  = node x []
      enc (a ⟨-⟩ b) = node 0 (encNF a ∷ encNF b ∷ [])

      encNF n = node 0 (encNFs n)

      encNFs [] = []
      encNFs ((n , t) ∷ ns) = node n (encTm t) ∷ encNFs ns

      encTm []       = []
      encTm (x ∷ xs) = enc x ∷ encTm xs

      dec   : TreeRep → Maybe SubAtom
      decNF : TreeRep → Maybe SubNF
      decNFs : List TreeRep → Maybe SubNF
      decTm  : List TreeRep → Maybe (Tm SubAtom)

      dec (node x []) = just (var x)
      dec (node _ (t ∷ t₁ ∷ [])) = _⟨-⟩_ <$> decNF t <*> decNF t₁
      dec _ = nothing

      decNF (leaf _)    = nothing
      decNF (node _ ts) = decNFs ts

      decNFs (node n ts ∷ ts₁) = _∷_ <$> (_,_ n <$> decTm ts) <*> decNFs ts₁
      decNFs _                 = just []

      decTm []       = just []
      decTm (x ∷ ts) = _∷_ <$> dec x <*> decTm ts

      emb    : ∀ a → dec    (enc    a) ≡ just a
      embNFs : ∀ n → decNFs (encNFs n) ≡ just n
      embTm  : ∀ t → decTm  (encTm  t) ≡ just t

      emb (var x) = refl
      emb (a ⟨-⟩ b) = _⟨-⟩_ =$= embNFs a =*= embNFs b

      embNFs [] = refl
      embNFs ((n , t) ∷ ns) = _∷_ =$= (_,_ n =$= embTm t) =*= embNFs ns

      embTm []       = refl
      embTm (x ∷ xs) = _∷_ =$= emb x =*= embTm xs

  EqSubAtom : Eq SubAtom
  EqSubAtom = EqByTreeEncoding

  OrdSubAtom : Ord SubAtom
  OrdSubAtom = OrdByTreeEncoding

_-nf_ : SubNF → SubNF → SubNF
a -nf b =
  case cancel a b of λ
  { (x  , []) → x
  ; ([] ,  _) → []
  ; (a′  , b′) → [ 1 , [ a′ ⟨-⟩ b′ ] ] }

normSub : SubExp → SubNF
normSub (var x) = [ 1 , [ var x ] ]
normSub (lit 0) = []
normSub (lit n) = [ n , [] ]
normSub (e ⟨+⟩ e₁) = normSub e +nf  normSub e₁
-- normSub ((e ⟨-⟩ e₁) ⟨-⟩ e₂) = normSub e -nf (normSub e₁ +nf normSub e₂)
normSub (e ⟨-⟩ e₁) = normSub e -nf normSub e₁
normSub (e ⟨*⟩ e₁) = normSub e *nf  normSub e₁
