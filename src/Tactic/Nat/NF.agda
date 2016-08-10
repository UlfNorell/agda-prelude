
module Tactic.Nat.NF where

open import Prelude
open import Tactic.Nat.Exp
open import Container.Bag

Tm : Set → Set
Tm Atom = List Atom

NF : Set → Set
NF Atom = Bag (Tm Atom)

product1 : List Nat → Nat
product1 [] = 1
product1 (x ∷ xs) = foldl (λ n x → n * x) x xs

module _ {Atom : Set} {{_ : Ord Atom}} where
  infixl 6 _+nf_
  infixl 7 _*nf_

  _+nf_ : NF Atom → NF Atom → NF Atom
  _+nf_ a b = union a b

  merge : Tm Atom → Tm Atom → Tm Atom
  merge x [] = x
  merge [] y = y
  merge (i ∷ x) (j ∷ y) =
    if i <? j then i ∷ merge x (j ∷ y)
              else j ∷ merge (i ∷ x) y

  nf-sort : NF Atom → NF Atom
  nf-sort [] = []
  nf-sort (x ∷ nf) = union [ x ] (nf-sort nf)

  mulTm : Nat × Tm Atom → Nat × Tm Atom → Nat × Tm Atom
  mulTm (a , x) (b , y) = a * b , merge x y

  _*nf_ : NF Atom → NF Atom → NF Atom
  []      *nf b = []
  (t ∷ a) *nf b = nf-sort (map (mulTm t) b) +nf (a *nf b)


  -- Normalising expressions --
  norm : Exp Atom → NF Atom
  norm (var x) = [ 1 , [ x ] ]
  norm (lit 0) = []
  norm (lit n) = [ n , [] ]
  norm (e ⟨+⟩ e₁) = norm e +nf norm e₁
  norm (e ⟨*⟩ e₁) = norm e *nf norm e₁

  ⟦_⟧t : Nat × Tm Atom → Env Atom → Nat
  ⟦ k , v ⟧t ρ = k * productR (map ρ v)

  ⟦_⟧n : NF Atom → Env Atom → Nat
  ⟦ nf ⟧n ρ = sumR (map (flip ⟦_⟧t ρ) nf)

  ⟦_⟧ts : Nat × Tm Atom → Env Atom → Nat
  ⟦ 1 , v ⟧ts ρ = product1 (map ρ v)
  ⟦ k , v ⟧ts ρ = product1 (map ρ v) * k

  ⟦_⟧ns : NF Atom → Env Atom → Nat
  ⟦ []     ⟧ns ρ = 0
  ⟦ t ∷ nf ⟧ns ρ = foldl (λ n t → n + ⟦ t ⟧ts ρ) (⟦ t ⟧ts ρ) nf

  cancel : NF Atom → NF Atom → NF Atom × NF Atom
  cancel nf₁ [] = nf₁ , []
  cancel [] nf₂ = [] , nf₂
  cancel ((i , x) ∷ nf₁) ((j , y) ∷ nf₂) with compare x y
  ... | less    _ = first  (_∷_ (i , x)) (cancel nf₁ ((j , y) ∷ nf₂))
  ... | greater _ = second (_∷_ (j , y)) (cancel ((i , x) ∷ nf₁) nf₂)
  ... | equal   _ with compare i j
  ...                | less    (diff k _) = second (_∷_ (suc k , y)) (cancel nf₁ nf₂)
  ...                | greater (diff k _) = first  (_∷_ (suc k , x)) (cancel nf₁ nf₂)
  ...                | equal    _         = cancel nf₁ nf₂
