
module Prelude.Equality.Inspect where

open import Prelude.Function using (id)
open import Prelude.Equality
open import Prelude.Product

module _ {a b} {A : Set a} {B : A → Set b} (f : ∀ x → B x) (x : A) where

  -- The Graph idiom is more powerful than the old Inspect idiom
  -- (defined in terms of Graph below), in that it lets you both
  -- abstract over a term and keep the equation that the old term
  -- equals the abstracted variable.

  -- Use as follows:
  --   example : Γ → T (f e)
  --   example xs with f e | graphAt f e
  --   ... | z | ingraph eq = ?  -- eq : f e ≡ z, goal : T z

  data Graph (y : B x) : Set b where
    ingraph : f x ≡ y → Graph y

  graphAt : Graph (f x)
  graphAt = ingraph refl

module _ {a} {A : Set a} where

  Inspect : A → Set a
  Inspect x = Σ _ λ y → Graph id x y

  infix 4 _with≡_
  pattern _with≡_ x eq = x , ingraph eq 

  inspect : ∀ x → Inspect x
  inspect x = x , ingraph refl
