-- A tactic that applies congruence and symmetry of equality proofs.
-- Given a hole and a lemma it tries (in order)
--   - refl
--   - lemma
--   - sym lemma
--   - f $≡ X₁ *≡ .. *≡ Xₙ and recurses on Xᵢ
--     if the goal is f us ≡ f vs
--     Hidden and instance arguments of f are left alone.

module Tactic.Cong where

open import Prelude
open import Container.Traversable
open import Tactic.Reflection

private
  refl′ : ∀ {a} {A : Set a} (x : A) → x ≡ x
  refl′ _ = refl

  pattern `refl a = def₁ (quote refl′) a

  parseEq : Term → Maybe (Term × Term)
  parseEq (def (quote _≡_) (hArg _ ∷ hArg _ ∷ vArg x ∷ vArg y ∷ [])) = just (x , y)
  parseEq _ = nothing

  -- build-cong f ps = f $≡ p₁ *≡ .. *≡ pₙ
  build-cong : Term → List Term → Term
  build-cong f [] = `refl unknown -- we tried this
  build-cong f (p ∷ ps) = foldl ap (def₂ (quote cong) f p) ps
    where
      ap = λ p q → def₂ (quote _*≡_) p q

  zipWithM!₃ : {A B C : Set} → (A → B → C → TC ⊤) → List A → List B → List C → TC ⊤
  zipWithM!₃ f (x ∷ xs) (y ∷ ys) (z ∷ zs) = f x y z *> zipWithM!₃ f xs ys zs
  zipWithM!₃ _ _ _ _ = pure _

  module _ (lemma : Term) where

    go go-cong : (d : Nat) (lhs rhs hole : Term) → TC ⊤
    go d lhs rhs hole =
      checkType hole (def₂ (quote _≡_) lhs rhs) *>
      (   unify hole (`refl lhs)
      <|> unify hole lemma
      <|> unify hole (def₁ (quote sym) lemma)
      <|> go-cong d lhs rhs hole
      <|> do lhs ← reduce lhs
             rhs ← reduce rhs
             go-cong d lhs rhs hole)

    solve : (d : Nat) (hole : Term) → TC ⊤
    solve d hole =
      caseM parseEq <$> (reduce =<< inferType hole) of λ where
        nothing → typeErrorS "Goal is not an equality type."
        (just (lhs , rhs)) → go d lhs rhs hole

    go-cong′ : ∀ d f us vs hole → TC ⊤
    go-cong′ d f us vs hole = do
      let us₁ = map unArg (filter isVisible us)
          vs₁ = map unArg (filter isVisible vs)
      holes ← traverse (const newMeta!) us₁
      zipWithM!₃ (go d) us₁ vs₁ holes
      unify hole (build-cong f holes)

    go-cong (suc d) (def f us) (def f₁ vs) hole = guard (f == f₁) (go-cong′ d (def₀ f) us vs hole)
    go-cong (suc d) (con c us) (con c₁ vs) hole = guard (c == c₁) (go-cong′ d (con₀ c) us vs hole)
    go-cong (suc d) (var x us) (var x₁ vs) hole = guard (x == x₁) (go-cong′ d (var₀ x) us vs hole)
    go-cong _ lhs rhs _ = empty

macro
  by-cong : ∀ {a} {A : Set a} {x y : A} → x ≡ y → Tactic
  by-cong {x = x} {y} lemma hole = do
      `lemma  ← quoteTC lemma
      ensureNoMetas =<< inferType hole
      lemMeta ← lemProxy `lemma
      solve lemMeta 100 hole <|> typeErrorS "Congruence failed"
      unify lemMeta `lemma
    where
      -- Create a meta for the lemma to avoid retype-checking it in case
      -- it's expensive. Don't do this if the lemma is a variable.
      lemProxy : Term → TC Term
      lemProxy lemma@(var _ []) = pure lemma
      lemProxy lemma = newMeta =<< quoteTC (x ≡ y)
