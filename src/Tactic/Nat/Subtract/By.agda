
module Tactic.Nat.Subtract.By where

open import Prelude
open import Builtin.Reflection
open import Tactic.Reflection.Quote
open import Tactic.Reflection
open import Control.Monad.State

open import Tactic.Nat.Reflect
open import Tactic.Nat.NF
open import Tactic.Nat.Exp
open import Tactic.Nat.Auto
open import Tactic.Nat.Auto.Lemmas
open import Tactic.Nat.Simpl.Lemmas
open import Tactic.Nat.Simpl
open import Tactic.Nat.Reflect

open import Tactic.Nat.Subtract.Exp
open import Tactic.Nat.Subtract.Reflect
open import Tactic.Nat.Subtract.Lemmas
open import Tactic.Nat.Less.Lemmas

private
  follows-diff-prf :
    ∀ {u u₁ v v₁ uv uv₁} →
    u < u₁ →
    (∀ a b → a + 0 ≡ b + uv → a + v ≡ b + u) →
    (∀ a b → a + 0 ≡ b + uv₁ → a + u₁ ≡ b + v₁) →
    v₁ ≡ suc (v₁ - suc v) + v
  follows-diff-prf {u} {v = v} {v₁} {uv} {uv₁} (diff! k) sound sound₁ =
      follows-from lem ʳ⟨≡⟩ (λ z → suc (z + v)) $≡ lem-sub-zero v₁ (suc v) (uv₁ + k + uv) (follows-from lem)
    where
      lem : suc (uv₁ + k + uv) + v ≡ v₁
      lem = sym $ sound₁ uv₁ 0 auto ʳ⟨≡⟩ auto ⟨≡⟩ sound (uv₁ + suc k + uv) (uv₁ + suc k) auto ʳ⟨≡⟩ auto

  decide-leq : ∀ u v ρ → Maybe (⟦ u ⟧ns (atomEnvS ρ) ≤ ⟦ v ⟧ns (atomEnvS ρ))
  decide-leq u v ρ with cancel u v | λ a b → cancel-sound-s′ a b u v (atomEnvS ρ)
  ... | [] , d | sound =
    let eval x = ⟦ x ⟧ns (atomEnvS ρ) in
    just (diff (eval d) $ sym (sound (suc (eval d)) 1 auto))
  ... | _  , _ | _     = nothing

  by-proof-less : ∀ a a₁ b b₁ ρ → Maybe (SubExpLess a a₁ ρ → SubExpLess b b₁ ρ)
  by-proof-less a a₁ b b₁ ρ with cancel (normSub a) (normSub a₁)
                                         | cancel (normSub b) (normSub b₁)
                                         | complicateSubLess a a₁ ρ
                                         | simplifySubLess b b₁ ρ
  ... | u , u₁ | v , v₁ | compl | simpl
    with cancel v u | cancel u₁ v₁
       | (λ a b → cancel-sound-s′ a b v u (atomEnvS ρ))
       | (λ a b → cancel-sound-s′ a b u₁ v₁ (atomEnvS ρ))
  ... | [] , uv | [] , uv₁ | sound | sound₁ = just $ λ a<a₁ →
      simpl $ diff (⟦ v₁ ⟧ns (atomEnvS ρ) - suc (⟦ v ⟧ns (atomEnvS ρ)))
                   (follows-diff-prf (compl a<a₁) sound sound₁)
  ... | _ | _ | _ | _ = nothing

  lem-plus-zero-r : ∀ a b → a + b ≡ 0 → b ≡ 0
  lem-plus-zero-r  zero   b eq = eq
  lem-plus-zero-r (suc a) b ()

  lem-leq-zero : ∀ {a b} → a ≤ b → b ≡ 0 → a ≡ 0
  lem-leq-zero (diff k eq) refl = lem-plus-zero-r k _ (follows-from (sym eq))

  -- More advanced tactics for equalities
  --   a + b ≡ 0 → a ≡ 0
  by-proof-eq : ∀ u u₁ v v₁ ρ → Maybe (⟦ u ⟧ns (atomEnvS ρ) ≡ ⟦ u₁ ⟧ns (atomEnvS ρ) → ⟦ v ⟧ns (atomEnvS ρ) ≡ ⟦ v₁ ⟧ns (atomEnvS ρ))
  by-proof-eq u  [] v  [] ρ = flip fmap (decide-leq v u ρ) lem-leq-zero
  by-proof-eq [] u₁ v  [] ρ = flip fmap (decide-leq v u₁ ρ) λ leq → lem-leq-zero leq ∘ sym
  by-proof-eq u  [] [] v₁ ρ = flip fmap (decide-leq v₁ u ρ) λ leq → sym ∘ lem-leq-zero leq
  by-proof-eq [] u₁ [] v₁ ρ = flip fmap (decide-leq v₁ u₁ ρ) λ leq → sym ∘ lem-leq-zero leq ∘ sym
  by-proof-eq u  u₁ v  v₁ ρ = nothing

  by-proof : ∀ hyp goal ρ → Maybe (⟦ hyp ⟧eqn ρ → ⟦ goal ⟧eqn ρ)
  by-proof (a :≡ a₁) (b :≡ b₁) ρ with cancel (normSub a) (normSub a₁)
                                               | cancel (normSub b) (normSub b₁)
                                               | complicateSubEq a a₁ ρ
                                               | simplifySubEq b b₁ ρ
  by-proof (a :≡ b) (a₁ :≡ b₁) ρ | u , u₁ |  v ,  v₁ | compl | simpl with u == v | u₁ == v₁
  by-proof (a :≡ b) (a₁ :≡ b₁) ρ | u , u₁ | .u , .u₁ | compl | simpl | yes refl | yes refl =
    just $ simpl ∘ compl
  ... | _ | _ with u == v₁ | u₁ == v   -- try sym
  by-proof (a :≡ b) (a₁ :≡ b₁) ρ | u , u₁ | .u₁ , .u | compl | simpl | w | w₁ | yes refl | yes refl =
    just $ simpl ∘ sym ∘ compl
  ...   | _ | _ = fmap (λ prf → simpl ∘ prf ∘ compl) (by-proof-eq u u₁ v v₁ ρ)

  by-proof (a :< b) (a₁ :≡ b₁) ρ = nothing
  by-proof (a :< a₁) (b :< b₁) ρ = by-proof-less a a₁ b b₁ ρ
  by-proof (a :≡ b) (a₁ :< b₁) ρ = flip fmap (by-proof-less a (lit 1 ⟨+⟩ b) a₁ b₁ ρ) λ prf eq →
    prf (diff 0 (cong suc (sym eq)))


by-tactic : Term → Term
by-tactic t =
  case termToSubHyps t of
  λ { (just (hyp ∷ goal ∷ [] , Γ)) →
        getProof (quote cantProve) t $
        def (quote by-proof)
            ( vArg (` hyp)
            ∷ vArg (` goal)
            ∷ vArg (quotedEnv Γ)
            ∷ [])
    ; _ → failedProof (quote invalidGoal) t
    }
