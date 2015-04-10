
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
open import Tactic.Nat.Refute
open import Tactic.Nat.Reflect

open import Tactic.Nat.Subtract.Exp
open import Tactic.Nat.Subtract.Reflect
open import Tactic.Nat.Subtract.Lemmas
open import Tactic.Nat.Less.Lemmas

private
  NFGoal : (R₁ R₂ : Nat → Nat → Set) (a b c d : SubNF) → Env Var → Set
  NFGoal _R₁_ _R₂_ a b c d ρ = ⟦ a ⟧ns (atomEnvS ρ) R₁ ⟦ b ⟧ns (atomEnvS ρ) → ⟦ c ⟧ns (atomEnvS ρ) R₂ ⟦ d ⟧ns (atomEnvS ρ)

  follows-diff-prf : ∀ {a b c d} → a ≤ b → b < c → c ≤ d → d ≡ suc (d - suc a) + a
  follows-diff-prf {a} (diff! i) (diff! j) (diff! k) =
    sym $ (λ z → suc z + a) $≡ lem-sub-zero (k + suc (j + (i + a))) (suc a) (i + j + k) auto ʳ⟨≡⟩
          auto

  decide-leq : ∀ u v ρ → Maybe (⟦ u ⟧ns (atomEnvS ρ) ≤ ⟦ v ⟧ns (atomEnvS ρ))
  decide-leq u v ρ with cancel u v | λ a b → cancel-sound-s′ a b u v (atomEnvS ρ)
  ... | [] , d | sound =
    let eval x = ⟦ x ⟧ns (atomEnvS ρ) in
    just (diff (eval d) $ sym (sound (suc (eval d)) 1 auto))
  ... | _  , _ | _     = nothing

  by-proof-less-nf : ∀ u u₁ v v₁ ρ → Maybe (NFGoal _<_ _<_ u u₁ v v₁ ρ)
  by-proof-less-nf u u₁ v v₁ ρ =
    forM v≤u  ← decide-leq v  u  ρ do
    for u₁≤v₁ ← decide-leq u₁ v₁ ρ do λ u<u₁ →
    diff (⟦ v₁ ⟧ns (atomEnvS ρ) - suc (⟦ v ⟧ns (atomEnvS ρ)))
         (follows-diff-prf v≤u u<u₁ u₁≤v₁)

  by-proof-less : ∀ a a₁ b b₁ ρ → Maybe (SubExpLess a a₁ ρ → SubExpLess b b₁ ρ)
  by-proof-less a a₁ b b₁ ρ with cancel (normSub a) (normSub a₁)
                               | cancel (normSub b) (normSub b₁)
                               | complicateSubLess a a₁ ρ
                               | simplifySubLess b b₁ ρ
  ... | u , u₁ | v , v₁ | compl | simpl =
    for prf ← by-proof-less-nf u u₁ v v₁ ρ do simpl ∘ prf ∘ compl

  lem-plus-zero-r : ∀ a b → a + b ≡ 0 → b ≡ 0
  lem-plus-zero-r  zero   b eq = eq
  lem-plus-zero-r (suc a) b ()

  lem-leq-zero : ∀ {a b} → a ≤ b → b ≡ 0 → a ≡ 0
  lem-leq-zero (diff k eq) refl = lem-plus-zero-r k _ (follows-from (sym eq))

  -- More advanced tactics for equalities
  --   a + b ≡ 0 → a ≡ 0
  by-proof-eq-adv : ∀ u u₁ v v₁ ρ → Maybe (NFGoal _≡_ _≡_ u u₁ v v₁ ρ)
  by-proof-eq-adv u  [] v  [] ρ = for leq ← decide-leq v  u  ρ do lem-leq-zero leq
  by-proof-eq-adv [] u₁ v  [] ρ = for leq ← decide-leq v  u₁ ρ do lem-leq-zero leq ∘ sym
  by-proof-eq-adv u  [] [] v₁ ρ = for leq ← decide-leq v₁ u  ρ do sym ∘ lem-leq-zero leq
  by-proof-eq-adv [] u₁ [] v₁ ρ = for leq ← decide-leq v₁ u₁ ρ do sym ∘ lem-leq-zero leq ∘ sym
  by-proof-eq-adv u  u₁ v  v₁ ρ = nothing

  by-proof-eq-nf : ∀ u u₁ v v₁ ρ → Maybe (NFGoal _≡_ _≡_ u u₁ v v₁ ρ)
  by-proof-eq-nf u u₁  v  v₁ ρ with u == v | u₁ == v₁
  by-proof-eq-nf u u₁ .u .u₁ ρ | yes refl | yes refl = just id
  ... | _ | _ with u == v₁ | u₁ == v -- try sym
  by-proof-eq-nf u u₁ .u₁ .u ρ | _ | _ | yes refl | yes refl = just sym
  ... | _ | _ = by-proof-eq-adv u u₁ v v₁ ρ -- try advanced stuff


  by-proof-eq : ∀ a a₁ b b₁ ρ → Maybe (SubExpEq a a₁ ρ → SubExpEq b b₁ ρ)
  by-proof-eq a a₁ b b₁ ρ with cancel (normSub a) (normSub a₁)
                             | cancel (normSub b) (normSub b₁)
                             | complicateSubEq a a₁ ρ
                             | simplifySubEq b b₁ ρ
  ... | u , u₁ |  v ,  v₁ | compl | simpl =
    for prf ← by-proof-eq-nf u u₁ v v₁ ρ do simpl ∘ prf ∘ compl

  not-less-zero′ : ∀ {n} → n < 0 → ⊥
  not-less-zero′ (diff _ ())

  not-less-zero : ∀ {A : Set} {n} → n < 0 → A
  not-less-zero n<0 = ⊥-elim (erase-⊥ (not-less-zero′ n<0))

  less-one-is-zero : ∀ {n} → n < 1 → n ≡ 0
  less-one-is-zero {zero} _ = refl
  less-one-is-zero {suc n} (diff k eq) = refute eq

  by-proof-less-eq-nf : ∀ u u₁ v v₁ ρ → Maybe (NFGoal _<_ _≡_ u u₁ v v₁ ρ)
  by-proof-less-eq-nf u [] v v₁ ρ = just not-less-zero  -- could've used refute, but we'll take it
  by-proof-less-eq-nf u [ 1 , [] ] v v₁ ρ =
    for prf ← by-proof-eq-nf u [] v v₁ ρ do prf ∘ less-one-is-zero
  by-proof-less-eq-nf u u₁ v v₁ ρ = nothing

  by-proof-less-eq : ∀ a a₁ b b₁ ρ → Maybe (SubExpLess a a₁ ρ → SubExpEq b b₁ ρ)
  by-proof-less-eq a a₁ b b₁ ρ with cancel (normSub a) (normSub a₁)
                                  | cancel (normSub b) (normSub b₁)
                                  | complicateSubLess a a₁ ρ
                                  | simplifySubEq b b₁ ρ
  ... | u , u₁ | v , v₁ | compl | simpl =
    for prf ← by-proof-less-eq-nf u u₁ v v₁ ρ do simpl ∘ prf ∘ compl

  by-proof : ∀ hyp goal ρ → Maybe (⟦ hyp ⟧eqn ρ → ⟦ goal ⟧eqn ρ)
  by-proof (a :≡ a₁) (b :≡ b₁) ρ = by-proof-eq a a₁ b b₁ ρ
  by-proof (a :< a₁) (b :≡ b₁) ρ = by-proof-less-eq a a₁ b b₁ ρ
  by-proof (a :< a₁) (b :< b₁) ρ = by-proof-less a a₁ b b₁ ρ
  by-proof (a :≡ a₁) (b :< b₁) ρ =
    for prf ← by-proof-less a (lit 1 ⟨+⟩ a₁) b b₁ ρ do
      λ eq → prf (diff 0 (cong suc (sym eq)))

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
