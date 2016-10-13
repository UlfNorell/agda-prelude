
module Tactic.Nat.Subtract.By where

open import Prelude
open import Builtin.Reflection
open import Tactic.Reflection.Quote
open import Tactic.Reflection.DeBruijn
open import Tactic.Reflection.Substitute
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

  follows-diff-prf : {a b c d : Nat} → a ≤ b → b < c → c ≤ d → d ≡ suc (d - suc a) + a
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
    do v≤u   ← decide-leq v  u  ρ
    -| u₁≤v₁ ← decide-leq u₁ v₁ ρ
    -| pure λ u<u₁ →
         diff (⟦ v₁ ⟧ns (atomEnvS ρ) - suc (⟦ v ⟧ns (atomEnvS ρ)))
              (follows-diff-prf v≤u u<u₁ u₁≤v₁)

  by-proof-less : ∀ a a₁ b b₁ ρ → Maybe (SubExpLess a a₁ ρ → SubExpLess b b₁ ρ)
  by-proof-less a a₁ b b₁ ρ with cancel (normSub a) (normSub a₁)
                               | cancel (normSub b) (normSub b₁)
                               | complicateSubLess a a₁ ρ
                               | simplifySubLess b b₁ ρ
  ... | u , u₁ | v , v₁ | compl | simpl =
    for prf ← by-proof-less-nf u u₁ v v₁ ρ do simpl ∘ prf ∘ compl

  lem-plus-zero-r : (a b : Nat) → a + b ≡ 0 → b ≡ 0
  lem-plus-zero-r  zero   b eq = eq
  lem-plus-zero-r (suc a) b ()

  lem-leq-zero : {a b : Nat} → a ≤ b → b ≡ 0 → a ≡ 0
  lem-leq-zero (diff k eq) refl = lem-plus-zero-r k _ (follows-from (sym eq))

  ⟨+⟩-sound-ns : ∀ {Atom} {{_ : Ord Atom}} u v (ρ : Env Atom) → ⟦ u +nf v ⟧ns ρ ≡ ⟦ u ⟧ns ρ + ⟦ v ⟧ns ρ
  ⟨+⟩-sound-ns u v ρ =
    ns-sound (u +nf v) ρ ⟨≡⟩
    ⟨+⟩-sound u v ρ ⟨≡⟩ʳ
    _+_ $≡ ns-sound u ρ *≡ ns-sound v ρ

  by-proof-eq-nf : Nat → ∀ u u₁ v v₁ ρ → Maybe (NFGoal _≡_ _≡_ u u₁ v v₁ ρ)

  by-proof-eq-sub : Nat → ∀ u u₁ v v₁ v₂ ρ → Maybe (NFGoal _≡_ _≡_ u u₁ [ 1 , [ v ⟨-⟩ v₁ ] ] v₂ ρ)
  by-proof-eq-sub n u u₁ v v₁ v₂ ρ =
    let eval  x = ⟦ x ⟧ns (atomEnvS ρ)
        evals x = ⟦ x ⟧sns ρ in
    for prf ← by-proof-eq-nf n u u₁ v (v₁ +nf v₂) ρ do λ u=u₁ →
    sym $ lem-sub-zero (evals v) (evals v₁) (eval v₂) $ sym $
      lem-eval-sns-ns v ρ ⟨≡⟩
      prf u=u₁ ⟨≡⟩
      ⟨+⟩-sound-ns v₁ v₂ (atomEnvS ρ) ⟨≡⟩ʳ
      (_+ eval v₂) $≡ (lem-eval-sns-ns v₁ ρ)

  by-proof-eq-sub₂ : Nat → ∀ u u₁ v v₁ v₂ v₃ ρ → Maybe (NFGoal _≡_ _≡_ u u₁ [ 1 , [ v ⟨-⟩ v₁ ] ] [ 1 , [ v₂ ⟨-⟩ v₃ ] ] ρ)
  by-proof-eq-sub₂ n u u₁ v v₁ v₂ v₃ ρ =
    let eval  x = ⟦ x ⟧ns (atomEnvS ρ)
        evals x = ⟦ x ⟧sns ρ in
    for prf ← by-proof-eq-nf n u u₁ (v₃ +nf v) (v₂ +nf v₁) ρ do λ u=u₁ →
    lem-sub (evals v₂) (evals v₃) (evals v) (evals v₁) $
      _+_ $≡ lem-eval-sns-ns v₃ ρ *≡ lem-eval-sns-ns v ρ ⟨≡⟩
      ⟨+⟩-sound-ns v₃ v (atomEnvS ρ) ʳ⟨≡⟩
      prf u=u₁ ⟨≡⟩ ⟨+⟩-sound-ns v₂ v₁ (atomEnvS ρ) ⟨≡⟩ʳ
      _+_ $≡ lem-eval-sns-ns v₂ ρ *≡ lem-eval-sns-ns v₁ ρ

  -- More advanced tactics for equalities
  --   a + b ≡ 0 → a ≡ 0
  by-proof-eq-adv : Nat → ∀ u u₁ v v₁ ρ → Maybe (NFGoal _≡_ _≡_ u u₁ v v₁ ρ)
  by-proof-eq-adv _ u  [] v  [] ρ = for leq ← decide-leq v  u  ρ do lem-leq-zero leq
  by-proof-eq-adv _ [] u₁ v  [] ρ = for leq ← decide-leq v  u₁ ρ do lem-leq-zero leq ∘ sym
  by-proof-eq-adv _ u  [] [] v₁ ρ = for leq ← decide-leq v₁ u  ρ do sym ∘ lem-leq-zero leq
  by-proof-eq-adv _ [] u₁ [] v₁ ρ = for leq ← decide-leq v₁ u₁ ρ do sym ∘ lem-leq-zero leq ∘ sym
  by-proof-eq-adv (suc n) u  u₁ [ 1 , [ v ⟨-⟩ v₁ ] ] [ 1 , [ v₂ ⟨-⟩ v₃ ] ] ρ = by-proof-eq-sub₂ n u u₁ v v₁ v₂ v₃ ρ
  by-proof-eq-adv n u  u₁ [ 1 , [ v ⟨-⟩ v₁ ] ] v₂ ρ = by-proof-eq-sub n u u₁ v v₁ v₂ ρ
  by-proof-eq-adv (suc n) u u₁ v₂ [ 1 , [ v ⟨-⟩ v₁ ] ] ρ =
    for prf ← by-proof-eq-sub n u u₁ v v₁ v₂ ρ do sym ∘ prf
  by-proof-eq-adv _ u  u₁ v  v₁ ρ = nothing

  by-proof-eq-nf n u u₁  v  v₁ ρ with u == v | u₁ == v₁
  by-proof-eq-nf n u u₁ .u .u₁ ρ | yes refl | yes refl = just id
  ... | _ | _ with u == v₁ | u₁ == v -- try sym
  by-proof-eq-nf n u u₁ .u₁ .u ρ | _ | _ | yes refl | yes refl = just sym
  ... | _ | _ = by-proof-eq-adv n u u₁ v v₁ ρ -- try advanced stuff


  by-proof-eq : ∀ a a₁ b b₁ ρ → Maybe (SubExpEq a a₁ ρ → SubExpEq b b₁ ρ)
  by-proof-eq a a₁ b b₁ ρ with cancel (normSub a) (normSub a₁)
                             | cancel (normSub b) (normSub b₁)
                             | complicateSubEq a a₁ ρ
                             | simplifySubEq b b₁ ρ
  ... | u , u₁ |  v ,  v₁ | compl | simpl =
    for prf ← by-proof-eq-nf 10 u u₁ v v₁ ρ do simpl ∘ prf ∘ compl

  not-less-zero′ : {n : Nat} → n < 0 → ⊥
  not-less-zero′ (diff _ ())

  not-less-zero : {A : Set} {n : Nat} → n < 0 → A
  not-less-zero n<0 = ⊥-elim (erase-⊥ (not-less-zero′ n<0))

  less-one-is-zero : {n : Nat} → n < 1 → n ≡ 0
  less-one-is-zero {zero} _ = refl
  less-one-is-zero {suc n} (diff k eq) = refute eq

  by-proof-less-eq-nf : ∀ u u₁ v v₁ ρ → Maybe (NFGoal _<_ _≡_ u u₁ v v₁ ρ)
  by-proof-less-eq-nf u [] v v₁ ρ = just not-less-zero  -- could've used refute, but we'll take it
  by-proof-less-eq-nf u [ 1 , [] ] v v₁ ρ =
    for prf ← by-proof-eq-nf 10 u [] v v₁ ρ do prf ∘ less-one-is-zero
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

by-tactic : Term → Type → TC Term
by-tactic prf g =
  inferNormalisedType prf >>= λ h →
  let t = pi (vArg h) (abs "_" (weaken 1 g)) in
  caseM termToSubHyps t of
  λ { (just (hyp ∷ goal ∷ [] , Γ)) → pure $
      applyTerm (safe
        (getProof (quote cantProve) t $
         def (quote by-proof)
             ( vArg (` hyp)
             ∷ vArg (` goal)
             ∷ vArg (quotedEnv Γ)
             ∷ [])) _) (vArg prf ∷ [])
    ; _ → pure $ failedProof (quote invalidGoal) t
    }
