
module Tactic.Nat.Subtract.Lemmas where

open import Prelude
open import Tactic.Nat.NF
open import Tactic.Nat.Exp
open import Tactic.Nat.Bag
open import Tactic.Nat.Simpl
open import Data.Nat.Properties.Core
open import Data.List.Properties
open import Tactic.Nat.Auto.Lemmas
open import Tactic.Nat.Simpl.Lemmas
open import Tactic.Nat.Auto
open import Tactic.Nat.Simpl

open import Tactic.Nat.Subtract.Exp

private
  lem-sub-zero : ∀ a b c → b + c ≡ a → a - b ≡ c
  lem-sub-zero ._  zero   c refl = refl
  lem-sub-zero ._ (suc b) c refl = lem-sub-zero _ b c refl

  lem-zero-sub : ∀ a b c → a + c ≡ b → a - b ≡ 0
  lem-zero-sub  zero   ._  zero   refl = refl
  lem-zero-sub  zero   ._ (suc c) refl = refl
  lem-zero-sub (suc a) ._  c      refl = lem-zero-sub a _ c refl

SoundSub : ∀ e (ρ : Env) → Set
SoundSub e ρ with normSub e
... | nothing = ⊤
... | just nf = ⟦ e ⟧se ρ ≡ ⟦ nf ⟧n ρ

sound-sub : ∀ e ρ → SoundSub e ρ
sound-sub (var x) ρ = auto
sound-sub (lit 0) ρ = refl
sound-sub (lit (suc n)) ρ = auto

sound-sub (e ⟨+⟩ e₁) ρ with normSub e | sound-sub e ρ | normSub e₁ | sound-sub e₁ ρ
sound-sub (e ⟨+⟩ e₁) ρ | nothing | prf | _       | prf₁ = prf
sound-sub (e ⟨+⟩ e₁) ρ | just _  | prf | nothing | prf₁ = prf₁
sound-sub (e ⟨+⟩ e₁) ρ | just n  | prf | just n₁ | prf₁ = cong₂ _+_ prf prf₁ ⟨≡⟩ʳ ⟨+⟩-sound n n₁ ρ

sound-sub (e ⟨*⟩ e₁) ρ with normSub e | sound-sub e ρ | normSub e₁ | sound-sub e₁ ρ
sound-sub (e ⟨*⟩ e₁) ρ | nothing | prf | _       | prf₁ = prf
sound-sub (e ⟨*⟩ e₁) ρ | just _  | prf | nothing | prf₁ = prf₁
sound-sub (e ⟨*⟩ e₁) ρ | just n  | prf | just n₁ | prf₁ = cong₂ _*_ prf prf₁ ⟨≡⟩ʳ ⟨*⟩-sound n n₁ ρ

sound-sub (e ⟨-⟩ e₁) ρ with normSub e | sound-sub e ρ | normSub e₁ | sound-sub e₁ ρ
sound-sub (e ⟨-⟩ e₁) ρ | nothing | prf | _       | prf₁ = prf
sound-sub (e ⟨-⟩ e₁) ρ | just _  | prf | nothing | prf₁ = prf₁
sound-sub (e ⟨-⟩ e₁) ρ | just n  | prf | just n₁ | prf₁
  with cancel n n₁ | (λ a b → cancel-sound′ a b n n₁ ρ) | λ a b → cancel-complete′ a b n n₁ ρ
... | (n′     , [])       | sound | complete =
      cong₂ _-_ prf prf₁ ⟨≡⟩
      lem-sub-zero (⟦ n ⟧n ρ) (⟦ n₁ ⟧n ρ) (⟦ n′ ⟧n ρ)
                   (complete (⟦ n₁ ⟧n ρ) (⟦ n ⟧n ρ) auto ⟨≡⟩ auto)
... | ([]     , x₁ ∷ n₁′) | sound | complete =
      cong₂ _-_ prf prf₁ ⟨≡⟩
      lem-zero-sub (⟦ n ⟧n ρ) (⟦ n₁ ⟧n ρ) (⟦ x₁ ∷ n₁′ ⟧n ρ)
                   (complete (⟦ n₁ ⟧n ρ) (⟦ n ⟧n ρ) auto ʳ⟨≡⟩ auto)
... | (x ∷ n′ , x₁ ∷ n₁′) | sound | complete = _
