
module Tactic.Nat where

open import Prelude

open import Tactic.Nat.Reflect public using (cantProve; invalidGoal; QED)
open import Tactic.Nat.Induction public
open import Tactic.Nat.Subtract public renaming
  ( autosub          to auto
  ; simplifysub      to simplify
  ; follows-from-sub to by
  ; refutesub        to refute )

open import Tactic.Reflection public using (apply-tactic; apply-goal-tactic)

-- All tactics know about addition, multiplication and subtraction
-- of natural numbers, and can prove equalities and inequalities (_<_).
-- The available tactics are:

{-
  auto

    Prove an equation or inequality.
-}

private
  auto-example₁ : ∀ a b → (a - b) * (a + b) ≡ a ^ 2 - b ^ 2
  auto-example₁ a b = auto

  auto-example₂ : ∀ a b → (a + b) ^ 2 ≥ a ^ 2 + b ^ 2
  auto-example₂ a b = auto

{-
  by eq

    Prove the goal using the given assumption. For equalities it simplifies
    the goal and the assumption and check that they are the same (or symmetric).
    For inequalities, to prove a < b -> c < d, it simplifies the assumption and
    goal and then tries to prove c′ ≤ a′ and b′ ≤ d′. When proving that an
    inequality follows from an equality a ≡ b, the equality is weakened to
    a ≤ b before applying the above procedure.
-}

private
  by-example₁ : ∀ xs ys → sum (xs ++ ys) ≡ sum ys + sum xs
  by-example₁ []       ys = auto
  by-example₁ (x ∷ xs) ys = by (by-example₁ xs ys)

  by-example₂ : ∀ a b c → a + c < b + c → a < b
  by-example₂ a b c lt = by lt

  by-example₃ : ∀ a b → a ≡ b * 2 → a + b < (b + 1) * 3
  by-example₃ a b eq = by eq

{-
  refute eq

  Proves an arbitrary proposition given a false equation. Works for equations
  that simplify to 0 ≡ suc n (or symmetric) or n < 0, for some n.
-}

private
  refute-example₁ : ∀ {Anything : Set} a → a ≡ 2 * a + 1 → Anything
  refute-example₁ a eq = refute eq

  refute-example₂ : ∀ {Anything : Set} a b → a + b < a → Anything
  refute-example₂ a b lt = refute lt

{-
  simplify-goal => ?

    Simplify the current goal and let you keep working on the new goal.
    In most cases 'by prf' works better than
    'simplify-goal => prf' since it will also simplify prf. The advantage
    of simplify-goal is that it allows holes in prf.
-}

private
  simplify-goal-example : ∀ a b → a - b ≡ b - a → a ≡ b
  simplify-goal-example  zero    b      eq = by eq
  simplify-goal-example (suc a)  zero   eq = refute eq
  simplify-goal-example (suc a) (suc b) eq =
    simplify-goal => simplify-goal-example a b eq
    -- Old goal: suc a ≡ suc b
    -- New goal:     a ≡ b

{-
  simplify eq to x => ?

    Simplify the given equation (and the current goal) and bind the simplified
    equation to x in the new goal.
-}

private
  lemma : ∀ a b → a + b ≡ 0 → a ≡ 0
  lemma zero    b eq = refl
  lemma (suc a) b eq = refute eq

  simplify-example : ∀ a b → (a + 1) * (b + 1) ≡ a * b + 1 → a ≡ 0
  simplify-example a b eq = simplify eq to eq′ => lemma a b eq′

{-
  induction

    Prove a goal ∀ n → P n using induction. Applies 'auto' in the base case
    and 'by IH' in the step case.
-}

private
  -- n .. 1
  downFrom : Nat → List Nat
  downFrom zero    = []
  downFrom (suc n) = suc n ∷ downFrom n

  induction-example : ∀ n → sum (downFrom n) * 2 ≡ n * (n + 1)
  induction-example = induction
