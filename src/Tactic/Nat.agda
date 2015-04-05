
module Tactic.Nat where

open import Prelude

open import Tactic.Nat.Reflect public using (cantProve; invalidGoal; QED)
open import Tactic.Nat.Induction public
open import Tactic.Nat.Subtract public renaming
  ( autosub          to auto
  ; simplifysub      to simplify
  ; follows-from-sub to follows-from
  ; refutesub        to refute )

open import Tactic.Reflection public using (apply-tactic; apply-goal-tactic)

-- All tactics know about addition, multiplication and subtraction
-- of natural numbers. The available ones are:

{-
  auto

    Prove an equation.
-}

private
  auto-example : ∀ a b → (a + b) * (a - b) ≡ a ^ 2 - b ^ 2
  auto-example a b = auto

{-
  follows-from eq

    Prove the goal using the given equation. Only works when the goal and the given
    equation simplify to the same thing. Symmetry not included.
-}

private
  follows-from-example : ∀ xs ys → sum (xs ++ ys) ≡ sum ys + sum xs
  follows-from-example []       ys = auto
  follows-from-example (x ∷ xs) ys = follows-from (follows-from-example xs ys)

{-
  refute eq

  Proves an arbitrary proposition given a false equation. For the purposes of this
  tactic a false equation is one that simplifies to 0 ≡ 1 + n (or symmetric) for
  some n.
-}

private
  refute-example : ∀ {Anything : Set} a → a ≡ 2 * a + 1 → Anything
  refute-example a eq = refute eq

{-
  simplify-goal => ?

    Simplify the current goal and let you keep working on the new goal.
    In most cases 'follows-from prf' works better than
    'simplify-goal => prf' since it will also simplify prf. The advantage
    of simplify-goal is that it allows holes in prf.
-}

private
  simplify-goal-example : ∀ a b → a - b ≡ b - a → a ≡ b
  simplify-goal-example  zero    b      eq = follows-from eq
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
    and 'follows-from IH' in the step case.
-}

private
  -- n .. 1
  downFrom : Nat → List Nat
  downFrom zero    = []
  downFrom (suc n) = suc n ∷ downFrom n

  induction-example : ∀ n → sum (downFrom n) * 2 ≡ n * (n + 1)
  induction-example = induction
