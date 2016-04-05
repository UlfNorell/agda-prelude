module NatTactic where

  module _ where
    open import Agda.Builtin.Nat
    open import Agda.Builtin.List

    -- n .. 1
    downFrom : Nat → List Nat
    downFrom zero    = []
    downFrom (suc n) = suc n ∷ downFrom n

  module AgdaPreludeTest where
    open import Prelude
    open import Tactic.Nat

-- All tactics know about addition, multiplication and subtraction
-- of natural numbers, and can prove equalities and inequalities (_<_).
-- The available tactics are:

{-
  auto

    Prove an equation or inequality.
-}

    auto-example₁ : (a b : Nat) → (a - b) * (a + b) ≡ a ^ 2 - b ^ 2
    auto-example₁ a b = auto

    auto-example₂ : (a b : Nat) → (a + b) ^ 2 ≥ a ^ 2 + b ^ 2
    auto-example₂ a b = auto

{-
  by eq

    Prove the goal using the given assumption. For equalities it simplifies
    the goal and the assumption and checks if they match any of the following
    forms (up to symmetry):

          a ≡ b → a ≡ b
      a + b ≡ 0 → a ≡ 0

    For inequalities, to prove a < b -> c < d, it simplifies the assumption and
    goal and then tries to prove c′ ≤ a′ and b′ ≤ d′.

    When proving that an inequality follows from an equality a ≡ b, the equality
    is weakened to a ≤ b before applying the above procedure.

    Proving an equality from an inequality works if the inequality simplifies to
    a ≤ 0 (or a < 0 in which case it's trivial). It then reduces that to a ≡ 0
    and tries to prove the goal from that.
-}

    by-example₁ : (xs ys : List Nat) → sum (xs ++ ys) ≡ sum ys + sum xs
    by-example₁ []       ys = auto
    by-example₁ (x ∷ xs) ys = by (by-example₁ xs ys)

    by-example₂ : (a b c : Nat) → a + c < b + c → a < b
    by-example₂ a b c lt = by lt

    by-example₃ : (a b : Nat) → a ≡ b * 2 → a + b < (b + 1) * 3
    by-example₃ a b eq = by eq

    by-example₄ : (a b c : Nat) → a + b + c ≤ b → 2 * c ≡ c
    by-example₄ a b c lt = by lt

    by-example₅ : (a b c : Nat) → a + b ≡ b + c → 2 + a ≡ 1 + c + 1
    by-example₅ a b c eq = by eq

{-
  refute eq

  Proves an arbitrary proposition given a false equation. Works for equations
  that simplify to 0 ≡ suc n (or symmetric) or n < 0, for some n.
-}

    refute-example₁ : {Anything : Set} (a : Nat) → a ≡ 2 * a + 1 → Anything
    refute-example₁ a eq = refute eq

    refute-example₂ : {Anything : Set} (a b : Nat) → a + b < a → Anything
    refute-example₂ a b lt = refute lt

{-
  simplify-goal ?

    Simplify the current goal and let you keep working on the new goal.
    In most cases 'by prf' works better than
    'simplify-goal => prf' since it will also simplify prf. The advantage
    of simplify-goal is that it allows holes in prf.
-}

    simplify-goal-example₁ : (a b : Nat) → a - b ≡ b - a → a ≡ b
    simplify-goal-example₁  zero    b      eq = by eq
    simplify-goal-example₁ (suc a)  zero   eq = refute eq
    simplify-goal-example₁ (suc a) (suc b) eq =
      simplify-goal (simplify-goal-example₁ a b eq)
      -- Old goal: suc a ≡ suc b
      -- New goal:     a ≡ b

    simplify-goal-example₂ : (a b : Nat) → a - b ≡ b - a → a < suc b
    simplify-goal-example₂  zero    b      eq = by eq
    simplify-goal-example₂ (suc a)  zero   eq = refute eq
    simplify-goal-example₂ (suc a) (suc b) eq =
      simplify-goal (simplify-goal-example₂ a b eq)
      -- Old goal: suc a ≤ suc b
      -- New goal:     a ≤ b

    simplify-goal-example₃ : (a b c : Nat) → a ≡ c → a + b ≡ b + c
    simplify-goal-example₃ a b c eq = simplify-goal eq

{-
  simplify eq λ x → ?

    Simplify the given equation (and the current goal) and bind the simplified
    equation to x in the new goal.
-}

    lemma₁ : (a b : Nat) → a + b ≡ 0 → a ≡ 0
    lemma₁ zero    b eq = refl
    lemma₁ (suc a) b eq = refute eq

    simplify-example₁ : ∀ a b → (a + 1) * (b + 1) ≡ a * b + 1 → a ≡ 0
    simplify-example₁ a b eq = simplify eq λ eq′ → lemma₁ a b eq′

    lemma₂ : (a b : Nat) → a + b ≡ 0 → a < suc 0
    lemma₂ zero    b eq = auto
    lemma₂ (suc a) b eq = refute eq

    simplify-example₂ : ∀ a b → (a + 1) * (b + 1) ≡ a * b + 1 → a < suc 0
    simplify-example₂ a b eq = simplify eq λ eq′ → by (lemma₂ a b eq′)

    simplify-example₃ : (a b c : Nat) → a + b ≡ b + c → 2 + a ≡ 1 + c + 1
    simplify-example₃ a b c eq = simplify eq λ eq′ → eq′

{-
  induction

    Prove a goal ∀ n → P n using induction. Applies 'auto' in the base case
    and 'by IH' in the step case.
-}

    induction-example₁ : ∀ n → sum (downFrom n) * 2 ≡ n * (n + 1)
    induction-example₁ = induction

    induction-example₂ : ∀ n → sum (downFrom n) * 2 < suc (n * (n + 1))
    induction-example₂ = induction

  -- some equivalences needed to adapt Tactic.Nat to the standard library
  module EquivalenceOf≤ where
    open import Agda.Builtin.Equality
    open import Agda.Builtin.Nat

    open import Data.Nat using (less-than-or-equal) renaming (_≤_ to _≤s_)
    open import Data.Nat.Properties using (≤⇒≤″; ≤″⇒≤)
    open import Prelude using (diff; id) renaming (_≤_ to _≤p_)

    open import Tactic.Nat.Generic (quote _≤p_) (quote id) (quote id) using (by)

    ≤p→≤s : ∀ {a b} → a ≤p b → a ≤s b
    ≤p→≤s (diff k b₊₁≡k₊₁+a) = ≤″⇒≤ (less-than-or-equal {k = k} (by b₊₁≡k₊₁+a))

    ≤s→≤p : ∀ {a b} → a ≤s b → a ≤p b
    ≤s→≤p a≤sb with ≤⇒≤″ a≤sb
    ≤s→≤p _ | less-than-or-equal {k = k} a+k≡b = diff k (by a+k≡b)

  module StandardLibraryTest where
    open import Agda.Builtin.Equality
    open import Data.Nat
    open import Data.List hiding (downFrom)
    open import Function

    private
      infixr 8 _^_
      _^_ : ℕ → ℕ → ℕ
      n ^ zero  = 1
      n ^ suc m = n ^ m * n

    open EquivalenceOf≤
    open import Tactic.Nat.Generic (quote _≤_) (quote ≤s→≤p) (quote ≤p→≤s)

    auto-example₁ : (a b : ℕ) → (a ∸ b) * (a + b) ≡ a ^ 2 ∸ b ^ 2
    auto-example₁ a b = auto

    auto-example₂ : (a b : ℕ) → (a + b) ^ 2 ≥ a ^ 2 + b ^ 2
    auto-example₂ a b = auto

    by-example₁ : (xs ys : List ℕ) → sum (xs ++ ys) ≡ sum ys + sum xs
    by-example₁ []       ys = auto
    by-example₁ (x ∷ xs) ys = by (by-example₁ xs ys)

    by-example₂ : (a b c : ℕ) → a + c < b + c → a < b
    by-example₂ a b c lt = by lt

    by-example₃ : (a b : ℕ) → a ≡ b * 2 → a + b < (b + 1) * 3
    by-example₃ a b eq = by eq

    by-example₄ : (a b c : ℕ) → a + b + c ≤ b → 2 * c ≡ c
    by-example₄ a b c lt = by lt

    by-example₅ : (a b c : ℕ) → a + b ≡ b + c → 2 + a ≡ 1 + c + 1
    by-example₅ a b c eq = by eq

    refute-example₁ : {Anything : Set} (a : ℕ) → a ≡ 2 * a + 1 → Anything
    refute-example₁ a eq = refute eq

    refute-example₂ : {Anything : Set} (a b : ℕ) → a + b < a → Anything
    refute-example₂ a b lt = refute lt

    simplify-goal-example₁ : (a b : ℕ) → a ∸ b ≡ b ∸ a → a ≡ b
    simplify-goal-example₁  zero    b      eq = by eq
    simplify-goal-example₁ (suc a)  zero   eq = refute eq
    simplify-goal-example₁ (suc a) (suc b) eq =
      simplify-goal (simplify-goal-example₁ a b eq)

    simplify-goal-example₂ : (a b : ℕ) → a ∸ b ≡ b ∸ a → a < suc b
    simplify-goal-example₂  zero    b      eq = by eq
    simplify-goal-example₂ (suc a)  zero   eq = refute eq
    simplify-goal-example₂ (suc a) (suc b) eq =
      simplify-goal (by (simplify-goal-example₂ a b eq))

    simplify-goal-example₃ : (a b c : ℕ) → a ≡ c → a + b ≡ b + c
    simplify-goal-example₃ a b c eq = simplify-goal eq

    lemma₁ : (a b : ℕ) → a + b ≡ 0 → a ≡ 0
    lemma₁ zero    b eq = refl
    lemma₁ (suc a) b eq = refute eq

    simplify-example₁ : ∀ a b → (a + 1) * (b + 1) ≡ a * b + 1 → a ≡ 0
    simplify-example₁ a b eq = simplify eq λ eq′ → lemma₁ a b eq′

    lemma₂ : (a b : ℕ) → a + b ≡ 0 → a < suc 0
    lemma₂ zero    b eq = s≤s z≤n
    lemma₂ (suc a) b eq = refute eq

    simplify-example₂ : ∀ a b → (a + 1) * (b + 1) ≡ a * b + 1 → a < suc 0
    simplify-example₂ a b eq = simplify eq λ eq′ → by (lemma₂ a b eq′)

    simplify-example₃ : (a b c : ℕ) → a + b ≡ b + c → 2 + a ≡ 1 + c + 1
    simplify-example₃ a b c eq = simplify eq λ eq′ → eq′

    induction-example₁ : ∀ n → sum (downFrom n) * 2 ≡ n * (n + 1)
    induction-example₁ = induction

    induction-example₂ : ∀ n → sum (downFrom n) * 2 < suc (n * (n + 1))
    induction-example₂ = induction
