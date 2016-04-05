
module Tactic.Nat where

open import Prelude
open import Tactic.Nat.Generic (quote _≤_) (quote id) (quote id) public

{-

All tactics know about addition, multiplication and subtraction
of natural numbers, and can prove equalities and inequalities (_<_).
The available tactics are:

  * auto

    Prove an equation or inequality.

  * by eq

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

  * refute eq

    Proves an arbitrary proposition given a false equation. Works for equations
    that simplify to 0 ≡ suc n (or symmetric) or n < 0, for some n.

  * simplify-goal ?

    Simplify the current goal and let you keep working on the new goal.
    In most cases 'by prf' works better than
    'simplify-goal prf' since it will also simplify prf. The advantage
    of simplify-goal is that it allows holes in prf.

  * simplify eq λ x → ?

    Simplify the given equation (and the current goal) and bind the simplified
    equation to x in the new goal.

  * induction

    Prove a goal ∀ n → P n using induction. Applies 'auto' in the base case
    and 'by IH' in the step case.
-}
