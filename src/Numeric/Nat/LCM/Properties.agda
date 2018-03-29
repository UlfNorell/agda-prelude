
module Numeric.Nat.LCM.Properties where

open import Prelude
open import Numeric.Nat.Divide
open import Numeric.Nat.Divide.Properties
open import Numeric.Nat.LCM

is-lcm-unique : ∀ {m m₁ a b} → IsLCM m a b → IsLCM m₁ a b → m ≡ m₁
is-lcm-unique {m} {m₁} (is-lcm a|m b|m lm) (is-lcm a|m₁ b|m₁ lm₁) =
  divides-antisym (lm m₁ a|m₁ b|m₁) (lm₁ m a|m b|m)

lcm-unique : ∀ {m a b} → IsLCM m a b → lcm! a b ≡ m
lcm-unique {a = a} {b} lm with lcm a b
... | lcm-res m₁ lm₁ = is-lcm-unique lm₁ lm

is-lcm-commute : ∀ {m a b} → IsLCM m a b → IsLCM m b a
is-lcm-commute (is-lcm a|m b|m g) = is-lcm b|m a|m (flip ∘ g)

lcm-commute : ∀ {a b} → lcm! a b ≡ lcm! b a
lcm-commute {a} {b} with lcm b a
... | lcm-res m lm = lcm-unique (is-lcm-commute lm)

private
  _|>_ = divides-trans

lcm-assoc : ∀ a b c → lcm! a (lcm! b c) ≡ lcm! (lcm! a b) c
lcm-assoc a b c with lcm a b | lcm b c
... | lcm-res ab (is-lcm a|ab b|ab lab)
    | lcm-res bc (is-lcm b|bc c|bc lbc) with lcm ab c
...    | lcm-res ab-c (is-lcm ab|abc c|abc labc) =
  lcm-unique {ab-c} {a} {bc}
    (is-lcm (a|ab |> ab|abc)
            (lbc ab-c (b|ab |> ab|abc) c|abc)
            λ k a|k bc|k → labc k (lab k a|k (b|bc |> bc|k)) (c|bc |> bc|k))
