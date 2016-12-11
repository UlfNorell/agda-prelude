
module Tactic.Deriving where

open import Prelude hiding (abs)
open import Tactic.Reflection

private
  makeArgs : Nat → List (Arg Nat) → List (Arg Term)
  makeArgs n xs = reverse $ map (fmap (λ i → var (n - i - 1) [])) xs

  computeInstanceType : Name → Nat → List (Arg Nat) → Type → Maybe Term
  computeInstanceType class n xs (agda-sort _) =
    just (def class (vArg (var n (makeArgs n xs)) ∷ []))
  computeInstanceType class n xs (pi a (abs s b)) =
    pi (hArg (unArg a)) ∘ abs s <$> computeInstanceType class (suc n) ((n <$ a) ∷ xs) b
  computeInstanceType _ _ _ _ = nothing

  computeTel : Name → Nat → List (Arg Nat) → Telescope → Telescope → Telescope × List (Arg Term)
  computeTel d n xs is [] = reverse is , makeArgs (n + length is) xs
  computeTel d n xs is (a ∷ tel) =
    first (hArg (unArg a) ∷_) $
    case computeInstanceType d 0 [] (weaken 1 $ unArg a) of λ
    { (just i) → computeTel d (1 + n) ((n <$ a) ∷ xs)
                              (iArg (weaken (length is) i) ∷ weaken 1 is) tel
    ; nothing  → computeTel d (1 + n) ((n <$ a) ∷ xs) (weaken 1 is) tel }

-- Computes the telescope of instances for a given datatype and class. For instance,
-- instanceTelescope (quote Vec) (quote Eq) computes to
-- {a : Level} {A : Set a} {{_ : Eq A}} {n : Nat} , 3 ∷ 2 ∷ 0 ∷ []
instanceTelescope : Name → Name → TC (Telescope × List (Arg Term))
instanceTelescope d class = computeTel class 0 [] [] <$> (fst ∘ telView <$> getType d)

-- Compute the type of an instance declaration for an arbitrary datatype and class.
instanceType : Name → Name → TC Type
instanceType d class =
  caseM instanceTelescope d class of λ
  { (tel , vs) → pure $ telPi tel $ def₁ class (def d vs)
  }
