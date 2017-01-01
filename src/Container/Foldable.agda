
module Container.Foldable where

open import Prelude

record Foldable {a b w} (F : Set a → Set b) : Set (lsuc w ⊔ lsuc a ⊔ b) where
  field
    foldMap : ∀ {A}{W : Set w} {{MonW : Monoid W}} → (A → W) → F A → W

open Foldable {{...}} public

fold : ∀ {a w} {W : Set w} {F : Set w → Set a} {{FoldF : Foldable F}} {{MonW : Monoid W}} → F W → W
fold = foldMap id

minimum : ∀ {a w} {W : Set w} {F : Set w → Set a} {{FoldF : Foldable F}} {{OrdW : Ord W}} → F W → Maybe W
minimum = foldMap {{MonW = monoid}} just
  where
    monoid : Monoid _
    Monoid.mempty monoid = nothing
    Monoid._<>_ monoid (just x) (just y) = just (min x y)
    Monoid._<>_ monoid (just x) nothing = just x
    Monoid._<>_ monoid nothing (just y) = just y
    Monoid._<>_ monoid nothing nothing = nothing

maximum : ∀ {a w} {W : Set w} {F : Set w → Set a} {{FoldF : Foldable F}} {{OrdW : Ord W}} → F W → Maybe W
maximum = foldMap {{MonW = monoid}} just
  where
    monoid : Monoid _
    Monoid.mempty monoid = nothing
    Monoid._<>_ monoid (just x) (just y) = just (max x y)
    Monoid._<>_ monoid (just x) nothing = just x
    Monoid._<>_ monoid nothing (just y) = just y
    Monoid._<>_ monoid nothing nothing = nothing

--- Instances ---

instance
  FoldableList : ∀ {a w} → Foldable {a = a} {w = w} List
  FoldableList = record { foldMap = λ f → foldr (λ x w → f x <> w) mempty }

  FoldableMaybe : ∀ {a w} → Foldable {a = a} {w = w} Maybe
  FoldableMaybe = record { foldMap = maybe mempty }
