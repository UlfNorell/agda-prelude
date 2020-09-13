module Container.Foldable where

open import Prelude

record Foldable {a b w} (F : Set a → Set b) : Set (lsuc w ⊔ lsuc a ⊔ b) where
  field
    foldMap : ∀ {A}{W : Set w} {{MonW : Monoid W}} → (A → W) → F A → W
    overlap {{super}} : Functor F

open Foldable {{...}} public

fold : ∀ {a w} {W : Set w} {F : Set w → Set a} {{FoldF : Foldable F}} {{MonW : Monoid W}} → F W → W
fold = foldMap id

minimum : ∀ {a w} {W : Set w} {F : Set w → Set a} {{FoldF : Foldable F}} {{OrdW : Ord W}} → F W → Maybe W
minimum = foldMap {{MonW = monoid}} just
  where
    semigroup : Semigroup _
    _<>_ {{semigroup}} (just x) (just y) = just (min x y)
    _<>_ {{semigroup}} (just x) nothing = just x
    _<>_ {{semigroup}} nothing (just y) = just y
    _<>_ {{semigroup}} nothing nothing = nothing

    monoid : Monoid _
    Monoid.super monoid = semigroup
    mempty {{monoid}} = nothing


maximum : ∀ {a w} {W : Set w} {F : Set w → Set a} {{FoldF : Foldable F}} {{OrdW : Ord W}} → F W → Maybe W
maximum = foldMap {{MonW = monoid}} just
  where
    semigroup : Semigroup _
    _<>_ {{semigroup}} (just x) (just y) = just (max x y)
    _<>_ {{semigroup}} (just x) nothing = just x
    _<>_ {{semigroup}} nothing (just y) = just y
    _<>_ {{semigroup}} nothing nothing = nothing

    monoid : Monoid _
    Monoid.super monoid = semigroup
    mempty {{monoid}} = nothing

--- Instances ---

instance
  FoldableList : ∀ {a w} → Foldable {a = a} {w = w} List
  foldMap {{FoldableList}} f = foldr (λ x w → f x <> w) mempty

  FoldableMaybe : ∀ {a w} → Foldable {a = a} {w = w} Maybe
  foldMap {{FoldableMaybe}} = maybe mempty
