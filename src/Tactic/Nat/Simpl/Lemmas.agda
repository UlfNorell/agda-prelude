
module Tactic.Nat.Simpl.Lemmas where

open import Prelude
open import Tactic.Nat.NF
open import Tactic.Nat.Exp
open import Container.Bag
open import Tactic.Nat.Auto
open import Prelude.Nat.Properties
open import Container.List.Properties
open import Tactic.Nat.Auto.Lemmas

product1-sound : ∀ xs → product1 xs ≡ productR xs
product1-sound [] = refl
product1-sound (x ∷ xs)
  rewrite sym (cong (λ x → foldl _*_ x xs) (mul-one-r x))
        | foldl-assoc _*_ mul-assoc x 1 xs
        | foldl-foldr _*_ 1 mul-assoc add-zero-r mul-one-r xs
        = refl

map-eq : ∀ {c b} {A : Set c} {B : Set b} (f g : A → B) →
           (∀ x → f x ≡ g x) → ∀ xs → map f xs ≡ map g xs
map-eq f g f=g [] = refl
map-eq f g f=g (x ∷ xs) rewrite f=g x | map-eq f g f=g xs = refl

fst-*** : ∀ {a b} {A₁ A₂ : Set a} {B₁ B₂ : Set b}
            (f : A₁ → B₁) (g : A₂ → B₂) (p : A₁ × A₂) →
            fst ((f *** g) p) ≡ f (fst p)
fst-*** f g (x , y) = refl

snd-*** : ∀ {a b} {A₁ A₂ : Set a} {B₁ B₂ : Set b}
            (f : A₁ → B₁) (g : A₂ → B₂) (p : A₁ × A₂) →
            snd ((f *** g) p) ≡ g (snd p)
snd-*** f g (x , y) = refl

eta : ∀ {a b} {A : Set a} {B : Set b} (p : A × B) → p ≡ (fst p , snd p)
eta (x , y) = refl

private
  shuffle₁ : (a b c : Nat) → a + (b + c) ≡ b + (a + c)
  shuffle₁ a b c = auto

module _ {Atom : Set} {{_ : Ord Atom}} where

  NFEqS : NF Atom × NF Atom → Env Atom → Set
  NFEqS (nf₁ , nf₂) ρ = ⟦ nf₁ ⟧ns ρ ≡ ⟦ nf₂ ⟧ns ρ

  NFEq : NF Atom × NF Atom → Env Atom → Set
  NFEq (nf₁ , nf₂) ρ = ⟦ nf₁ ⟧n ρ ≡ ⟦ nf₂ ⟧n ρ

  ts-sound : ∀ x (ρ : Env Atom) → ⟦ x ⟧ts ρ ≡ ⟦ x ⟧t ρ
  ts-sound (0 , x) ρ = mul-zero-r (product1 (map ρ x))
  ts-sound (1 , x) ρ = product1-sound (map ρ x) ⟨≡⟩ʳ add-zero-r _
  ts-sound (suc (suc i) , x) ρ
    rewrite sym (product1-sound (map ρ x))
          = auto

  private
    et : Env Atom → Nat × Tm Atom → Nat
    et  = flip ⟦_⟧t

    ets : Env Atom → Nat × Tm Atom → Nat
    ets = flip ⟦_⟧ts

    plus-nf : Nat → Env Atom → NF Atom → Nat
    plus-nf = λ a ρ xs → a + ⟦ xs ⟧n ρ

  ns-sound : ∀ nf (ρ : Env Atom) → ⟦ nf ⟧ns ρ ≡ ⟦ nf ⟧n ρ
  ns-sound [] ρ = refl
  ns-sound (x ∷ nf) ρ
    rewrite sym (foldl-map-fusion _+_ (ets ρ) (ets ρ x) nf)
          | ts-sound x ρ
          | map-eq (ets ρ) (et ρ) (flip ts-sound ρ) nf
          | sym (foldl-foldr _+_ 0 add-assoc (λ _ → refl) add-zero-r (map (et ρ) nf))
          | sym (foldl-assoc _+_ add-assoc (et ρ x) 0 (map (et ρ) nf))
          | add-zero-r (et ρ x)
          = refl

  private
    lem-sound : ∀ a b ρ f g (xs : NF Atom × NF Atom) →
            a + ⟦ fst ((f *** g) xs) ⟧n ρ ≡ b + ⟦ snd ((f *** g) xs) ⟧n ρ →
            a + ⟦ f (fst xs) ⟧n ρ         ≡ b + ⟦ g (snd xs) ⟧n ρ
    lem-sound a b ρ f g xs H =
      cong (plus-nf a ρ) (fst-*** f g xs)
      ʳ⟨≡⟩ H
       ⟨≡⟩ cong (plus-nf b ρ) (snd-*** f g xs)

  cancel-sound′ : ∀ a b nf₁ nf₂ (ρ : Env Atom) →
                    a + ⟦ fst (cancel nf₁ nf₂) ⟧n ρ ≡ b + ⟦ snd (cancel nf₁ nf₂) ⟧n ρ →
                    a + ⟦ nf₁ ⟧n ρ ≡ b + ⟦ nf₂ ⟧n ρ
  cancel-sound′ a b [] []        ρ H = H
  cancel-sound′ a b [] (x ∷ nf₂) ρ H = H
  cancel-sound′ a b (x ∷ nf₁) [] ρ H = H
  cancel-sound′ a b ((i , x) ∷ nf₁) ((j , y) ∷ nf₂) ρ H
    with compare x y
  ... | less _ = add-assoc a _ _ ⟨≡⟩ cancel-sound′ (a + et ρ (i , x)) b nf₁ ((j , y) ∷ nf₂) ρ
                   (add-assoc a _ _ ʳ⟨≡⟩ lem-sound a b ρ (_∷_ (i , x)) id (cancel nf₁ ((j , y) ∷ nf₂)) H)
  ... | greater _ =
          cancel-sound′ a (b + et ρ (j , y)) ((i , x) ∷ nf₁) nf₂ ρ
            (lem-sound a b ρ id (_∷_ (j , y)) (cancel ((i , x) ∷ nf₁) nf₂) H ⟨≡⟩ add-assoc b _ _)
          ⟨≡⟩ʳ add-assoc b _ _
  cancel-sound′ a b ((i , x) ∷ nf₁) ((j , .x) ∷ nf₂) ρ H | equal refl
    with compare i j
  cancel-sound′ a b ((i , x) ∷ nf₁) ((.(suc k + i) , .x) ∷ nf₂) ρ H | equal refl | less (diff! k) =
    shuffle₁ a (et ρ (i , x)) _
    ⟨≡⟩ cong (et ρ (i , x) +_) (cancel-sound′ a (b + et ρ (suc k , x)) nf₁ nf₂ ρ
          (lem-sound a b ρ id (_∷_ (suc k , x)) (cancel nf₁ nf₂) H ⟨≡⟩ add-assoc b _ _))
    ⟨≡⟩ auto
  cancel-sound′ a b ((.(suc k + j) , x) ∷ nf₁) ((j , .x) ∷ nf₂) ρ H | equal refl | greater (diff! k) =
    sym (shuffle₁ b (et ρ (j , x)) _
         ⟨≡⟩ cong (et ρ (j , x) +_) (sym (cancel-sound′ (a + et ρ (suc k , x)) b nf₁ nf₂ ρ
               (add-assoc a _ _ ʳ⟨≡⟩ lem-sound a b ρ (_∷_ (suc k , x)) id (cancel nf₁ nf₂) H)))
         ⟨≡⟩ auto)
  cancel-sound′ a b ((i , x) ∷ nf₁) ((.i , .x) ∷ nf₂) ρ H | equal refl | equal refl =
    shuffle₁ a (et ρ (i , x)) _
    ⟨≡⟩ cong (et ρ (i , x) +_) (cancel-sound′ a b nf₁ nf₂ ρ H)
    ⟨≡⟩ shuffle₁ (et ρ (i , x)) b _

  cancel-sound-s′ : ∀ a b nf₁ nf₂ (ρ : Env Atom) →
                         a + ⟦ fst (cancel nf₁ nf₂) ⟧ns ρ ≡ b + ⟦ snd (cancel nf₁ nf₂) ⟧ns ρ →
                         a + ⟦ nf₁ ⟧ns ρ ≡ b + ⟦ nf₂ ⟧ns ρ
  cancel-sound-s′ a b nf₁ nf₂ ρ eq =
    (a +_) $≡ ns-sound nf₁ ρ ⟨≡⟩
    cancel-sound′ a b nf₁ nf₂ ρ
      ((a +_) $≡ ns-sound (fst (cancel nf₁ nf₂)) ρ ʳ⟨≡⟩
       eq ⟨≡⟩ (b +_) $≡ ns-sound (snd (cancel nf₁ nf₂)) ρ) ⟨≡⟩ʳ
    (b +_) $≡ ns-sound nf₂ ρ

  cancel-sound : ∀ nf₁ nf₂ ρ → NFEqS (cancel nf₁ nf₂) ρ → NFEq (nf₁ , nf₂) ρ
  cancel-sound nf₁ nf₂ ρ H rewrite cong (λ p → NFEqS p ρ) (eta (cancel nf₁ nf₂)) =
    (cancel-sound′ 0 0 nf₁ nf₂ ρ
      (ns-sound (fst (cancel nf₁ nf₂)) ρ
         ʳ⟨≡⟩ H ⟨≡⟩
       ns-sound (snd (cancel nf₁ nf₂)) ρ))

  private
    prod : Env Atom → List Atom → Nat
    prod ρ x = productR (map ρ x)

  private
    lem-complete : ∀ a b ρ f g (xs : NF Atom × NF Atom) →
            a + ⟦ f (fst xs) ⟧n ρ         ≡ b + ⟦ g (snd xs) ⟧n ρ →
            a + ⟦ fst ((f *** g) xs) ⟧n ρ ≡ b + ⟦ snd ((f *** g) xs) ⟧n ρ
    lem-complete a b ρ f g xs H =
      cong (plus-nf a ρ) (fst-*** f g xs)
       ⟨≡⟩  H
       ⟨≡⟩ʳ cong (plus-nf b ρ) (snd-*** f g xs)

  cancel-complete′ : ∀ a b nf₁ nf₂ (ρ : Env Atom) →
                       a + ⟦ nf₁ ⟧n ρ ≡ b + ⟦ nf₂ ⟧n ρ →
                       a + ⟦ fst (cancel nf₁ nf₂) ⟧n ρ ≡ b + ⟦ snd (cancel nf₁ nf₂) ⟧n ρ
  cancel-complete′ a b [] [] ρ H = H
  cancel-complete′ a b [] (x ∷ nf₂) ρ H = H
  cancel-complete′ a b (x ∷ nf₁) [] ρ H = H
  cancel-complete′ a b ((i , x) ∷ nf₁) ((j , y) ∷ nf₂) ρ H with compare x y
  ... | less lt =
    lem-complete a b ρ (_∷_ (i , x)) id (cancel nf₁ ((j , y) ∷ nf₂))
      (add-assoc a _ _
       ⟨≡⟩ cancel-complete′ (a + et ρ (i , x)) b nf₁ ((j , y) ∷ nf₂) ρ
             (add-assoc a _ _ ʳ⟨≡⟩ H))
  ... | greater _ =
    lem-complete a b ρ id (_∷_ (j , y)) (cancel ((i , x) ∷ nf₁) nf₂)
      (cancel-complete′ a (b + et ρ (j , y)) ((i , x) ∷ nf₁) nf₂ ρ
        (H ⟨≡⟩ add-assoc b _ _)
       ⟨≡⟩ʳ add-assoc b _ _)
  cancel-complete′ a b ((i , x) ∷ nf₁) ((j , .x) ∷ nf₂) ρ H | equal refl with compare i j
  cancel-complete′ a b ((i , x) ∷ nf₁) ((.(suc (k + i)) , .x) ∷ nf₂) ρ H | equal refl | less (diff! k) =
    lem-complete a b ρ id (_∷_ (suc k , x)) (cancel nf₁ nf₂)
      (cancel-complete′ a (b + suc k * prod ρ x) nf₁ nf₂ ρ
        (add-inj₂ (i * prod ρ x) _ _
          (shuffle₁ (i * prod ρ x) a _
            ⟨≡⟩ H ⟨≡⟩ auto))
      ⟨≡⟩ʳ add-assoc b _ _)
  cancel-complete′ a b ((.(suc (k + j)) , x) ∷ nf₁) ((j , .x) ∷ nf₂) ρ H | equal refl | greater (diff! k) =
    lem-complete a b ρ (_∷_ (suc k , x)) id (cancel nf₁ nf₂)
      (add-assoc a _ _ ⟨≡⟩
       cancel-complete′ (a + suc k * prod ρ x) b nf₁ nf₂ ρ
         (add-inj₂ (j * prod ρ x) _ _
           (sym (shuffle₁ (j * prod ρ x) b _ ⟨≡⟩ʳ
                 auto ʳ⟨≡⟩ H))))
  cancel-complete′ a b ((i , x) ∷ nf₁) ((.i , .x) ∷ nf₂) ρ H | equal refl | equal refl =
    cancel-complete′ a b nf₁ nf₂ ρ
      (add-inj₂ (i * prod ρ x) _ _
        (shuffle₁ a (i * prod ρ x) _ ʳ⟨≡⟩ H ⟨≡⟩ shuffle₁ b (i * prod ρ x) _))

  cancel-complete-s′ : ∀ a b nf₁ nf₂ (ρ : Env Atom) →
                         a + ⟦ nf₁ ⟧ns ρ ≡ b + ⟦ nf₂ ⟧ns ρ →
                         a + ⟦ fst (cancel nf₁ nf₂) ⟧ns ρ ≡ b + ⟦ snd (cancel nf₁ nf₂) ⟧ns ρ
  cancel-complete-s′ a b nf₁ nf₂ ρ eq =
    (a +_) $≡ ns-sound (fst (cancel nf₁ nf₂)) ρ ⟨≡⟩
    cancel-complete′ a b nf₁ nf₂ ρ
      ((a +_) $≡ ns-sound nf₁ ρ ʳ⟨≡⟩
       eq ⟨≡⟩ (b +_) $≡ ns-sound nf₂ ρ) ⟨≡⟩ʳ
    (b +_) $≡ ns-sound (snd (cancel nf₁ nf₂)) ρ

  cancel-complete : ∀ nf₁ nf₂ ρ → NFEq (nf₁ , nf₂) ρ → NFEqS (cancel nf₁ nf₂) ρ
  cancel-complete nf₁ nf₂ ρ H rewrite cong (λ p → NFEqS p ρ) (eta (cancel nf₁ nf₂)) =
         ns-sound (fst (cancel nf₁ nf₂)) ρ
    ⟨≡⟩  cancel-complete′ 0 0 nf₁ nf₂ ρ H
    ⟨≡⟩ʳ ns-sound (snd (cancel nf₁ nf₂)) ρ
