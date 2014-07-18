
module Tactic.Deriving where

open import Prelude
open import Data.List
open import Builtin.Reflection
open import Tactic.Reflection.DeBruijn
open import Tactic.Reflection.Telescope
open import Tactic.Reflection.Free

private
  subst : ∀ {a b} {A : Set a} (B : A → Set b) {x y : A} → x ≡ y → B x → B y
  subst B refl b = b

  -- Pattern synonyms --

  pattern con₁ f x     = con f (vArg x ∷ [])
  pattern con₂ f x y   = con f (vArg x ∷ vArg y ∷ [])
  pattern con₃ f x y z = con f (vArg x ∷ vArg y ∷ vArg z ∷ [])

  pattern def₁ f x     = def f (vArg x ∷ [])
  pattern def₂ f x y   = def f (vArg x ∷ vArg y ∷ [])
  pattern def₃ f x y z = def f (vArg x ∷ vArg y ∷ vArg z ∷ [])

  infix 5 _`≡_
  pattern _`≡_ x y = def₂ (quote _≡_) x y
  pattern `subst x y z = def₃ (quote subst) x y z
  pattern `refl = con (quote refl) []

  pattern `Eq a = def (quote Eq) (vArg a ∷ [])
  pattern _`→_ a b = pi (vArg (el unknown a)) (el unknown b)
  pattern _`→ʰ_ a b = pi (hArg (el unknown a)) (el unknown b)
  pattern _`→ⁱ_ a b = pi (iArg (el unknown a)) (el unknown b)
  infixr 4 _`→_ _`→ʰ_ _`→ⁱ_

  -- Analysing constructor types --

  data ConArgKind : Set where
    index normal : ConArgKind

  instance
    EqConArgKind : Eq ConArgKind
    EqConArgKind = record { _==_ = eq }
      where
        eq : ∀ x y → Dec (x ≡ y)
        eq index index = yes refl
        eq index normal = no (λ ())
        eq normal index = no (λ ())
        eq normal normal = yes refl

  data TypeHead : Set where
    fun set : TypeHead
    var     : Nat → TypeHead
    def     : Name → TypeHead
    bad     : TypeHead

  ConstructorSpec = List (Arg ConArgKind × TypeHead)
  Constructors = List (Name × ConstructorSpec)

  typeHead : Type → TypeHead
  typeHead (el s (var x _)) = var x
  typeHead (el s (con _ _)) = bad
  typeHead (el s (def f _)) = def f
  typeHead (el s (lam v t)) = bad
  typeHead (el s (pat-lam cs args)) = bad
  typeHead (el s (pi a b)) = fun
  typeHead (el s (sort s₁)) = set
  typeHead (el s (lit l)) = bad
  typeHead (el s unknown) = bad

  private
    classify : Telescope → Type → List (Arg ConArgKind × TypeHead)
    classify tel a = cl (listToVec tel)
      where
        fvs = freeVars a
        cl : ∀ {n} → Vec (Arg Type) n → List (Arg ConArgKind × TypeHead)
        cl [] = []
        cl {n = suc j} (arg i a ∷ as) = (arg i kind , adjust (typeHead a)) ∷ cl as
          where
            kind = if elem j fvs then index else normal
            adjust : TypeHead → TypeHead
            adjust (var x) = var (x + suc j)
            adjust k = k

  classifyConstructorArgs : Name → ConstructorSpec
  classifyConstructorArgs = uncurry classify ∘ telView ∘ typeOf

  computeConstructors : Name → Constructors
  computeConstructors d =
    case definitionOf d of
    λ { (data-type cs) → map (id &&& classifyConstructorArgs) cs
      ; _ → [] }

  data NormalArg (spec : ConstructorSpec) : Set where
    normal : ∀ {h} → (vArg normal , h) ∈ spec → NormalArg spec

  sucNormal : ∀ {x xs} → NormalArg xs → NormalArg (x ∷ xs)
  sucNormal (normal i) = normal (suc i)

  count : ∀ {a} {A : Set a} → (A → Bool) → List A → Nat
  count p []       = 0
  count p (x ∷ xs) = (if p x then 1 else 0) + count p xs

  isNormal : (a : Arg ConArgKind) → Maybe (a ≡ vArg normal)
  isNormal (vArg normal) = just refl
  isNormal _             = nothing

  isJust : ∀ {a} {A : Set a} → Maybe A → Bool
  isJust (just _) = true
  isJust nothing  = false

  countNormal : ConstructorSpec → Nat
  countNormal = count λ x → isJust (isNormal (fst x))

  normalArgs : {spec : ConstructorSpec} → Vec (NormalArg spec) (countNormal spec)
  normalArgs {[]} = []
  normalArgs {(a , h) ∷ spec} with isNormal a
  normalArgs {(.(vArg normal) , h) ∷ spec} | just refl = normal zero! ∷ (sucNormal <$> normalArgs)
  normalArgs {(a , h) ∷ spec}              | nothing   = sucNormal <$> normalArgs

  normalIx : ∀ {h} {spec : ConstructorSpec} → (vArg normal , h) ∈ spec → Nat
  normalIx (zero p) = zero
  normalIx {spec = (a , _) ∷ spec} (suc i) =
    if isJust (isNormal a) then suc (normalIx i) else normalIx i

  -- Matching constructor case --

  data Focus (cs : Constructors) : Set where
    focus : ∀ {c spec h} → (c , spec) ∈ cs → (vArg normal , h) ∈ spec → Focus cs

  focusCon : ∀ {cs} → Focus cs → Name
  focusCon (focus {c = c} _ _) = c

  private
    conP : Name × ConstructorSpec → Arg Pattern
    conP (c , spec) = vArg (con c (replicate (countNormal spec) (vArg var)))

    other-clause : Name × ConstructorSpec → Clause
    other-clause cspec = clause (conP cspec ∷ []) (def (quote ⊥) [])

    this-clause : ∀ {h} (c : Name) (spec : ConstructorSpec) → (vArg normal , h) ∈ spec → Term → Clause
    this-clause c spec i lhs = clause (conP (c , spec) ∷ []) (weaken a lhs `≡ var (a - suc (normalIx i)) [])
      where a = countNormal spec

    clauses : ∀ {c spec h} (cs : Constructors) → (c , spec) ∈ cs → (vArg normal , h) ∈ spec → Term → List Clause
    clauses [] () j _
    clauses ((c , a) ∷ cs) (zero refl) j lhs = this-clause c a j lhs ∷ map other-clause cs
    clauses (c       ∷ cs) (suc i)     j lhs = other-clause c        ∷ clauses cs i j lhs

  -- injPred : (cs : Constructors) → Focus cs → Term → Term
  -- injPred cs (focus i j) lhs = pat-lam (clauses cs i j lhs) []

  -- injTerm : (cs : Constructors) → Focus cs → Term → Term → Term
  -- injTerm cs foc lhs eq = `subst (injPred cs foc lhs) eq `refl

  downFrom : Nat → List Nat
  downFrom 0 = []
  downFrom (suc n) = n ∷ downFrom n

  downFromVec : ∀ {n} → Vec Nat n
  downFromVec {0} = []
  downFromVec {suc n} = n ∷ downFromVec

  typed : ∀ {a} (A : Set a) → A → A
  typed _ x = x

  iterate : ∀ {a} {A : Set a} → Nat → (A → A) → A → A
  iterate zero    f x = x
  iterate (suc n) f x = f (iterate n f x)

  nPi : Nat → Term → Term
  nPi n = iterate n (λ a → unknown `→ a)

  nLam : Nat → Term → Term
  nLam n = iterate n (lam visible)

  injType : (c : Name) (pars : List (Arg Term)) (xs : List Term) → Nat → Term
  injType c pars xs n =
    nPi (2 * n) (con c (weaken (2 * n) pars ++ xArgs ++ args₁) `≡ con c (xArgs ++ args₂) `→
                 var (2 * n) [] `≡ var n [])
    where
      xArgs = map vArg (weaken (2 * n) xs)
      args₁ args₂ : List (Arg Term)
      args₁ = map (λ i → vArg (var (i + n) [])) (downFrom n)
      args₂ = map (λ i → vArg (var  i      [])) (downFrom n)

  injPrf : Name → (pars : List (Arg Term)) (xs ys zs : List Term) → Term → Term
  injPrf c pars xs ys zs eq =
    def (quote typed) ( vArg (injType c pars xs (length ys))
                      ∷ vArg (pat-lam (clause ps (con (quote refl) []) ∷ []) [])
                      ∷ (map vArg (ys ++ zs ++ [ eq ])))
    where
      ps : List (Arg Pattern)
      ps = (vArg var <$ ys) ++ (vArg dot <$ zs) ++ [ vArg `refl ]

  disprove : Name → (pars : List (Arg Term)) (xs ys zs : List Term) → Nat → Term
  disprove c pars xs ys zs neq =
    con₁ (quote no) $′ lam visible $
    var (1 + neq) (vArg (injPrf c (weaken 1 pars) (weaken 1 xs) (weaken 1 ys) (weaken 1 zs) (var 0 [])) ∷ [])

  -- eq : y ≡ z
  -- zs′ ⊢ cont : Dec (c xs y ys ≡ c xs y zs′)
  -- Builds subst (λ q → ∀ zs′ → Dec (c xs y ys ≡ c xs q zs′)) eq zs cont
  --        : Dec (c xs y ys ≡ c xs z zs)
  castArg : (c : Name) (xs : List Term) (y : Term) (ys zs : List Term) (eq : Term) → Term → Term
  castArg c xs y ys zs eq cont =
    def (quote subst) $′ map vArg
    $ lam visible (nPi n $ def₁ (quote Dec)
        (con c (map (vArg ∘ weaken (n + 1)) (xs ++ y ∷ ys)) `≡
         con c (map vArg $ weaken (n + 1) xs ++ var n [] ∷ zs′)))
    ∷ eq ∷ nLam n cont ∷ zs
    where n  = length zs
          zs′ = map (λ i → var i []) (downFrom n)

  splitOnRes : (c : Name) (pars : List (Arg Term)) (xs : List Term) (y z : Term) (ys zs : List Term) → Term → Term
  splitOnRes c pars xs y z ys zs cont =
    pat-lam
    ( clause (vArg (con₁ (quote yes) var) ∷ []) (castArg c xs′ y′ ys′ zs′ (var 0 []) (weakenFrom (length zs) 1 cont))
    ∷ clause (vArg (con₁ (quote no)  var) ∷ []) (disprove c pars′ xs′ (y′ ∷ ys′) (z′ ∷ zs′) 0)
    ∷ []) []
    where
      pars′ = weaken 1 pars
      xs′ = weaken 1 xs
      y′  = weaken 1 y
      z′  = weaken 1 z
      ys′ = weaken 1 ys
      zs′ = weaken 1 zs

  caseOnArg : Name → (eqF : Name) (pars : List (Arg Term)) (xs : List Term) (y z : Term) (ys zs : List Term) → Term → Term
  caseOnArg c eqF pars xs y z ys zs cont =
    def₂ (quote case_of_) (def₂ eqF y z) (splitOnRes c pars xs y z ys zs cont)

  private
    conCase : ∀ {n c spec} {cs : Constructors} → (c , spec) ∈ cs → List (Arg Term) → List Term →
                      Vec (NormalArg spec × Name × Term) n → Vec Term n → Term
    conCase         i pars xs [] [] = con₁ (quote yes) `refl
    conCase {n = suc k} {c = c} i pars xs ((normal j , eqFun , y) ∷ args) (z ∷ zs) =
      caseOnArg c eqFun pars xs y z
                (map (snd ∘ snd) $ vecToList args)
                (vecToList zs)
                (conCase i (weaken k pars) (weaken k $ xs ++ [ y ]) (second (second (weaken k)) <$> args) zs′)
      where zs′ = (λ i → var i []) <$> downFromVec

  constructorCase : ∀ {c spec} (cs : Constructors) → (c , spec) ∈ cs → List (Arg Term) → Vec (Name × Term × Term) (countNormal spec) → Term
  constructorCase cs i params args =
    conCase i params []
            ((λ a c → a , fst c , fst (snd c)) <$> normalArgs <*> args)
            (snd ∘ snd <$> args)

  -- The no-confusion case --

  absurdLam : Term
  absurdLam = pat-lam [ absurd-clause (vArg absurd ∷ []) ] []

  no-confusion : Term
  no-confusion = con₁ (quote no) absurdLam

  -- Clauses --

  cross : ∀ {a b} {A : Set a} {B : Set b} → List A → List B → List (A × B)
  cross xs ys = concatMap (λ x → map (_,_ x) ys) xs

  pairs : ∀ {a} {A : Set a} → List A → List (A × A)
  pairs [] = []
  pairs xs = cross xs xs

  annotate∈ : ∀ {a} {A : Set a} (xs : List A) → List (Σ A λ x → x ∈ xs)
  annotate∈ {A = A} xs = loop xs id
    where
      loop : (ys : List A) → (∀ {x} → x ∈ ys → x ∈ xs) → List (Σ A (flip _∈_ xs))
      loop []       inj = []
      loop (x ∷ ys) inj = (x , inj zero!) ∷ (loop ys (inj ∘ suc))

  InstanceTable = TypeHead → Name

  lookupInstance : TypeHead → InstanceTable → Name
  lookupInstance h tbl = tbl h

  ConSpec : Constructors → Set
  ConSpec cs = Σ (Name × ConstructorSpec) (flip _∈_ cs)

  argTable : InstanceTable → (spec : ConstructorSpec) → Nat → Nat → Vec (Name × Term × Term) (countNormal spec)
  argTable tbl [] n i = []
  argTable tbl ((a , h) ∷ spec) n i with isNormal a
  ... | just z  = (lookupInstance h tbl , var (2 * n - i) [] , var (n - i) []) ∷ argTable tbl spec n (suc i)
  ... | nothing = argTable tbl spec n i

  matchingConClause : (cs : Constructors) → InstanceTable → Nat → ConSpec cs → Clause
  matchingConClause cs tbl params ((c , spec) , i) =
    clause (replicate params (hArg var) ++ conP (c , spec) ∷ conP (c , spec) ∷ [])
           (constructorCase cs i pars (argTable tbl spec n 1))
    where
      n = countNormal spec
      pars = map (λ i → hArg (var (i + 2 * n) [])) (downFrom params)

  mismatchConClause : InstanceTable → Name × ConstructorSpec → Name × ConstructorSpec → Clause
  mismatchConClause tbl c₁ c₂ =
    clause (conP c₁ ∷ conP c₂ ∷ []) no-confusion

  eqClause : (cs : Constructors) → InstanceTable → Nat → ConSpec cs → ConSpec cs → Clause
  eqClause cs tbl params ((c₁ , spec₁) , i₁) ((c₂ , spec₂) , i₂) =
    ifYes c₁ == c₂
    then matchingConClause cs tbl params ((c₁ , spec₁) , i₁)
    else mismatchConClause tbl (c₁ , spec₁) (c₂ , spec₂)

  eqClauses : Constructors → InstanceTable → Nat → List Clause
  eqClauses cs tbl params = map (uncurry (eqClause cs tbl params)) $ pairs (annotate∈ cs)

  -- Computing the type --

  makeArgs : Nat → List (Arg Nat) → List (Arg Term)
  makeArgs n xs = reverse $ map (fmap (λ i → var (n - i - 1) [])) xs

  computeInstanceType : Nat → List (Arg Nat) → Type → Maybe Term
  computeInstanceType n xs (el _ (sort _)) =
    just (`Eq (var n (makeArgs n xs)))
  computeInstanceType n xs (el _ (pi a b)) =
    pi (hArg (unArg a)) ∘ el unknown <$> computeInstanceType (suc n) ((n <$ a) ∷ xs) b
  computeInstanceType _ _ _ = nothing

  computeType : Name → Nat → List (Arg Nat) → Telescope → Telescope → Term
  computeType d n xs is [] =
    unEl $ telPi (reverse is) $ el unknown $
    def d (makeArgs (n + k) xs) `→ def d (makeArgs (n + k + 1) xs) `→
    def₁ (quote Dec) (var 1 [] `≡ var 0 [])
    where k = length is
  computeType d n xs is (a ∷ tel) =
    unEl (unArg a) `→ʰ 
    (case computeInstanceType 0 [] (weaken 1 $ unArg a) of
     λ { (just i) → computeType d (1 + n) ((n <$ a) ∷ xs) (iArg (el unknown $ weaken (length is) i) ∷ weaken 1 is) tel
       ; nothing →  computeType d (1 + n) ((n <$ a) ∷ xs) (weaken 1 is) tel })

  eqType : Name → Type
  eqType d = el unknown (computeType d 0 [] [] $ fst $ telView $ typeOf d)

  -- Instance tables --

  data MissingEqFun : Set where

  simpleITable : Name → Name → InstanceTable
  simpleITable d f (var x) = quote _==_
  simpleITable d f (def x) = ifYes x == d then f else quote MissingEqFun
  simpleITable d f _ = quote MissingEqFun

-- Tying it all together --

derivingEq : Name → Name → Function
derivingEq d f = fun-def (eqType d)
                         (eqClauses (computeConstructors d) (simpleITable d f) (dataParameters d))
