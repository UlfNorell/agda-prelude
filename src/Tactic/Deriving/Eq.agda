
open import Prelude
open import Data.List
open import Data.Traversable
open import Builtin.Reflection
open import Tactic.Reflection.Free
open import Tactic.Reflection.DeBruijn
open import Tactic.Reflection.Equality
open import Tactic.Reflection.Telescope

module Tactic.Deriving.Eq where

_∋_ : ∀ {a} (A : Set a) → A → A
A ∋ x = x

private
  -- Pattern synonyms --

  pattern con₀ f       = con f ([])
  pattern con₁ f x     = con f (vArg x ∷ [])
  pattern con₂ f x y   = con f (vArg x ∷ vArg y ∷ [])
  pattern con₃ f x y z = con f (vArg x ∷ vArg y ∷ vArg z ∷ [])

  pattern def₀ f       = def f ([])
  pattern def₁ f x     = def f (vArg x ∷ [])
  pattern def₂ f x y   = def f (vArg x ∷ vArg y ∷ [])
  pattern def₃ f x y z = def f (vArg x ∷ vArg y ∷ vArg z ∷ [])
  pattern def₄ f x y z u = def f (vArg x ∷ vArg y ∷ vArg z ∷ vArg u ∷ [])

  infix 5 _`≡_
  pattern _`≡_ x y = def₂ (quote _≡_) x y
  pattern `subst x y z = def₃ (quote transport) x y z
  pattern `refl = con (quote refl) []

  pattern `Eq a = def (quote Eq) (vArg a ∷ [])
  pattern _`→_  a b = pi (vArg (el unknown a)) (abs "_" (el unknown b))
  pattern _`→ʰ_ a b = pi (hArg (el unknown a)) (abs "_" (el unknown b))
  pattern _`→ⁱ_ a b = pi (iArg (el unknown a)) (abs "_" (el unknown b))
  infixr 4 _`→_ _`→ʰ_ _`→ⁱ_

  pattern vLam s t = lam visible (abs s t)

  -- Helper functions --

  nLam : ∀ {A} → List (Arg A) → Term → Term
  nLam [] t = t
  nLam (arg (arg-info v _) s ∷ tel) t = lam v (abs "x" (nLam tel t))

  nPi : ∀ {A} → List (Arg A) → Term → Term
  nPi [] t = t
  nPi (arg i _ ∷ tel) t = pi (arg i (el unknown unknown)) (abs "x" (el unknown (nPi tel t)))

  newArgs : ∀ {A} → List (Arg A) → List (Arg Term)
  newArgs {A} tel = newArgsFrom (length tel) tel
    where
      newArgsFrom : Nat → List (Arg A) → List (Arg Term)
      newArgsFrom (suc n) (arg i _ ∷ tel) = arg i (var n []) ∷ newArgsFrom n tel
      newArgsFrom _ _ = []

  hideTel : ∀ {A} → List (Arg A) → List (Arg A)
  hideTel [] = []
  hideTel (arg (arg-info _ r) t ∷ tel) = arg (arg-info hidden r) t ∷ hideTel tel

  weakenTelFrom : (from n : Nat) → Telescope → Telescope
  weakenTelFrom from n [] = []
  weakenTelFrom from n (t ∷ tel) = weakenFrom from n t ∷ weakenTelFrom (suc from) n tel

  weakenTel : (n : Nat) → Telescope → Telescope
  weakenTel 0 = id
  weakenTel n = weakenTelFrom 0 n

  #pars : (d : Name) → Nat
  #pars d = case (definitionOf d) of λ
    { (data-type n _) → n
    ; _               → 0
    }

  argsTel : (c : Name) → Telescope
  argsTel c = case (telView (typeOf c)) of λ
    { (tel , el _ (def d ixs)) → drop (#pars d) tel
    ; (tel , _               ) → tel
    }

  #args : (c : Name) → Nat
  #args c = length (argsTel c)

  params : (c : Name) → List (Arg Type)
  params c = case (telView (typeOf c)) of λ
    { (tel , el _ (def d ixs)) → take (#pars d) tel
    ; _                        → []
    }

  -- Unification of datatype indices --

  data Unify : Set where
    positive : List Nat → Unify
    negative : Unify
    failure  : String → Unify

  _&U_ : Unify → Unify → Unify
  (positive xs) &U (positive ys) = positive (xs ++ ys)
  (positive _)  &U negative      = negative
  negative      &U (positive _)  = negative
  negative      &U negative      = negative
  (failure msg) &U _             = failure msg
  _             &U (failure msg) = failure msg

  unify : Term → Term → Unify
  unifyArgs : List (Arg Term) → List (Arg Term) → Unify

  unify s            t            with s == t
  unify s            t            | yes _ = positive []
  unify (var x [])   (var y [])   | no  _ =
    if (x < y) -- In var-var case, instantiate the one that is bound the closest to us.
    then (positive (x ∷ []))
    else (positive (y ∷ []))
  unify (var x [])   t            | no  _ =
    if (elem x (freeVars t))
    then (failure "cyclic occurrence") -- We don't currently know if the occurrence is rigid or not
    else (positive (x ∷ []))
  unify t            (var x [])   | no  _ =
    if (elem x (freeVars t))
    then (failure "cyclic occurrence")
    else (positive (x ∷ []))
  unify (con c₁ xs₁) (con c₂ xs₂) | no  _ =
    if (isYes (c₁ == c₂))
    then unifyArgs xs₁ xs₂
    else negative
  unify _ _                       | no  _ = failure "not a constructor or a variable"

  unifyArgs [] [] = positive []
  unifyArgs [] (_ ∷ _) = failure "panic: different number of arguments"
  unifyArgs (_ ∷ _) [] = failure "panic: different number of arguments"
  unifyArgs (arg v₁ x ∷ xs) (arg v₂ y ∷ ys) =
    if (isYes (_==_ {{EqArgInfo}} v₁ v₂))
    then (unify x y &U unifyArgs xs ys)
    else (failure "panic: hiding mismatch")

  unifyIndices : (c₁ c₂ : Name) → Unify
  unifyIndices c₁ c₂ = case (telView (typeOf c₁) ,′ telView (typeOf c₂)) of λ
    { ((tel₁ , el _ (def d₁ xs₁)) , (tel₂ , el _ (def d₂ xs₂))) →
        let n₁ = #pars d₁
            n₂ = #pars d₂
            ixs₁ = drop n₁ xs₁
            ixs₂ = drop n₂ xs₂
        in unifyArgs (weaken                        (length tel₂ - n₂) ixs₁)
           -- weaken all variables of first constructor by number of arguments of second constructor
                     (weakenFrom (length tel₂ - n₂) (length tel₁ - n₁) ixs₂)
           -- weaken parameters of second constructor by number of arguments of first constructor
    ; _ → failure "panic: constructor type doesn't end in a def"
    }

  -- Analysing constructor types --

  forcedArgs : (c : Name) → List Nat
  forcedArgs c = case (unifyIndices c c) of λ
    { (positive xs) → xs
    ; _             → []
    }

  data Forced : Set where forced free : Forced

  instance
    DeBruijnForced : DeBruijn Forced
    DeBruijnForced = record
      { strengthenFrom = λ _ _ → just
      ; weakenFrom     = λ _ _ → id
      }

    DeBruijnVec : ∀ {a} {A : Set a} {n} {{_ : DeBruijn A}} → DeBruijn (Vec A n)
    DeBruijnVec = record
      { strengthenFrom = λ m n → traverse (strengthenFrom m n)
      ; weakenFrom     = λ m n → fmap (weakenFrom m n)
      }

    DeBruijnProd : {A B : Set} {{_ : DeBruijn A}} {{_ : DeBruijn B}} → DeBruijn (A × B)
    DeBruijnProd = record
      { strengthenFrom = λ { m n (x , y) → _,_ <$> (strengthenFrom m n x) <*> (strengthenFrom m n y) }
      ; weakenFrom     = λ { m n (x , y) → weakenFrom m n x , weakenFrom m n y }
      }

  RemainingArgs : Nat → Set
  RemainingArgs = Vec (Arg (Forced × Term × Term))

  leftArgs : ∀ {n} → RemainingArgs n → List (Arg Term)
  leftArgs = map (fmap (fst ∘ snd)) ∘ vecToList

  rightArgs : ∀ {n} → RemainingArgs n → List (Arg Term)
  rightArgs = map (fmap (snd ∘ snd)) ∘ vecToList

  classifyArgs : (c : Name) → RemainingArgs _
  classifyArgs c = classify (#argsc - 1) (#freec - 1) (argsTel c)
  -- The final argument should be (weakenTel (#argsc + #freec) (argsTel c)),
  -- but we don't really care about the types of the arguments anyway.
    where
      forcedc = forcedArgs c

      #argsc   = #args c
      #forcedc = length forcedc
      #freec   = #argsc - #forcedc

      classify : (m n : Nat) (tel : List (Arg Type)) → RemainingArgs (length tel)
      classify m n [] = []
      classify m n (arg i (el _ ty) ∷ tel) =
        if (elem m forcedc)
        then arg i (forced , var (#freec + m) [] , var (#freec + m) []) ∷ classify (m - 1) n       tel
        else arg i (free   , var (#freec + m) [] , var n            []) ∷ classify (m - 1) (n - 1) tel

  rightArgsFree : ∀ {n} → RemainingArgs n → List (Arg Term)
  rightArgsFree [] = []
  rightArgsFree (arg _ (forced , _ , _) ∷ xs) = rightArgsFree xs
  rightArgsFree (arg i (free   , _ , x) ∷ xs) = arg i x ∷ rightArgsFree xs

  countFree : ∀ {n} → RemainingArgs n → Nat
  countFree xs = length (rightArgsFree xs)

  refreshArgs : ∀ {n} → RemainingArgs n → RemainingArgs n
  refreshArgs xs = refresh (nfree - 1) xs
    where
      nfree = countFree xs

      refresh : ∀ {n} → Nat → RemainingArgs n → RemainingArgs n
      refresh n [] = []
      refresh n (arg i (forced , x , y) ∷ xs) = arg i (forced , x , y) ∷ refresh n xs
      refresh n (arg i (free   , x , y) ∷ xs) = arg i (free , x , var n []) ∷ refresh (n - 1) xs

  -- Matching constructor case --

  caseDec : ∀ {a b} {A : Set a} {B : Set b} → Dec A → (A → B) → (¬ A → B) → B
  caseDec (yes x) y n = y x
  caseDec (no x)  y n = n x

  checkEqArgs : ∀ {n} (c : Name) (xs : List (Arg Term)) (ys : RemainingArgs n) → Term
  checkEqArgs c xs (arg i (forced , y , z) ∷ args) =
    checkEqArgs c (xs ++ [ arg i y ]) args
  checkEqArgs {suc remainingArgs} c xs (arg i (free , y , z) ∷ args) =
    def₃ (quote caseDec)
      (def₂ (quote _==_) y z)
      (vLam "x≡y" checkEqArgsYes)
      (vLam "x≢y" checkEqArgsNo)
    where
      remainingFree = countFree args

      checkEqArgsYes : Term
      checkEqArgsYes =
        def (quote transport) (
          (vArg (vLam "x" (nPi (rightArgsFree args) (def₁ (quote Dec)
            (weaken (2 + remainingFree)
               (con c (xs ++ arg i y ∷ (leftArgs args)))
             `≡
             con c (weaken (2 + remainingFree) xs ++
                    arg i (var remainingFree []) ∷
                    rightArgs (refreshArgs (weaken (2 + remainingFree) args)))))))) ∷
          (vArg (var 0 [])) ∷
          (vArg (nLam (rightArgsFree args)
            (checkEqArgs c
              (weaken (1 + remainingFree) (xs ++ [ arg i y ]))
              (refreshArgs (weaken (1 + remainingFree) args))))) ∷
          weaken 1 (rightArgsFree args))

      checkEqArgsNo : Term
      checkEqArgsNo =
        con₁ (quote no) (vLam "eq" (var 1 (vArg (def₃ (quote _∋_)
          (nPi (hideTel (arg i z ∷ rightArgsFree args))
            (weaken (3 + remainingFree) (con c (xs ++ arg i y ∷ leftArgs args))
              `≡ con c (weaken (3 + remainingFree) xs ++
                        arg i (var remainingFree []) ∷
                        rightArgs (refreshArgs (weaken (3 + remainingFree) args)))
            `→
             weaken (4 + remainingFree) y `≡ var (1 + remainingFree) []))
          (pat-lam (clause
            (replicate (1 + remainingFree) (hArg dot) ++ vArg `refl ∷ [])
            `refl ∷ []) [])
          (var 0 [])) ∷ [])))

  checkEqArgs _ _ _ = con₁ (quote yes) (con₀ (quote refl))

  matchingClause : (c : Name) → Clause
  matchingClause c = clause (makeParamsPats ++
                              vArg (con c (makeLeftPattern args)) ∷
                              vArg (con c (makeRightPattern args)) ∷ [])
                            (checkEqArgs c makeParams args)
    where
      args = classifyArgs c

      makeParamsPats : List (Arg Pattern)
      makeParamsPats = map (fmap (λ _ → var "A")) (hideTel (params c))

      makeParams : List (Arg Term)
      makeParams = weaken (length (vecToList args) + countFree args) (newArgs (params c))

      makeLeftPattern : ∀ {n} → RemainingArgs n → List (Arg Pattern)
      makeLeftPattern [] = []
      makeLeftPattern (arg i _ ∷ xs) = arg i (var "x") ∷ makeLeftPattern xs

      makeRightPattern : ∀ {n} → RemainingArgs n → List (Arg Pattern)
      makeRightPattern [] = []
      makeRightPattern (arg i (forced , _ , _) ∷ xs) = arg i dot ∷ makeRightPattern xs
      makeRightPattern (arg i (free   , _ , _) ∷ xs) = arg i (var "y") ∷ makeRightPattern xs

  -- Mismatching constructor case --

  mismatchingClause : (c₁ c₂ : Name) (fs : List Nat) → Clause
  mismatchingClause c₁ c₂ fs =
    clause (vArg (con c₁ (makePattern (#args₁ + #args₂ - 1) (argsTel c₁))) ∷
            vArg (con c₂ (makePattern (#args₂ - 1) (argsTel c₂))) ∷ [])
           (con (quote no) ([ vArg (pat-lam ([ absurd-clause ([ vArg absurd ]) ]) []) ]))
    where
      args₁ = argsTel c₁
      args₂ = argsTel c₂
      #args₁ = length args₁
      #args₂ = length args₂
      forced₁ = filter (λ i → #args₂ ≤ i) fs
      forced₂ = filter (λ i → #args₂ > i) fs
      #forced₁ = length forced₁
      #forced₂ = length forced₂

      makePattern : (k : Nat) (args : List (Arg Type)) → List (Arg Pattern)
      makePattern k [] = []
      makePattern k (arg i _ ∷ args) = (if (elem k fs) then (arg i dot) else arg i (var "x"))
                                         ∷ makePattern (k - 1) args

  -- Clauses --

  makeClause : (c₁ c₂ : Name) → List Clause
  makeClause c₁ c₂ = case (c₁ == c₂) of λ
    { (yes _) → [ matchingClause c₁ ]
    ; (no  _) → case (unifyIndices c₁ c₂) of λ
      { (positive fs) → [ mismatchingClause c₁ c₂ fs ]
      ; _             → []
      }
    }

  constructorPairs : (d : Name) → List (Name × Name)
  constructorPairs d = case (definitionOf d) of λ
    { (data-type _ cs) → concat (map (λ c₁ → map (_,_ c₁) cs) cs)
    ; _ → []
    }

  eqDefinition : (d : Name) → List Clause
  eqDefinition d = concat (map (uncurry makeClause) (constructorPairs d))

  makeArgs : Nat → List (Arg Nat) → List (Arg Term)
  makeArgs n xs = reverse $ map (fmap (λ i → var (n - i - 1) [])) xs

  computeInstanceType : Nat → List (Arg Nat) → Type → Maybe Term
  computeInstanceType n xs (el _ (sort _)) =
    just (`Eq (var n (makeArgs n xs)))
  computeInstanceType n xs (el _ (pi a (abs s b))) =
    pi (hArg (unArg a)) ∘ abs s ∘ el unknown <$> computeInstanceType (suc n) ((n <$ a) ∷ xs) b
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

deriveEqType : Name → Term
deriveEqType d = computeType d 0 [] [] $ fst $ telView $ typeOf d

deriveEqDef : Name → List Clause
deriveEqDef d = eqDefinition d
