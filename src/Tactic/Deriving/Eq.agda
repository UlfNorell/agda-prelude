
open import Prelude hiding (abs)
open import Prelude.Variables
open import Container.List
open import Container.Traversable
open import Tactic.Reflection hiding (substArgs) renaming (unify to unifyTC)
open import Tactic.Reflection.Equality
open import Tactic.Deriving

module Tactic.Deriving.Eq where

_∋_ : ∀ {a} (A : Set a) → A → A
A ∋ x = x

private
  -- Pattern synonyms --
  infix 5 _`≡_
  pattern _`≡_ x y = def₂ (quote _≡_) x y
  pattern `subst x y z = def₃ (quote transport) x y z
  pattern `refl = con (quote refl) []

  pattern `Eq a = def (quote Eq) (vArg a ∷ [])

  pattern vLam s t = lam visible (abs s t)

  -- Helper functions --

  nLam : Telescope → Term → Term
  nLam [] t = t
  nLam ((x , arg (arg-info v _) s) ∷ tel) t = lam v (abs x (nLam tel t))

  nPi : Telescope → Term → Term
  nPi [] t = t
  nPi ((x , arg i _) ∷ tel) t = pi (arg i unknown) (abs x (nPi tel t))

  newVars' : (Nat → A) → List (Arg B) → List (Arg A)
  newVars' {A = A} {B = B} mkVar tel = newArgsFrom (length tel) tel
    where
      newArgsFrom : Nat → List (Arg B) → List (Arg A)
      newArgsFrom (suc n) (arg i _ ∷ tel) = arg i (mkVar n) ∷ newArgsFrom n tel
      newArgsFrom _ _ = []

  newVars : List (Arg A) → List (Arg Term)
  newVars = newVars' (λ x → var x [])

  newPatVars : List (Arg A) → List (Arg Pattern)
  newPatVars = newVars' var

  hideTel : Telescope → Telescope
  hideTel [] = []
  hideTel ((x , arg (arg-info _ r) t) ∷ tel) = (x , arg (arg-info hidden r) t) ∷ hideTel tel

  weakenTelFrom : (from n : Nat) → Telescope → Telescope
  weakenTelFrom from n [] = []
  weakenTelFrom from n (t ∷ tel) = weakenFrom from n t ∷ weakenTelFrom (suc from) n tel

  weakenTel : (n : Nat) → Telescope → Telescope
  weakenTel 0 = id
  weakenTel n = weakenTelFrom 0 n

  #pars : (d : Name) → TC Nat
  #pars = getParameters

  argsTel : (c : Name) → TC Telescope
  argsTel c = caseM telView <$> getType c of λ
    { (tel , def d ixs) → flip drop tel <$> #pars d
    ; (tel , _        ) → pure tel
    }

  #args : (c : Name) → TC Nat
  #args c = length <$> argsTel c

  params : (c : Name) → TC Telescope
  params c = telView <$> getType c >>= λ
    { (tel , def d ixs) → flip take tel <$> #pars d
    ; _                 → pure []
    }

  -- Parallel substitution --

  Substitution : Set
  Substitution = List (Nat × Term)

  underLambda : Substitution → Substitution
  underLambda = map (λ { (i , t) → suc i , weaken 1 t })

  {-# TERMINATING #-}
  subst : Substitution → Term → Term
  apply : Term → List (Arg Term) → Term
  substArgs : Substitution → List (Arg Term) → List (Arg Term)

  subst sub (var x args) = case (lookup sub x) of λ
    { (just s) → apply s (substArgs sub args)
    ; nothing  → var x (substArgs sub args)
    }
  subst sub (con c args) = con c (substArgs sub args)
  subst sub (def f args) = def f (substArgs sub args)
  subst sub (lam v t)    = lam v (fmap (subst (underLambda sub)) t)
  subst sub (lit l)      = lit l
  subst sub _            = unknown -- TODO

  apply f [] = f
  apply (var x args) xs = var x (args ++ xs)
  apply (con c args) xs = con c (args ++ xs)
  apply (def f args) xs = def f (args ++ xs)
  apply (lam _ (abs _ t)) (arg _ x ∷ xs) = case (strengthen 1 (subst ((0 , weaken 1 x) ∷ []) t)) of λ
    { (just f) → apply f xs
    ; nothing  → unknown
    }
  apply _ _ = unknown -- TODO

  substArgs sub = map (fmap (subst sub))

  -- Unification of datatype indices --

  data Unify : Set where
    positive : List (Nat × Term) → Unify
    negative : Unify

  failure : ∀ {a} {A : Set a} → String → TC A
  failure s = typeErrorS ("Unification error when deriving Eq: " & s)

  _&U_ : Unify → Unify → Unify
  (positive xs) &U (positive ys) = positive (xs ++ ys)
  (positive _)  &U negative      = negative
  negative      &U (positive _)  = negative
  negative      &U negative      = negative

  {-# TERMINATING #-}
  unify : Term → Term → TC Unify
  unifyArgs : List (Arg Term) → List (Arg Term) → TC Unify

  unify s            t            with s == t
  unify s            t            | yes _ = pure (positive [])
  unify (var x [])   (var y [])   | no  _ =
    if (x <? y) -- In var-var case, instantiate the one that is bound the closest to us.
    then pure (positive ((x , var y []) ∷ []))
    else pure (positive ((y , var x []) ∷ []))
  unify (var x [])   t            | no  _ =
    if (elem x (freeVars t))
    then failure "cyclic occurrence" -- We don't currently know if the occurrence is rigid or not
    else pure (positive ((x , t) ∷ []))
  unify t            (var x [])   | no  _ =
    if (elem x (freeVars t))
    then failure "cyclic occurrence"
    else pure (positive ((x , t) ∷ []))
  unify (con c₁ xs₁) (con c₂ xs₂) | no  _ =
    if (isYes (c₁ == c₂))
    then unifyArgs xs₁ xs₂
    else pure negative
  unify _ _                       | no  _ = failure "not a constructor or a variable"

  unifyArgs [] [] = pure (positive [])
  unifyArgs [] (_ ∷ _) = failure "panic: different number of arguments"
  unifyArgs (_ ∷ _) [] = failure "panic: different number of arguments"
  unifyArgs (arg v₁ x ∷ xs) (arg v₂ y ∷ ys) =
    if isYes (_==_ {{EqArgInfo}} v₁ v₂)
    then (unify x y >>= λ
      { (positive sub) → (positive sub &U_) <$> unifyArgs (substArgs sub xs) (substArgs sub ys)
      ; negative       → pure negative
      })
    else failure "panic: hiding mismatch"

  unifyIndices : (c₁ c₂ : Name) → TC Unify
  unifyIndices c₁ c₂ = do
    let panic = failure "panic: constructor type doesn't end in a def"
    tel₁ , def d₁ xs₁ ← telView <$> getType c₁ where _ → panic
    tel₂ , def d₂ xs₂ ← telView <$> getType c₂ where _ → panic
    n₁ ← #pars d₁
    n₂ ← #pars d₂
    let ixs₁ = drop n₁ xs₁
        ixs₂ = drop n₂ xs₂
    unifyArgs (weaken                        (length tel₂ - n₂) ixs₁)
            -- weaken all variables of first constructor by number of arguments of second constructor
              (weakenFrom (length tel₂ - n₂) (length tel₁ - n₁) ixs₂)
            -- weaken parameters of second constructor by number of arguments of first constructor

  -- Analysing constructor types --

  forcedArgs : (c : Name) → TC (List Nat)
  forcedArgs c = caseM (unifyIndices c c) of λ
    { (positive xs) → pure (map fst xs)
    ; _             → pure []
    }

  data Forced : Set where forced free : Forced

  instance
    DeBruijnForced : DeBruijn Forced
    strengthenFrom {{DeBruijnForced}} _ _ = just
    weakenFrom     {{DeBruijnForced}} _ _ = id

  RemainingArgs : Nat → Set
  RemainingArgs = Vec (Arg (Forced × Term × Term))

  leftArgs : ∀ {n} → RemainingArgs n → List (Arg Term)
  leftArgs = map (fmap (fst ∘ snd)) ∘ vecToList

  rightArgs : ∀ {n} → RemainingArgs n → List (Arg Term)
  rightArgs = map (fmap (snd ∘ snd)) ∘ vecToList

  classifyArgs : (c : Name) → TC (Σ Nat RemainingArgs)
  classifyArgs c = do
      #argsc  ← #args c
      forcedc ← forcedArgs c
      let #freec = #argsc - length forcedc
      _,_ _ ∘ classify #freec forcedc (#argsc - 1) (#freec - 1) <$> argsTel c
  -- The final argument should be (weakenTel (#argsc + #freec) (argsTel c)),
  -- but we don't really care about the types of the arguments anyway.
    where
      classify : Nat → List Nat → (m n : Nat) (tel : Telescope) → RemainingArgs (length tel)
      classify _ _ m n [] = []
      classify #freec forcedc m n ((_ , arg i ty) ∷ tel) =
        if (elem m forcedc)
        then arg i (forced , var (#freec + m) [] , var (#freec + m) []) ∷
             classify #freec forcedc (m - 1) n       tel
        else arg i (free   , var (#freec + m) [] , var n            []) ∷
             classify #freec forcedc (m - 1) (n - 1) tel

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

      wk : {A : Set} {{_ : DeBruijn A}} → Nat → A → A
      wk k = weaken (k + remainingFree)

      checkEqArgsYes : Term
      checkEqArgsYes =
        def (quote transport) (
          (vArg (vLam "x" (nPi (map ("x" ,_) (rightArgsFree args)) (def₁ (quote Dec)
            (wk 2
               (con c (xs ++ arg i y ∷ (leftArgs args)))
             `≡
             con c (wk 2 xs ++
                    arg i (var remainingFree []) ∷
                    rightArgs (refreshArgs (wk 2 args)))))))) ∷
          (vArg (var 0 [])) ∷
          (vArg (nLam (map ("x" ,_) (rightArgsFree args))
            (checkEqArgs c
              (wk 1 (xs ++ [ arg i y ]))
              (refreshArgs (wk 1 args))))) ∷
          weaken 1 (rightArgsFree args))

      checkEqArgsNo : Term
      checkEqArgsNo =
        con₁ (quote no) (vLam "eq" (var 1 (vArg (def₃ (quote _∋_)
          (nPi (hideTel (("_" , arg i z) ∷ map ("_" ,_) (rightArgsFree args)))
            (weaken (3 + remainingFree) (con c (xs ++ arg i y ∷ leftArgs args))
              `≡ con c (wk 3 xs ++
                        arg i (var remainingFree []) ∷
                        rightArgs (refreshArgs (wk 3 args)))
            `→
             wk 4 y `≡ var (1 + remainingFree) []))
          (pat-lam (clause
            []
            (replicate (1 + remainingFree) (hArg (dot unknown)) ++ vArg `refl ∷ [])
            `refl ∷ []) [])
          (var 0 [])) ∷ [])))

  checkEqArgs _ _ _ = con₁ (quote yes) (con₀ (quote refl))

  matchingClause : (c : Name) → TC Clause
  matchingClause c = do
      _ , args  ← classifyArgs c
      let #cargs-total = length (vecToList args)
          #cargs-free  = countFree args
      paramTel  ← hideTel <$> params c
      let paramPats = weaken (#cargs-total + #cargs-free) $ newPatVars $ map snd paramTel
      let paramArgs = weaken (#cargs-total + #cargs-free) $ newVars $ map snd paramTel
      pure (clause (paramTel ++ ctel-total args ++ ctel-free args)
                   (paramPats ++
                    vArg (con c (makeLeftPattern args (#cargs-total + #cargs-free))) ∷
                    vArg (con c (makeRightPattern args #cargs-free)) ∷ [])
                   (checkEqArgs c paramArgs args))
    where
      ctel-total : RemainingArgs n → Telescope
      ctel-total [] = []
      ctel-total (arg i _ ∷ args) = ("_" , arg i unknown) ∷ ctel-total args

      ctel-free : RemainingArgs n → Telescope
      ctel-free [] = []
      ctel-free (arg i (forced , _) ∷ args) = ctel-free args
      ctel-free (arg i (free   , _) ∷ args) = ("_" , arg i unknown) ∷ ctel-free args

      makeLeftPattern : ∀ {n} → RemainingArgs n → Nat → List (Arg Pattern)
      makeLeftPattern (arg i x ∷ xs) (suc n) = arg i (var n) ∷ makeLeftPattern xs n
      makeLeftPattern _ _ = []

      makeRightPattern : ∀ {n} → RemainingArgs n → Nat → List (Arg Pattern)
      makeRightPattern (arg i (forced , _ , _) ∷ xs) n       = arg i (dot unknown) ∷ makeRightPattern xs n
      makeRightPattern (arg i (free   , _ , _) ∷ xs) (suc n) = arg i (var n) ∷ makeRightPattern xs n
      makeRightPattern _ _ = []

  -- Mismatching constructor case --

  mismatchingClause : (c₁ c₂ : Name) (fs : List Nat) → TC Clause
  mismatchingClause c₁ c₂ fs = do
      tel₁ ← argsTel c₁
      tel₂ ← argsTel c₂
      let #args₁ = length tel₁
          #args₂ = length tel₂
          free-tel₁ = makeFreeTel (#args₁ + #args₂) tel₁
          free-tel₂ = makeFreeTel #args₂ tel₂
          #free-args₁ = length free-tel₁
          #free-args₂ = length free-tel₂
      pure (clause (free-tel₁ ++ free-tel₂)
                   (vArg (con c₁ (makePattern (#args₁ + #args₂) (#free-args₁ + #free-args₂) tel₁)) ∷
                    vArg (con c₂ (makePattern #args₂ #free-args₂ tel₂)) ∷ [])
                   (con (quote no) [ vArg absurd-lam ]))
    where
      makeFreeTel : (k : Nat) → Telescope → Telescope
      makeFreeTel (suc k) ((x , a) ∷ xs) = if (elem k fs) then [] else [ x , (unknown <$ a) ] ++ makeFreeTel k xs
      makeFreeTel _       _              = []

      makePattern : (k : Nat) (n : Nat) (tel : Telescope) → List (Arg Pattern)
      makePattern (suc k) n ((_ , arg i _) ∷ args) =
        if (elem k fs)
        then arg i (dot unknown) ∷ makePattern k n args
        else arg i (var (n - 1)) ∷ makePattern k (n - 1) args
      makePattern k n _                     = []


  -- Clauses --

  makeClause : (c₁ c₂ : Name) → TC (List Clause)
  makeClause c₁ c₂ = case (c₁ == c₂) of λ
    { (yes _) → _∷ [] <$> matchingClause c₁
    ; (no  _) → caseM (unifyIndices c₁ c₂) of λ
      { (positive fs) → _∷ [] <$> mismatchingClause c₁ c₂ (map fst fs)
      ; _             → pure []
      }
    }

  constructorPairs : (d : Name) → TC (List (Name × Name))
  constructorPairs d = caseM getDefinition d of λ
    { (data-type _ cs) → pure $ concat (map (λ c₁ → map (_,_ c₁) cs) cs)
    ; _ → pure []
    }

  eqDefinition : (d : Name) → TC (List Clause)
  eqDefinition d = concat <$> (mapM (uncurry makeClause) =<< constructorPairs d)

  makeArgs : Nat → List (Arg Nat) → List (Arg Term)
  makeArgs n xs = reverse $ map (fmap (λ i → var (n - i - 1) [])) xs

  computeInstanceType : Nat → List (Arg Nat) → Type → Maybe Term
  computeInstanceType n xs (agda-sort _) =
    just (`Eq (var n (makeArgs n xs)))
  computeInstanceType n xs (pi a (abs s b)) =
    pi (hArg (unArg a)) ∘ abs s <$> computeInstanceType (suc n) ((n <$ a) ∷ xs) b
  computeInstanceType _ _ _ = nothing

  computeType : Name → Nat → List (Arg Nat) → Telescope → Telescope → Term
  computeType d n xs is [] =
    telPi (reverse is) $
    def d (makeArgs (n + k) xs) `→ def d (makeArgs (n + k + 1) xs) `→
    def₁ (quote Dec) (var 1 [] `≡ var 0 [])
    where k = length is
  computeType d n xs is ((x , a) ∷ tel) =
    unArg a `→ʰ
    (case computeInstanceType 0 [] (weaken 1 $ unArg a) of
     λ { (just i) → computeType d (1 + n) ((n <$ a) ∷ xs) ((x , iArg (weaken (length is) i)) ∷ weaken 1 is) tel
       ; nothing →  computeType d (1 + n) ((n <$ a) ∷ xs) (weaken 1 is) tel })


eqType : Name → TC Type
eqType d = computeType d 0 [] [] ∘ fst ∘ telView <$> getType d

macro
  deriveEqType : Name → Tactic
  deriveEqType d hole = unifyTC hole =<< (computeType d 0 [] [] ∘ fst ∘ telView <$> getType d)

deriveEqDef : Name → Name → TC ⊤
deriveEqDef i d = defineFun i =<< eqDefinition d

declareEqInstance : Name → Name → TC ⊤
declareEqInstance iname d =
  declareDef (iArg iname) =<< instanceType d (quote Eq)

defineEqInstance : Name → Name → TC ⊤
defineEqInstance iname d = do
  fname ← freshName ("_==[" & show d & "]_")
  declareDef (vArg fname) =<< eqType d
  dictCon ← recordConstructor (quote Eq)
  defineFun iname (clause [] [] (con₁ dictCon (def₀ fname)) ∷ [])
  defineFun fname =<< eqDefinition d
  return _

deriveEq : Name → Name → TC ⊤
deriveEq iname d =
  declareEqInstance iname d >>
  defineEqInstance  iname d
