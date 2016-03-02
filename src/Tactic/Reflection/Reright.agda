module Tactic.Reflection.Reright where
  open import Prelude
  
  open import Container.Traversable

  open import Tactic.Reflection
  open import Tactic.Reflection.Match
  open import Tactic.Reflection.Replace
  open import Tactic.Reflection.Quote

  private
    {-# TERMINATING #-}
    reorderVars : List Nat → Term → Term
    reorderVars xs (var x args) = var (maybe x id (index xs x)) (fmap (reorderVars xs) <$> args)
    reorderVars xs (con c args) = con c ((fmap ∘ fmap) (reorderVars xs) args)
    reorderVars xs (def f args) = def f (fmap (reorderVars xs) <$> args)
    reorderVars xs (lam v t) = lam v (reorderVars (0 ∷ weaken 1 xs) <$> t)
    reorderVars xs (pat-lam cs args) = pat-lam (fmap (reorderVarsInClause xs) cs) ((fmap ∘ fmap) (reorderVars xs) args) where
      reorderVarsInClause : List Nat → Clause → Clause -- TODO reorder patterns?
      reorderVarsInClause xs (clause ps t) = (clause ps (reorderVars xs t))
      reorderVarsInClause xs (absurd-clause ps) = (absurd-clause ps)
    reorderVars xs (pi a b) = pi (reorderVars xs <$> a) (reorderVars (0 ∷ weaken 1 xs) <$> b)
    reorderVars xs (agda-sort (set t)) = agda-sort (set (reorderVars xs t))
    reorderVars xs (agda-sort (lit n)) = agda-sort (lit n)
    reorderVars xs (agda-sort unknown) = agda-sort unknown
    reorderVars xs (lit l) = lit l
    reorderVars xs (meta x args) = meta x $ (fmap ∘ fmap) (reorderVars xs) args
    reorderVars xs unknown = unknown

    {-# TERMINATING #-}
    freeDependencies : List (Arg Type) → Type → Maybe VarSet
    freeDependencies Γ x = foldr _∪_ (freeVars x) <$> mapM go (freeVars x) where
      _∪_ : VarSet → VarSet → VarSet -- REFACTOR this was stolen from Tactic.Reflection.Free
      []       ∪ ys = ys
      xs       ∪ [] = xs
      (x ∷ xs) ∪ (y ∷ ys) with compare x y
      ... | (less    _) = x ∷ (xs ∪ (y ∷ ys))
      ... | (equal   _) = x ∷ (xs ∪ ys)
      ... | (greater _) = y ∷ ((x ∷ xs) ∪ ys)
     
      go : Nat → Maybe VarSet
      go v = weaken (suc v) $ join $ freeDependencies (drop (suc v) Γ) <$> (unArg <$> index Γ v)

    .test-freeDependencies₁ : freeDependencies [] unknown ≡ just []
    test-freeDependencies₁ = refl

    .test-freeDependencies₂ : freeDependencies (vArg (var₀ 0) ∷ vArg unknown ∷ []) (var₀ 0) ≡ just (0 ∷ 1 ∷ [])
    test-freeDependencies₂ = refl

    .test-freeDependencies₃ : freeDependencies (vArg (var₀ 0) ∷ vArg (var₀ 1) ∷ vArg unknown ∷ vArg unknown ∷ []) (var₀ 0) ≡ just (0 ∷ 1 ∷ 3 ∷ [])
    test-freeDependencies₃ = refl

    .test-freeDependencies₄ : freeDependencies (vArg (var₀ 0) ∷ vArg (var₀ 1) ∷ vArg unknown ∷ vArg unknown ∷ []) (var₀ 1) ≡ just (1 ∷ 3 ∷ [])
    test-freeDependencies₄ = refl

    .test-freeDependencies₅ : freeDependencies (vArg (var₀ 1) ∷ vArg unknown ∷ vArg unknown ∷ []) (var₀ 0) ≡ just (0 ∷ 2 ∷ [])
    test-freeDependencies₅ = refl

    .test-freeDependencies₆ : freeDependencies (vArg (var₀ 0) ∷ vArg (var₀ 1) ∷ vArg unknown ∷ vArg unknown ∷ []) (var₁ 0 (var₀ 1)) ≡ just (0 ∷ 1 ∷ 3 ∷ [])
    test-freeDependencies₆ = refl

    record Request : Set where
      field
        l≡r : Term
        A : Type
        L R : Type
        Γᶜ : List (Arg Type)
        𝐺 : Type

      [iᶜ∣iᶜ∈FVᴬ] : VarSet
      [iᶜ∣iᶜ∈FVᴬ] = maybe [] id $ freeDependencies Γᶜ A -- TODO this is a hack; I don't expect freeDependencies will return 'nothing', but if it does, I hope(!) the rest of the computation will fail
      
      [iᶜ∣iᶜ∉FVᴬ] : VarSet
      [iᶜ∣iᶜ∉FVᴬ] = filter (not ∘ flip elem [iᶜ∣iᶜ∈FVᴬ]) (from 0 for (length Γᶜ))

      record γᶜ' : Set where
        field
          iᶜ : Nat
          γᶜᵢ : Arg Type
          iᶜ∈FVᴬ : Bool
          iʷ : Nat
          γᶜᵢ∈Γʳ : Bool
   
        gᶜᵢ : Type
        gᶜᵢ = unArg γᶜᵢ

      {-# TERMINATING #-}
      Γᶜ' : List γᶜ'
      Γᶜ' = go 0 Γᶜ where
        go : Nat → List (Arg Type) → List γᶜ'
        go iᶜ [] = []
        go iᶜ (γᶜᵢ ∷ Γᶜ) = γᶜᵢ' ∷ go (suc iᶜ) (weaken 1 Γᶜ) where
          γᶜᵢ' = record
            { iᶜ = iᶜ
            ; γᶜᵢ = γᶜᵢ
            ; iᶜ∈FVᴬ = elem iᶜ [iᶜ∣iᶜ∈FVᴬ]
            ; iʷ = if elem iᶜ [iᶜ∣iᶜ∉FVᴬ] then (length (filter (_<? iᶜ) [iᶜ∣iᶜ∉FVᴬ])) else (length [iᶜ∣iᶜ∉FVᴬ] + (length (filter (_≤? iᶜ) [iᶜ∣iᶜ∈FVᴬ])))
            ; γᶜᵢ∈Γʳ = let gᶜᵢ = unArg γᶜᵢ in (isNo $ weaken 1 gᶜᵢ == weaken 1 gᶜᵢ r[ unknown / L ]) && (isNo $ l≡r == var₀ iᶜ)
            }

      [iʷ∣γᶜᵢ∈Γʳ] : VarSet
      [iʷ∣γᶜᵢ∈Γʳ] = iʷ <$> filter γᶜᵢ∈Γʳ Γᶜ' where open γᶜ'

      [iʷ] : List Nat
      [iʷ] = iʷ <$> Γᶜ' where open γᶜ'

      subsetList : {A : Set} → List A → List Nat → Maybe (List A)
      subsetList xs is = traverse (index xs) is

      module _ where
        private
          Γʷ/ᶜ : Maybe (List (Arg Type))
          Γʷ/ᶜ = go 0 [iʷ] Γᶜ where
            go : Nat → List Nat → List (Arg Type) → Maybe (List (Arg Type))
            go _ _ [] = just []
            go _ [] _ = nothing
            go m (_ ∷ [iʷ]) (γᶜᵢ ∷ Γᶜ) = _∷_ <$> (strengthen (suc m) $ reorderVars [iʷ] <$> γᶜᵢ) <*> (go (suc m) [iʷ] $ Γᶜ)

        Γʷ/ᴬ = join $ strengthen 1 $ join $ subsetList <$> Γʷ/ᶜ <*> pure [iᶜ∣iᶜ∈FVᴬ]
        Γʷ/⁻ᴬ = join $ subsetList <$> Γʷ/ᶜ <*> pure [iᶜ∣iᶜ∉FVᴬ]
        
      module _ where
        private
          Lʷ = reorderVars [iʷ] L

        Γʷ = caseF Γʷ' of _R[ var₀ (length [iᶜ∣iᶜ∉FVᴬ]) / Lʷ ] where
          Γʷ' : Maybe (List (Arg Type))
          Γʷ' = _++_ <$> Γʷ/⁻ᴬ <*> (_∷_ <$> (strengthen (length [iᶜ∣iᶜ∉FVᴬ] + 1) $ hArg (reorderVars [iʷ] A)) <*> Γʷ/ᴬ) where
   
        𝐺ʷ = reorderVars [iʷ] 𝐺 r[ var₀ (length [iᶜ∣iᶜ∉FVᴬ]) / Lʷ ]

      module _ where
        private
          Rʷ = reorderVars [iʷ] R

        gʳ : Maybe Type
        gʳ = join $ go <$> gʳ' <*> pure [iʷ∣γᶜᵢ∈Γʳ] <*> pure 𝐺ʷʳ where
          go : List (Arg Type) → List Nat → Type → Maybe Type
          go [] [] 𝐺 = just 𝐺
          go (γʷ ∷ Γʷ) (iʷ ∷ iʷs) 𝐺 = go Γʷ iʷs $ pi (weaken (1 + iʷ) γʷ) $ abs "_" $ weaken 1 𝐺 r[ var₀ 0 / var₀ $ weaken 1 iʷ ]
          go _ _ _ = nothing
   
          gʳ' : Maybe (List (Arg Type))
          gʳ' = join $ subsetList <$> (caseF Γʷ of _R[ Rʷ / var₀ (length [iᶜ∣iᶜ∉FVᴬ]) ]) <*> pure [iʷ∣γᶜᵢ∈Γʳ]
   
          𝐺ʷʳ = 𝐺ʷ r[ Rʷ / var₀ (length [iᶜ∣iᶜ∉FVᴬ]) ]
        
        helper-type : Maybe Type
        helper-type = telPi <$> (_++_ <$> (reverse <$> Γʷ) <*> (_∷_ <$> (pure $ vArg (def₂ (quote _≡_) (var₀ (length [iᶜ∣iᶜ∉FVᴬ])) Rʷ)) <*> ([_] ∘ vArg <$> (weaken 1 <$> gʳ)))) <*> pure (weaken 2 𝐺ʷ)

      make-vars-from-args : List Nat → List (Arg Type) → Maybe (List (Arg Type))
      make-vars-from-args [] [] = pure []
      make-vars-from-args (i ∷ is) (x ∷ xs) = _∷_ <$> pure (var₀ i <$ x) <*> make-vars-from-args is xs
      make-vars-from-args _ _ = nothing
      
      defineHelper : Name → TC ⊤
      defineHelper n =
        maybe (typeError [ strErr "error constructing helper function type, patterns, or term" ]) 
              (λ {(helper-type , helper-patterns , helper-term) →
                catchTC
                  (define (vArg n) helper-type [ clause helper-patterns helper-term ])
                  (typeError ( strErr "error defining helper function" ∷
                               strErr "\nhelper-type:" ∷ termErr helper-type ∷
                               strErr "\n`helper-type:" ∷ termErr (` helper-type) ∷
                               strErr "\nhelper-patterns:" ∷ termErr (` helper-patterns) ∷
                               strErr "\nhelper-term:" ∷ termErr helper-term ∷
                               strErr "\ngʳ:" ∷ termErr (` gʳ) ∷
                               strErr "\nΓʷ:" ∷ termErr (` Γʷ) ∷
                               strErr "\n𝐺ʷ:" ∷ termErr (` 𝐺ʷ) ∷
                               strErr "\nl≡r:" ∷ termErr (` l≡r) ∷
                               strErr "\nA:" ∷ termErr (` A) ∷
                               strErr "\nL:" ∷ termErr (` L) ∷
                               strErr "\nR:" ∷ termErr (` R) ∷
                               strErr "\nΓᶜ:" ∷ termErr (` Γᶜ) ∷
                               strErr "\n𝐺:" ∷ termErr (` 𝐺) ∷
                               strErr "\nΓʷ/ᴬ" ∷ termErr (` Γʷ/ᴬ) ∷
                               strErr "\nΓʷ/⁻ᴬ" ∷ termErr (` Γʷ/⁻ᴬ) ∷
                               strErr "\n[iᶜ∣iᶜ∈FVᴬ]" ∷ termErr (` [iᶜ∣iᶜ∈FVᴬ]) ∷
                               strErr "\n[iᶜ∣iᶜ∉FVᴬ]" ∷ termErr (` [iᶜ∣iᶜ∉FVᴬ]) ∷
                               strErr "\n[iʷ]" ∷ termErr (` [iʷ]) ∷
                               [] ))
                  })
              (_,_ <$> helper-type <*> (_,_ <$> helper-patterns <*> helper-term))
        where
        
        helper-patterns : Maybe (List (Arg Pattern))
        helper-patterns = (λ pa w p-a pr → pa ++ w ∷ (p-a ++ pr)) <$> (telePat ∘ reverse <$> Γʷ/ᴬ) <*> just (hArg dot) <*> (telePat ∘ reverse <$> Γʷ/⁻ᴬ) <*> pure (vArg (con₀ (quote refl)) ∷ [ vArg (var "_") ])

        helper-term : Maybe Term
        helper-term = 
          γʷs ← join $ subsetList <$> Γʷ <*> pure [iʷ∣γᶜᵢ∈Γʳ] -|
          iʷs ← make-vars-from-args [iʷ∣γᶜᵢ∈Γʳ] γʷs -|
          pure $ var 0 (reverse (weaken 1 iʷs))

      callHelper : Name → Tactic
      callHelper n hole =
        maybe (typeError [ strErr "error constructing helper call" ])
              (unify hole)
              $ helper-call n
        where
        
        helper-call : Name → Maybe Term
        helper-call n = def n <$> (reverse <$> (_∷_ <$> pure (vArg l≡r) <*> Γʰ)) where
          Γʰ : Maybe $ List $ Arg Term
          Γʰ = (λ xs → take (length [iᶜ∣iᶜ∉FVᴬ]) xs ++ hArg unknown ∷ drop (length [iᶜ∣iᶜ∉FVᴬ]) xs) <$> (join $ make-vars-from-args <$> pure ([iᶜ∣iᶜ∉FVᴬ] ++ [iᶜ∣iᶜ∈FVᴬ]) <*> Γʰ') where
            Γʰ' : Maybe (List (Arg Type))
            Γʰ' = _++_ <$> subsetList Γᶜ [iᶜ∣iᶜ∉FVᴬ] <*> subsetList Γᶜ [iᶜ∣iᶜ∈FVᴬ]
     
    inferGoal : Term → TC Type
    inferGoal hole = unPi =<< forceFun =<< inferType hole where
      unPi : Type → TC Type
      unPi (pi _ (abs _ (meta x _))) = blockOnMeta! x
      unPi (pi _ (abs _ b)) = maybe (typeError (strErr "error strengthening" ∷ termErr b ∷ [])) pure $ strengthen 1 b
      unPi x = typeError (strErr "goal is not a pi type" ∷ termErr x ∷ [])

    getRequest : Term → Term → TC Request
    getRequest l≡r hole = do
      L≡R ← inferType l≡r -|
      L≡R-matched ← maybe (typeError (strErr "not an equality" ∷ termErr l≡r ∷ termErr L≡R ∷ [])) pure $
        match 3 (def (quote _≡_) (hArg unknown ∷ (hArg (var₀ 0)) ∷ (vArg (var₀ 1)) ∷ (vArg (var₀ 2)) ∷ [])) L≡R -|
      𝐺 ← inferGoal hole -|
      Γᶜ ← getContext -|
      case L≡R-matched of λ { (A ∷ L ∷ R ∷ []) →
        pure $ record { l≡r = l≡r ; A = A ; L = L ; R = R ; Γᶜ = Γᶜ ; 𝐺 = 𝐺 } }

  macro
    reright : Term → Tactic
    reright l≡r hole =
      q ← getRequest l≡r hole -|
      n ← freshName "reright" -|
      let open Request q in 
      defineHelper n ~|
      callHelper n hole
