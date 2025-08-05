{-# OPTIONS --safe --without-K #-}

module Class.MonadTC where

open import Meta.Prelude

open import Data.List using (map)

import Agda.Builtin.Reflection as R'
import Reflection as R
open import Reflection.Syntax

open import Reflection.Debug

open import Class.Show
open import Class.DecEq
open import Class.MonadReader
open import Class.MonadError
open import Class.Functor
open import Class.Monad
open import Class.Traversable

data ReductionOptions : Set where
  onlyReduce : List Name → ReductionOptions
  dontReduce : List Name → ReductionOptions

reduceAll : ReductionOptions
reduceAll = dontReduce []

record TCOptions : Set where
  field
    debug : DebugOptions
    fuel  : List (String × ℕ)

defaultTCOptions : TCOptions
defaultTCOptions = record
  { debug = defaultDebugOptions
  ; fuel  = [] }

record TCEnv : Set where
  field
    normalisation  : Bool
    reconstruction : Bool
    noConstraints  : Bool
    reduction      : ReductionOptions
    globalContext  : Telescope
    localContext   : Telescope
    goal           : Term ⊎ Type
    options        : TCOptions

  open TCOptions options public

initTCEnvWithGoal : Term → R.TC TCEnv
initTCEnvWithGoal goal = R.getContext <&> λ ctx → record
  { normalisation  = false
  ; reconstruction = false
  ; noConstraints  = false
  ; reduction      = reduceAll
  ; globalContext  = ctx
  ; localContext   = []
  ; goal           = inj₁ goal
  ; options        = defaultTCOptions
  }

initTCEnv : R.TC TCEnv
initTCEnv = initTCEnvWithGoal unknown

record MonadTC (M : ∀ {f} → Set f → Set f)
               ⦃ m : Monad M ⦄ ⦃ me : MonadError (List ErrorPart) M ⦄ : Setω₁ where
  field
    unify            : Term → Term → M ⊤
    typeError        : List ErrorPart → M A
    inferType        : Term → M Type
    checkType        : Term → Type → M Term
    normalise        : Term → M Term
    reduce           : Term → M Term
    quoteTC          : A → M Term
    unquoteTC        : Term → M A
    quoteωTC         : ∀ {A : Setω} → A → M Term
    freshName        : String → M Name
    declareDef       : Arg Name → Type → M ⊤
    declarePostulate : Arg Name → Type → M ⊤
    defineFun        : Name → List Clause → M ⊤
    getType          : Name → M Type
    getDefinition    : Name → M Definition
    blockOnMeta      : Meta → M A
    commitTC         : M ⊤
    isMacro          : Name → M Bool
    debugPrint       : String → ℕ → List ErrorPart → M ⊤
    runSpeculative   : M (A × Bool) → M A
    getInstances     : Meta → M (List Term)

  open MonadError me

  runAndReset : M A → M A
  runAndReset x = runSpeculative ((_, false) <$> x)

  -- dry-run and return true iff no error occured
  -- does not change any state
  isSuccessful : M A → M Bool
  isSuccessful x = runAndReset (catch (x >> return true) (λ _ → return false))

  -- TODO: return true on function, axiom and prim-fun constructors?
  isDef : Name → M Bool
  isDef n = do
    constructor′ _ _ ← getDefinition n
      where _ → return true
    return false

  isCon : Name → M Bool
  isCon n = do
    constructor′ _ _ ← getDefinition n
      where _ → return false
    return true

  nameConstr : Name → List (Arg Term) → M Term
  nameConstr n args = do
    isD ← isDef n
    isC ← isCon n
    case (isD , isC) of λ where
      (true , _)      → return $ def n args
      (false , true)  → return $ con n args
      (false , false) → error ((R'.primShowQName n <+> "is neither a definition nor a constructor!") ∷ᵈ [])

  termFromName : Name → M Term
  termFromName n = nameConstr n []

  -- apply the unique constructor of the record to the arguments
  mkRecord : Name → List (Arg Term) → M Term
  mkRecord n args = do
    (record′ c _) ← getDefinition n
      where _ → error ("Not a record!" ∷ᵈ [])
    return $ con c args

  isSolvedMeta : Term → M Bool
  isSolvedMeta m@(meta x args) = do
    r@(meta y _) ← reduce m
      where _ → return true
    return (x ≠ y)
  isSolvedMeta _ = error ("Not a meta!" ∷ᵈ [])

  hasUnsolvedMetas : Term → M Bool
  hasUnsolvedMetas' : List (Arg Term) → M Bool
  hasUnsolvedMetasCl : List Clause → M Bool
  hasUnsolvedMetasTel : Telescope → M Bool

  hasUnsolvedMetas (var x args) = hasUnsolvedMetas' args
  hasUnsolvedMetas (con c args) = hasUnsolvedMetas' args
  hasUnsolvedMetas (def f args) = hasUnsolvedMetas' args
  hasUnsolvedMetas (lam v (abs _ t)) = hasUnsolvedMetas t
  hasUnsolvedMetas (pat-lam cs args) = do
    a ← hasUnsolvedMetasCl cs
    b ← hasUnsolvedMetas' args
    return (a ∨ b)
  hasUnsolvedMetas (pi (arg _ a) (abs _ b)) = do
    a ← hasUnsolvedMetas a
    b ← hasUnsolvedMetas b
    return (a ∨ b)
  hasUnsolvedMetas (sort (set t)) = hasUnsolvedMetas t
  hasUnsolvedMetas (sort (prop t)) = hasUnsolvedMetas t
  hasUnsolvedMetas (sort unknown) = return true
  hasUnsolvedMetas (sort _) = return false
  hasUnsolvedMetas (lit l) = return false
  hasUnsolvedMetas m@(meta x x₁) = not <$> isSolvedMeta m
  hasUnsolvedMetas unknown = return false

  hasUnsolvedMetas' [] = return false
  hasUnsolvedMetas' ((arg _ x) ∷ l) = do
    a ← hasUnsolvedMetas x
    b ← hasUnsolvedMetas' l
    return (a ∨ b)

  hasUnsolvedMetasCl [] = return false
  hasUnsolvedMetasCl (clause tel _ t ∷ cl) = do
    a ← hasUnsolvedMetas t
    b ← hasUnsolvedMetasTel tel
    c ← hasUnsolvedMetasCl cl
    return (a ∨ b ∨ c)
  hasUnsolvedMetasCl (absurd-clause tel _ ∷ cl) = do
    a ← hasUnsolvedMetasTel tel
    b ← hasUnsolvedMetasCl cl
    return (a ∨ b)

  hasUnsolvedMetasTel [] = return false
  hasUnsolvedMetasTel ((_ , arg _ x) ∷ tel) = do
    a ← hasUnsolvedMetas x
    b ← hasUnsolvedMetasTel tel
    return (a ∨ b)

  -- this allows mutual recursion
  declareAndDefineFuns : List (Arg Name × Type × List Clause) → M ⊤
  declareAndDefineFuns ds = do
    traverse (λ (n , t , _) → declareDef n t) ds
    traverse (λ where (arg _ n , _ , cs) → defineFun n cs) ds
    return _

  declareAndDefineFunsDebug : List (Arg Name × Type × List Clause) → M ⊤
  declareAndDefineFunsDebug ds = do
    traverse (λ (n , t , _) → declareDef n t) ds
    traverse (λ where (arg _ n , _ , _) → do
      b ← getType n >>= hasUnsolvedMetas
      if b then error [ strErr $ show n ] else return tt) ds
    traverse (λ where (arg _ n , _ , cs) → defineFun n cs) ds
    traverse (λ where (arg _ n , _ , _) → do
      d@(function cs) ← getDefinition n
        where _ → error [ strErr "Weird bug" ]
      b ← hasUnsolvedMetasCl cs
      if b then error [ strErr $ show d ] else return tt) ds
    return _

  declareAndDefineFun : Arg Name → Type → List Clause → M ⊤
  declareAndDefineFun n ty cls = declareAndDefineFuns [ (n , ty , cls) ]

  newMeta : Term → M Term
  newMeta = checkType unknown

module _ {M : ∀ {f} → Set f → Set f}
  ⦃ m : Monad M ⦄ ⦃ me : MonadError (List ErrorPart) M ⦄ ⦃ mtc : MonadTC M ⦄ ⦃ mre : MonadReader TCEnv M ⦄ where

  open MonadError me
  open MonadTC mtc
  open MonadReader mre

  record IsMErrorPart (A : Set ℓ) : Setω where
    field toMErrorPart : A → M (List ErrorPart)

  open IsMErrorPart ⦃...⦄ public

  data MErrorPartWrap : Set where
    wrap : M (List ErrorPart) → MErrorPartWrap

  IsMErrorPart-IsErrorPart : ⦃ _ : IsErrorPart A ⦄ → IsMErrorPart A
  IsMErrorPart-IsErrorPart .toMErrorPart a = return [ toErrorPart a ]

  instance
    IsMErrorPart-String : IsMErrorPart String
    IsMErrorPart-String = IsMErrorPart-IsErrorPart

    IsMErrorPart-Term : IsMErrorPart Term
    IsMErrorPart-Term = IsMErrorPart-IsErrorPart

    IsMErrorPart-Name : IsMErrorPart Name
    IsMErrorPart-Name = IsMErrorPart-IsErrorPart

    IsMErrorPart-MErrorPartWrap : IsMErrorPart MErrorPartWrap
    IsMErrorPart-MErrorPartWrap .toMErrorPart (wrap a) = a

  []ᵐ : M (List ErrorPart)
  []ᵐ = return []

  infixr 5 _∷ᵈᵐ_
  _∷ᵈᵐ_ : A → ⦃ _ : IsMErrorPart A ⦄ → M (List ErrorPart) → M (List ErrorPart)
  e ∷ᵈᵐ es = do e ← toMErrorPart e; es ← es; return (e ++ es)

  _ᵛ : A → MErrorPartWrap
  a ᵛ = wrap do a ← quoteTC a; return (a ∷ᵈ [])

  _ᵛⁿ : A → MErrorPartWrap
  a ᵛⁿ = wrap do a ← local (λ env → record env { normalisation = true }) $ quoteTC a; return (a ∷ᵈ [])

  _ᵗ : Term → MErrorPartWrap
  t ᵗ = wrap do T ← inferType t; return (t ∷ᵈ " : " ∷ᵈ T ∷ᵈ [])

  debugLog : List ErrorPart → M ⊤
  debugLog es = do
    record { options = record { debug = debug } } ← ask
    if debug .DebugOptions.filter (debug .DebugOptions.path)
      then debugPrint (debugOptionsPath debug) (debug .DebugOptions.level)
             (debugPrintPrefix debug ∷ es)
      else return tt

  debugLogᵐ : M (List ErrorPart) → M ⊤
  debugLogᵐ x = do x ← x; debugLog x

  debugLog1ᵐ : A → ⦃ _ : IsMErrorPart A ⦄ → M ⊤
  debugLog1ᵐ a = debugLogᵐ (a ∷ᵈᵐ []ᵐ)

  -- withDebugOptions : DebugOptions → M A → M A
  -- withDebugOptions opts x = local (λ where
  --   env@record { debug = opts' } → record env { debug = specializeDebugOptions opts' opts }) x

  withAppendDebugPath : String → M A → M A
  withAppendDebugPath path x = local (λ where
    env@record { options = o@record { debug = opts } } → record env {
      options = record o { debug = record opts { path = opts .DebugOptions.path ∷ʳ path } } }) x

  noConstraints : M A → M A
  noConstraints = local λ e → record e { noConstraints = true }

  hasType : Term → Type → M Bool
  hasType t ty = isSuccessful (noConstraints $ checkType t ty)

  hasType' : Name → Type → M Bool
  hasType' n ty = isSuccessful $ noConstraints $ do
    t ← termFromName n
    t' ← checkType t ty
    if isAppliedToUnknownsAndMetas t'
      then return tt
      else error ("This makes the function return false" ∷ᵈ [])
    where
      isUnknownsAndMetas : List (Arg Term) → Bool
      isUnknownsAndMetas [] = true
      isUnknownsAndMetas (arg i (meta x x₁) ∷ l) = isUnknownsAndMetas l
      isUnknownsAndMetas (arg i unknown ∷ l) = isUnknownsAndMetas l
      isUnknownsAndMetas (arg i _ ∷ l) = false

      isAppliedToUnknownsAndMetas : Term → Bool
      isAppliedToUnknownsAndMetas (var x args)      = isUnknownsAndMetas args
      isAppliedToUnknownsAndMetas (con c args)      = isUnknownsAndMetas args
      isAppliedToUnknownsAndMetas (def f args)      = isUnknownsAndMetas args
      isAppliedToUnknownsAndMetas (pat-lam cs args) = isUnknownsAndMetas args
      isAppliedToUnknownsAndMetas (meta x args)     = isUnknownsAndMetas args
      isAppliedToUnknownsAndMetas _                 = true

  extendContext : String × Arg Type → M A → M A
  extendContext ty = local λ where e@record { localContext = Γ } → record e { localContext = ty ∷ Γ }

  getContext : M Telescope
  getContext = reader λ where
    e@record { localContext = Γ ; globalContext = Γ' } → Γ Data.List.++ Γ'

  getLocalContext : M Telescope
  getLocalContext = reader λ where e@record { localContext = Γ } → Γ

  inContext : Telescope → M A → M A
  inContext ctx = local λ e → record e { localContext = ctx }

  -- extend context by multiple variables
  extendContext' : Telescope → M A → M A
  extendContext' [] x = x
  extendContext' (c ∷ cs) x = extendContext c (extendContext' cs x)

  dropContext : ℕ → M A → M A
  dropContext n x = do
    ctx ← getContext
    inContext (drop n ctx) x

  logAndError : List ErrorPart → M A
  logAndError e = debugLog e >> error e

  error1 : ⦃ IsErrorPart A ⦄ → A → M B
  error1 a = error (a ∷ᵈ [])

  debugLog1 : ⦃ IsErrorPart A ⦄ → A → M ⊤
  debugLog1 a = debugLog (a ∷ᵈ [])

  logAndError1 : ⦃ IsErrorPart A ⦄ → A → M B
  logAndError1 a = debugLog1 a >> error1 a

  markDontFail : String → M A → M A
  markDontFail s x = catch x λ e → logAndError (s ∷ᵈ " should never fail! This is a bug!\nError:\n" ∷ᵈ e)

  goalTy : M Type
  goalTy = do
    inj₁ t ← reader TCEnv.goal
      where inj₂ T → return T
    inferType t

  -- take the first result if it's a just, otherwise reset the state and
  -- run the second computation
  runSpeculativeMaybe : M (Maybe A) → M A → M A
  runSpeculativeMaybe x y = do
    nothing ← runSpeculative (< id , is-just > <$> x)
      where just a → return a
    y

  try : List (M ⊤) → M ⊤ → M ⊤
  try [] e = e
  try (x ∷ cs) e = MonadError.catch me x (λ _ → try cs e)

  getConstrs : Name → M (List (Name × Type))
  getConstrs n = do
    d ← getDefinition n
    cs ← case d of λ where
      (record′ c fs)  → return [ c ]
      (data-type pars cs) → return cs
      _                   → error (n ∷ᵈ "is not a data or record definition!" ∷ᵈ [])
    traverse (λ n → (n ,_) <$> (normalise =<< getType n)) (List Name ∋ cs)

  getConstrsForType : Term → M (List (Name × Type))
  getConstrsForType ty = do
    (def n _) ← normalise ty
      where _ → error (ty ∷ᵈ "does not reduce to a definition!" ∷ᵈ [])
    getConstrs n

  getConstrsForTerm : Term → M (List (Name × Type))
  getConstrsForTerm t = getConstrsForType =<< inferType t

  -- run a TC computation to arrive at the term under the binder for the pattern
  withPattern : Telescope → List (Arg Pattern) → M Term → M Clause
  withPattern tel ps t = Clause.clause tel ps <$> extendContext' tel t

  unifyWithGoal : Term → M ⊤
  unifyWithGoal t = do
    inj₁ t' ← reader TCEnv.goal
      where _ → error1 "unifyWithGoal: Goal is not a term!"
    unify t' t

  runWithHole : Term → M A → M A
  runWithHole t = local (λ env → record env { goal = inj₁ t })

  runWithGoalTy : Term → M A → M A
  runWithGoalTy t = local (λ env → record env { goal = inj₂ t })

  goalHole : M Term
  goalHole = do
    inj₂ T ← reader TCEnv.goal
      where inj₁ hole → return hole
    newMeta T

  withGoalHole : M ⊤ → M Term
  withGoalHole tac = do
    hole ← goalHole
    runWithHole hole tac
    return hole

  -- Finding all instance candidates of a given type.
  findInstances : Type → M (List Term)
  findInstances ty = runAndReset $ do
    just m ← findMeta <$> newMeta ty
      where _ → error1 "[findInstances] newMeta did not produce meta-variable!"
    getInstances m
    where
      open import Data.Maybe using (_<∣>_)
      findMeta = λ where
        (pi (arg _ ty) (abs _ t)) → findMeta ty <∣> findMeta t
        (lam _ (abs _ t))         → findMeta t
        (meta m _)                → just m
        _                         → nothing

MonadTC-TC : MonadTC R.TC ⦃ Monad-TC ⦄ ⦃ MonadError-TC ⦄
MonadTC-TC = record { R; R' using (quoteωTC; withReconstructed; onlyReduceDefs; dontReduceDefs; getInstances) }
