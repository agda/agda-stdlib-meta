{-# OPTIONS --safe --without-K #-}

open import Meta.Prelude
open import Meta.Init

open import Class.Monad
open import Class.MonadError.Instances
open import Class.MonadReader.Instances
open import Class.MonadTC.Instances

module Reflection.Utils.TCI
  {M : ∀ {a} → Set a → Set a} ⦃ _ : Monad M ⦄ ⦃ me : MonadError (List ErrorPart) M ⦄
  ⦃ mre : MonadReader TCEnv M ⦄ ⦃ _ : MonadTC M ⦄ where

import Data.Sum
open import Data.List using (map; zipWith)
open import Reflection.Utils
open import Relation.Nullary.Decidable using (⌊_⌋)

open import Class.DecEq
open import Class.Functor
open import Class.Traversable

instance _ = Functor-M

fresh-level : M Level
fresh-level = newMeta (quote Level ∙) >>= unquoteTC

withHole : Type → (Hole → M ⊤) → M Hole
withHole ty k = do
  hole′ ← newMeta ty
  k hole′
  return hole′

apply : Type → Term → List (Arg Term) → M (Type × Term)
apply A t []       = return (A , t)
apply A t (a ∷ as) = do
  A ← reduce A
  A , t ← apply₁ A t a
  apply A t as
  where
    apply₁ : Type → Term → Arg Term → M (Type × Term)
    apply₁ (pi (arg i₁@(arg-info k _) A) B) t₁ (arg i₂ t₂) = do
      a ← fresh-level
      b ← fresh-level
      A ← unquoteTC {A = Set a} A
      B ← unquoteTC {A = A → Set b} (lam visible B)
      t₂ ← unquoteTC {A = A} t₂
      Bt₂ ← quoteTC (B t₂)
      case k of λ where
        visible → do
          t₁ ← unquoteTC {A = ∀ (x : A) → B x} t₁
          Bt₂ ,_ <$> quoteTC (t₁ t₂)
        hidden → do
          t₁ ← unquoteTC {A = ∀ {x : A} → B x} t₁
          Bt₂ ,_ <$> quoteTC (t₁ {x = t₂})
        instance′ → do
          t₁ ← unquoteTC {A = ∀ ⦃ x : A ⦄ → B x} t₁
          Bt₂ ,_ <$> quoteTC (t₁ ⦃ x = t₂ ⦄)
    apply₁ (meta x _) _ _ = blockOnMeta x
    apply₁ A          _ _ = error1 "apply: not a Π-type"

_-∙-_ : Term → Term → M Term
f -∙- x = do
  ty ← inferType f
  proj₂ <$> apply ty f [ vArg x ]

_-∗-_ : Term → List Term → M Term
f -∗- []       = return f
f -∗- (x ∷ xs) = f -∙- x >>= _-∗- xs

instantiate : Hole → M Term
instantiate = reduce >=> normalise

ensureNoMetas : Term → M ⊤
ensureNoMetas = λ where
  (var x args) → noMetaArgs args
  (con c args) → noMetaArgs args
  (def f args) → noMetaArgs args
  (lam v (abs _ t)) → ensureNoMetas t
  (pat-lam cs args) → noMetaClauses cs >> noMetaArgs args
  (pi a b) → noMetaArg a >> noMetaAbs b
  (agda-sort s) → noMetaSort s
  (lit l) → return _
  -- (meta x _) → errorP "meta found!"
  (meta x _) → blockOnMeta x
  unknown → return _
   where
    noMetaArg : Arg Term → M ⊤
    noMetaArg (arg _ v) = ensureNoMetas v

    noMetaArgs : List (Arg Term) → M ⊤
    noMetaArgs [] = return _
    noMetaArgs (v ∷ vs) = noMetaArg v >> noMetaArgs vs

    noMetaClause : Clause → M ⊤
    noMetaClause (clause _ ps t) = ensureNoMetas t
    noMetaClause (absurd-clause _ ps) = return _

    noMetaClauses : List Clause → M ⊤
    noMetaClauses [] = return _
    noMetaClauses (c ∷ cs) = noMetaClause c >> noMetaClauses cs

    noMetaAbs : Abs Term → M ⊤
    noMetaAbs (abs _ v) = ensureNoMetas v

    noMetaSort : Sort → M ⊤
    noMetaSort (set t) = ensureNoMetas t
    noMetaSort _       = return _

module NewMeta where
  unifyStrict : THole → Term → M ⊤
  unifyStrict (hole , ty) x = withAppendDebugPath "unifyStrict" do
    debugLog (hole ∷ᵈ " :=? " ∷ᵈ x ∷ᵈ [])
    m ← newMeta ty
    noConstraints $ unify m x >> unify hole m
    debugLog (hole ∷ᵈ " :=  " ∷ᵈ x ∷ᵈ [])

printTerm : String → Term → M ⊤
printTerm s t = do
  ty ← inferType t
  debugLog
    ( s ∷ᵈ ": {"
    ∷ᵈ ty
    ∷ᵈ " ∋ "
    ∷ᵈ t
    ∷ᵈ "}\n"
    ∷ᵈ [])

module NoMeta where
  unifyStrict : THole → Term → M ⊤
  unifyStrict (hole , ty) x = withAppendDebugPath "unifyStrictNoMeta" do
    -- unify hole x
    -- instantiate hole >>= ensureNoMetas

    debugLog ("———————————————————————————————————————\nx" ∷ᵈ x ∷ᵈ [])
    unify hole x
    hole ← normalise hole
    printTerm "hole′" hole
    -- (x ∷ hole ∷ []) ← mapM instantiate (x ∷ hole ∷ [])
    --   where _ → _IMPOSSIBLE_
    -- printTerm "x′" x
    ensureNoMetas hole
    debugLog1 "No metas found :)\n"

open NewMeta public
-- open NoMeta public

import Data.List.NonEmpty as NE

unifyStricts : THole → List Term → M ⊤
unifyStricts ht = NE.foldl₁ (λ x y → catch x (λ _ → y))
                ∘ (NE._∷ʳ error1 "∅")
                ∘ map ({-noConstraints ∘ -}unifyStrict ht)

compatible? : Type → Type → M Bool
compatible? ty ty′ = do
  -- print $ show ty ◇ " ≈? " ◇ show ty′
  b ← runSpeculative $ (_, false) <$>
    catch (unify (varsToUnknown ty) (varsToUnknown ty′) >> return true)
          (λ _ → return false)
  -- print $ "  ——→ " ◇ show b
  return b

logTelescope : List (Maybe String × Arg Type) → M ⊤
logTelescope l = withAppendDebugPath "context" do
  catch (helper (length l) l) (λ _ → debugLog1 "Error while printing the context!")
  where
    helper : ℕ → List (Maybe String × Arg Type) → M ⊤
    helper n [] = return _
    helper n ((x , ty@(arg _ t)) ∷ l) = do
      let name = case x of λ where
        nothing   → "?"
        (just "") → "_"
        (just x)  → x
      debugLog ("  " ∷ᵈ name ∷ᵈ " : "  ∷ᵈ mapVars (_∸ (n ∸ (1 + length l))) t ∷ᵈ [])
      extendContext (name , ty) $ helper n l

logContext : Telescope → M ⊤
logContext l = withAppendDebugPath "context" do
  debugLog1 "Context:"
  catch (helper (length l) l) (λ _ → debugLog1 "Error while printing the context!")
  catch (do
    goalTy ← goalTy
    debugLog ("  ⊢ " ∷ᵈ goalTy ∷ᵈ []))
    λ _ → do
      inj₁ t ← reader TCEnv.goal
        where _ → error1 "Bug in logContext!"
      debugLog ("Error while infering the goal type! Goal: " ∷ᵈ t ∷ᵈ [])
  where
    helper : ℕ → Telescope → M ⊤
    helper n [] = return _
    helper n ((_ , arg _ t) ∷ l) = do
      helper n l
      debugLog ("  " ∷ᵈ ♯ (n ∸ (length l + 1)) ∷ᵈ " : " ∷ᵈ mapVars (_+ (n ∸ length l)) t ∷ᵈ [])

logCurrentContext : M ⊤
logCurrentContext = markDontFail "logCurrentContext" (logContext =<< getContext)

inDebugPath : String → M A → M A
inDebugPath path x = withAppendDebugPath path do
  debugLog (("*****" <+> path <+> "*****") ∷ᵈ [])
  -- This throws an internal error if the macro is run in a type signature
  -- (Agda issue #7187)
  -- logCurrentContext
  x

viewAndReduceTy : Type → M TypeView
viewAndReduceTy ty = helper ty =<< (length ∘ proj₁ ∘ viewTy) <$> normalise ty
  where
    helper : Type → ℕ → M TypeView
    helper ty    zero = return $ viewTy ty
    helper ty (suc k) with viewTy ty
    ... | (tel , ty') = extendContext' (map (λ where (abs s t) → s , t) tel) $ do
      rTy ← reduce ty'
      (tel' , rTy') ← helper rTy k
      return (tel ++ tel' , rTy')

getType' : Name → M TypeView
getType' n = viewAndReduceTy =<< getType n

getTypeDB : ℕ → M TypeView
getTypeDB n = viewAndReduceTy =<< inferType (♯ n)

getDataDef : Name → M DataDef
getDataDef n = inDebugPath "getDataDef" do
  debugLog ("Find details for datatype: " ∷ᵈ n ∷ᵈ [])
  (data-type pars cs) ← getDefinition n
    where _ → error1 "Not a data definition!"
  debugLogᵐ ("Constructor names: " ∷ᵈᵐ cs ᵛ ∷ᵈᵐ []ᵐ)
  cs' ← traverse ⦃ Functor-List ⦄ (λ n → (n ,_) <$> getType' n) cs
  debugLogᵐ ("Result: " ∷ᵈᵐ cs' ᵛⁿ ∷ᵈᵐ []ᵐ)
  args ← proj₁ <$> getType' n
  return record { name = n ; constructors = cs' ; params = take pars args ; indices = drop pars args }

getRecordDef : Name → M RecordDef
getRecordDef n = do
  (record-type c fs) ← getDefinition n
    where _ → error1 "Not a record definition!"
  args ← proj₁ <$> getType' n
  return (record { name = c ; fields = fs ; params = args })

getDataOrRecordDef : Name → M (DataDef ⊎ RecordDef)
getDataOrRecordDef n =
  catch (inj₁ <$> getDataDef n)
    λ _ → catch (inj₂ <$> getRecordDef n)
    λ _ → error1 "Neither a data not a record definition!"

getParams : Name → M (List (Abs (Arg Type)))
getParams n = Data.Sum.[ DataDef.params , RecordDef.params ] <$> getDataOrRecordDef n

getParamsAndIndices : Name → M (List (Abs (Arg Type)))
getParamsAndIndices n =
  Data.Sum.[ (λ d → DataDef.params d ++ DataDef.indices d) , RecordDef.params ] <$> getDataOrRecordDef n

getFuel : String → M ℕ
getFuel s = do
  fuels ← reader (λ where record { options = record { fuel = f } } → f )
  case lookupᵇ (λ s s' → ⌊ s ≟ s' ⌋) fuels s of λ where
    nothing  → error1 ("Key" <+> s <+> "doesn't exist in the fuels map")
    (just f) → return f

isSort : Term → M Bool
isSort t = do
  (agda-sort _) ← normalise t
    where _ → return false
  return true

isNArySort : Term → M (Bool × ℕ)
isNArySort t = do
  (tel , ty) ← viewAndReduceTy t
  b ← isSort ty
  return (b , length tel)

isDefT : Name → Term → M Bool
isDefT n t = do
  (def n' _) ← normalise t
    where _ → return false
  return ⌊ n ≟ n' ⌋

-- run a computation that returns a term, resetting the TC state but
-- ensuring that the term doesn't contain any metavariables
withSafeReset : M Term → M Term
withSafeReset x = runAndReset $ do
  t ← x
  let m = findMetas t
  if null m
    then return t
    else do
      debugLogᵐ ("Remaining metavariables:" ∷ᵈᵐ m ᵛⁿ ∷ᵈᵐ []ᵐ)
      debugLog ("In term: " ∷ᵈ t ∷ᵈ [])
      error1 "Unsolved metavariables remaining in withSafeReset!"

-- apply a list of terms to a name, picking the correct constructor of the term datatype & visibility
applyWithVisibility : Name → List Term → M Term
applyWithVisibility n l = do
  (argTys , _) ← getType' n
  nameConstr n (zipWith (λ where (abs _ (arg i _)) → arg i) argTys l)

applyWithVisibilityDB : ℕ → List Term → M Term
applyWithVisibilityDB n l = do
  (argTys , _) ← getTypeDB n
  return $ var n (zipWith (λ where (abs _ (arg i _)) → arg i) argTys l)
