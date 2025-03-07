-- Generic type class dervations. Works with mutually recursive types
-- and can use mutual recursion to satisfy the termination
-- checker. Writing an actual derivation strategy then does not
-- require dealing with any mutual recursion, it is all handled here.
--
-- TODO: This breaks with:
-- - mutual recursion that nests too deep (i.e. deeper than 1, e.g. Term)
-- - indexed datatypes that require absurd clauses (e.g. Vec)
--
-- TODO: support type classes with more than one field
--
-- TODO: enable using existing code for instance when mutually recursing
--
-- TODO: Requires K to pass the termination checker. Maybe we can do without somehow.

{-# OPTIONS -v allTactics:100 #-}
{-# OPTIONS --safe --without-K #-}
open import Meta.Init

module Tactic.Derive (className : Name) (projName : Name) where

open import Meta.Prelude

open import Agda.Builtin.Reflection using () renaming (primShowQName to showName)

import Data.List as L
import Data.Bool.ListAction as LB
import Data.List.NonEmpty as NE
import Data.String as S
open import Data.Maybe using (fromMaybe)
open import Reflection.Tactic
open import Reflection.Utils
open import Reflection.Utils.TCI
open import Relation.Nullary.Decidable
open import Tactic.ClauseBuilder

open import Class.DecEq
open import Class.Functor
open import Class.Monad
open import Class.MonadReader.Instances
open import Class.MonadTC.Instances
open import Class.Show
open import Class.Traversable

instance
  _ = ContextMonad-MonadTC
  _ = Functor-M
  _ = Show-List

open ClauseExprM

-- generate the type of the `className dName` instance
genClassType : ℕ → Name → Maybe Name → TC Type
genClassType arity dName wName = do
  params ← getParamsAndIndices dName
  let params' = L.map (λ where (abs x y) → abs x (hide y)) $ take (length params ∸ arity) params
  sorts ← collectRelevantSorts params'
  debugLog1 ("Generate required instances at indices: " S.++ show (L.map proj₁ sorts))
  let adjustedDBs = L.zipWith (λ (i , tel) a → (i + a , tel)) sorts (upTo (length sorts))
  adjustedDBs' ← extendContext' (toTelescope params) $ genSortInstanceWithCtx adjustedDBs
  let adjParams = params' ++ adjustedDBs'
  debugLog1 "AdjustedParams: "
  logTelescope (L.map ((λ where (abs s x) → just s , x)) adjParams)
  ty ← applyWithVisibility dName (L.map (♯ ∘ (_+ length sorts)) (downFrom (length params)))
  return $ modifyClassType wName (adjParams , ty)
  where
    -- returns list of DB indices (at the end) and telescope of argument types
    collectRelevantSorts : List (Abs (Arg Type)) → TC (List (ℕ × ℕ))
    collectRelevantSorts [] = return []
    collectRelevantSorts (abs x (arg _ t) ∷ l) = do
      rec ← extendContext (x , hArg t) $ collectRelevantSorts l
      (b , k) ← isNArySort t
      return (if b then (length l , k) ∷ rec else rec)

    genSortInstance : ℕ → ℕ → ℕ → TC Term
    genSortInstance k 0 i       = do
      res ← applyWithVisibilityDB (i + k) (L.map ♯ $ downFrom k)
      return $ className ∙⟦ res ⟧
    genSortInstance k (suc a) i = do
      res ← extendContext ("" , hArg unknown) $ genSortInstance k a i
      return $ pi (hArg unknown) $ abs "_" res

    genSortInstanceWithCtx : List (ℕ × ℕ) → TC (List (Abs (Arg Term)))
    genSortInstanceWithCtx [] = return []
    genSortInstanceWithCtx ((i , k) ∷ xs) = do
      x' ← (abs "_" ∘ iArg) <$> (genSortInstance k k i)
      (x' ∷_) <$> (extendContext ("", hArg unknown) $ genSortInstanceWithCtx xs)

    modifyClassType : Maybe Name → TypeView → Type
    modifyClassType nothing  (tel , ty) = tyView (tel , className ∙⟦ ty ⟧)
    modifyClassType (just n) (tel , ty) = tyView (tel , className ∙⟦ n ∙⟦ ty ⟧ ⟧)

lookupName : List (Name × Name) → Name → Maybe Name
lookupName = lookupᵇ (λ n n' → ⌊ n ≟ n' ⌋)

-- Look at the constructors of the argument and return all types that
-- recursively contain it. This isn't very clever right now.
genMutualHelpers : Name → TC (List Name)
genMutualHelpers n = do
  tys ← L.map (unArg ∘ unAbs) <$> (L.concatMap (proj₁ ∘ viewTy ∘ proj₂) <$> getConstrs n)
  return $ deduplicate _≟_ $ L.mapMaybe helper tys
  where
    helper : Type → Maybe Name
    helper (def n' args) =
      if LB.any (λ where (arg _ (def n'' _)) → ⌊ n ≟ n'' ⌋ ; _ → false) args
      then just n' else nothing
    helper _ = nothing

module _ (arity : ℕ) (genCe : (Name → Maybe Name) → List SinglePattern → List (NE.List⁺ SinglePattern × TC (ClauseExpr ⊎ Maybe Term))) where
  -- Generate the declaration & definition of a particular derivation.
  --
  -- Takes a dictionary (for mutual recursion), a wrapper (also for
  -- mutual recursion), the name of the original type we want to derive
  -- Show for and the name we want to define Show originally at.
  deriveSingle : List (Name × Name) → Name → Name → Maybe Name → TC (Arg Name × Type × List Clause)
  deriveSingle transName dName iName wName = inDebugPath "DeriveSingle" do
    debugLog ("For: " ∷ᵈ dName ∷ᵈ [])
    goalTy ← genClassType arity dName wName
    ps ← constructorPatterns' (fromMaybe dName wName ∙)
    -- TODO: find a good way of printing this
    --debugLogᵐ ("Constrs: " ∷ᵈᵐ ps ᵛⁿ ∷ᵈᵐ []ᵐ)
    cs ← local (λ c → record c { goal = inj₂ goalTy }) $
      singleMatchExpr ([] , iArg (Pattern.proj projName)) $ contMatch $ multiMatchExprM $
        genCe (lookupName transName) ps
    let defName = maybe (maybe vArg (iArg iName) ∘ lookupName transName) (iArg iName) wName
    return (defName , goalTy , clauseExprToClauses cs)

  deriveMulti : Name × Name × List Name → TC (List (Arg Name × Type × List Clause))
  deriveMulti (dName , iName , hClasses) = do
    hClassNames ← traverse ⦃ Functor-List ⦄
      (λ cn → freshName (showName className S.++ "-" S.++ showName cn S.++ showName dName)) hClasses
    traverse ⦃ Functor-List ⦄ (deriveSingle (L.zip hClasses hClassNames) dName iName) (nothing ∷ L.map just hClasses)

  derive-Class : ⦃ TCOptions ⦄ → List (Name × Name) → UnquoteDecl
  derive-Class l = initUnquoteWithGoal (className ∙) $
    declareAndDefineFuns =<< runAndReset (concat <$> traverse ⦃ Functor-List ⦄ helper l)
    where
      helper : Name × Name → TC (List (Arg Name × Type × List Clause))
      helper (a , b) = do hs ← genMutualHelpers a ; deriveMulti (a , b , hs)
