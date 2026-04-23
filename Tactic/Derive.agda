-- Generic type class dervations. Works with mutually recursive types
-- and can use mutual recursion to satisfy the termination
-- checker. Writing an actual derivation strategy then does not
-- require dealing with any mutual recursion, it is all handled here.
--
-- TODO: This breaks with indexed datatypes that require absurd clauses (e.g. Vec)
--
-- TODO: This is very slow for mutual recursion that nests too deep (e.g. Term)
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

import Data.Bool.ListAction as L
import Data.List as L hiding (any)
import Data.List.NonEmpty as NE
import Data.String as S
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
  _ = Functor-M {M = TC}
  _ = Show-List
  _ = DecEq-×

open ClauseExprM

-- A wrapper chain `[n₁ , n₂ , … , nₖ]` represents the applied type
-- `n₁ (n₂ (… (nₖ dName)))`.
WrapperChain : Set
WrapperChain = List Name

applyChain : WrapperChain → Term → Term
applyChain []       t = t
applyChain (n ∷ ns) t = n ∙⟦ applyChain ns t ⟧

-- Does the a path of the syntax tree of the term match the given
-- wrapper chain applied to `dName`?
matchesChain : WrapperChain → Name → Term → Bool
matchesChain []       dName (def n _)    = ⌊ dName ≟ n ⌋
matchesChain []       _     _            = false
matchesChain (n ∷ ns) dName (def n' args) =
  ⌊ n ≟ n' ⌋ ∧ L.any (λ where (arg _ t) → matchesChain ns dName t) args
matchesChain _        _     _            = false

-- generate the type of the `className dName` instance
genClassType : ℕ → Name → Maybe WrapperChain → TC Type
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

    modifyClassType : Maybe WrapperChain → TypeView → Type
    modifyClassType nothing   (tel , ty) = tyView (tel , className ∙⟦ ty ⟧)
    modifyClassType (just ns) (tel , ty) = tyView (tel , className ∙⟦ applyChain ns ty ⟧)

-- Entry in the translation table: ((chain , target data name) , instance name).
-- The chain applied to the target datatype gives the concrete type whose
-- instance we resolved to `instance name`. An empty chain represents a
-- user-declared base instance for the target itself.
TransEntry : Set
TransEntry = (WrapperChain × Name) × Name

lookupByTerm : List TransEntry → Term → Maybe Name
lookupByTerm l ty = proj₂ <$> L.findᵇ (λ where ((c , t) , _) → matchesChain c t ty) l

-- allChainsTo:
-- Look at the constructors of the argument and return all non-empty
-- wrapper chains `[n₁ , … , nₖ]` together with the mutual-peer name `t`
-- they terminate at, such that some constructor field has a subterm
-- of the form `n₁ (n₂ (… (nₖ t)))`.
private module AllChainsTo (ns : List Name) where
  nameInSeeds : Name → Bool
  nameInSeeds n' = L.any (_≡ᵇ n') ns

  -- All chains from the head of `t` down to some position equal to
  -- some seed in `ns`.
  mutual
    chainsTo : Term → List (WrapperChain × Name)
    chainsTo (def n' args) with nameInSeeds n'
    ... | true  = [ ([] , n') ]
    ... | false = L.map (λ where (c , t) → (n' ∷ c , t)) (chainsToArgs args)
    chainsTo _ = []

    chainsToArgs : List (Arg Term) → List (WrapperChain × Name)
    chainsToArgs []               = []
    chainsToArgs (arg _ t ∷ rest) = chainsTo t ++ chainsToArgs rest

  -- `chainsTo` applied to the term and, recursively, to every
  -- argument position, so nested sub-chains are also collected.
  -- Bare references to seeds themselves are skipped (no helper needed).
  mutual
    allChainsTo : Term → List (WrapperChain × Name)
    allChainsTo t@(def n' args) with nameInSeeds n'
    ... | true  = []
    ... | false = chainsTo t ++ allChainsToArgs args
    allChainsTo _ = []

    allChainsToArgs : List (Arg Term) → List (WrapperChain × Name)
    allChainsToArgs []               = []
    allChainsToArgs (arg _ t ∷ rest) = allChainsTo t ++ allChainsToArgs rest

open AllChainsTo using (allChainsTo)

-- Collect all non-empty wrapper chains (tagged with their terminating
-- seed) discovered in the constructors arguments of the constructors
-- of any seed.
genMutualHelpers : List Name → TC (List (WrapperChain × Name))
genMutualHelpers ns = do
  tysPerSeed ← traverse
    (λ n → L.map (unArg ∘ unAbs) <$> (L.concatMap (proj₁ ∘ viewTy ∘ proj₂) <$> getConstrs n)) ns
  return $ deduplicate _≟_ $ L.concatMap (allChainsTo ns) $ concat tysPerSeed

module _ (arity : ℕ) (genCe : (Term → Maybe Name) → List SinglePattern → List (NE.List⁺ SinglePattern × TC (ClauseExpr ⊎ Maybe Term))) where
  -- Generate the declaration & definition of a particular derivation.
  -- `tgtData` is the target datatype and `wName` is an optional wrapper
  -- chain; the resulting instance has type
  -- `className (applyChain wName tgtData)` and is declared at `iName`.
  -- Base instances (wName ≡ nothing) are declared with `iArg` so they
  -- participate in instance search; helpers (wName ≡ just _) are
  -- declared with `vArg` and referenced explicitly via `transName`.

  deriveSingle : List TransEntry → Name → Name → Maybe WrapperChain → TC (Arg Name × Type × List Clause)
  deriveSingle transName tgtData iName wChain = inDebugPath "DeriveSingle" do
    debugLog ("For: " ∷ᵈ tgtData ∷ᵈ [])
    -- e.g. `⦃ DecEq A ⦄ → DecEq (List (Arg A))` for chain [List,Arg]
    goalTy ← genClassType arity tgtData wChain
    -- we only ever have to pattern-match on the outermost patterns
    -- since we call other instances directly (i.e. we wouldn't match
    -- on `Arg` in the above example, but rather call another helper
    -- `⦃ DecEq A ⦄ → DecEq (Arg A)`)
    let outerName = maybe (λ where [] → tgtData ; (x ∷ _) → x) tgtData wChain
    ps ← constructorPatterns' (outerName ∙)
    -- TODO: find a good way of printing this
    --debugLogᵐ ("Constrs: " ∷ᵈᵐ ps ᵛⁿ ∷ᵈᵐ []ᵐ)
    cs ← local (λ c → record c { goal = inj₂ goalTy }) $
      singleMatchExpr ([] , iArg (Pattern.proj projName)) $ contMatch $ multiMatchExprM $
        genCe (lookupByTerm transName) ps
     -- only names declared by the user should participate in instance search
    let defName = maybe (λ _ → vArg iName) (iArg iName) wChain
    return (defName , goalTy , clauseExprToClauses cs)

  -- Derive all instances for a group of mutually-defined seeds at once,
  -- sharing a single translation table that covers both the user-named
  -- base instances and the fresh wrapper-chain helpers.
  deriveGroup : List (Name × Name) → TC (List (Arg Name × Type × List Clause))
  deriveGroup seeds = do
    -- discover all wrapper-chain helpers needed by any seed's constructors,
    -- e.g. ([List,Arg],Term) when Term has a `List (Arg Term)` field
    helpers ← genMutualHelpers $ L.map proj₁ seeds
    -- generate fresh, human-readable names for the helpers
    helperNames ← traverse ⦃ Functor-List ⦄ mkHelperName helpers
    let helperTable : List TransEntry
        helperTable = L.zip helpers helperNames

        -- seeds get empty-chain entries so cross-seed references are
        -- resolved explicitly rather than relying on instance search
        seedTable : List TransEntry
        seedTable = L.map (λ (s , i) → (([] , s) , i)) seeds

        -- all derivations share a single table so every mutual peer and helper is in scope
        open D (seedTable ++ helperTable)
    baseResults ← traverse deriveBase seeds
    helperResults ← traverse deriveHelper helperTable
    return (baseResults ++ helperResults)
    where
      mkHelperName : WrapperChain × Name → TC Name
      mkHelperName (chain , tgt) = freshName
        (showName className
          S.++ L.foldr (λ n s → "-" S.++ showName n S.++ s) "" chain
          S.++ "-" S.++ showName tgt)

      module D (transName : List (TransEntry)) where
        deriveBase : Name × Name → TC (Arg Name × Type × List Clause)
        deriveBase (s , i) = deriveSingle transName s i nothing

        deriveHelper : TransEntry → TC (Arg Name × Type × List Clause)
        deriveHelper ((chain , tgt) , n) = deriveSingle transName tgt n (just chain)

  derive-Class : ⦃ TCOptions ⦄ → List (Name × Name) → UnquoteDecl
  derive-Class l = initUnquoteWithGoal (className ∙) $
    declareAndDefineFuns =<< runAndReset (deriveGroup l)
