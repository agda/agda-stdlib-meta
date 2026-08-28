------------------------------------------------------------------------
-- The generic driver for reflection-based equational-solver
-- frontends: turns a `Theory` (see `Tactic.Solver.Core.Signature`)
-- into a working solver macro. `solveByTheory` takes care of:
--
--   * the goal type: walking under its pi-prefix (type aliases,
--     binder visibility), splitting the equation, and the
--     metavariable retry/error policy;
--   * inspecting the goal without ever normalising it: each step is
--     a weak-head reduction with `blockedNames` opaque, so reduction
--     stops exactly when recognised syntax surfaces;
--   * atoms: unrecognised subterms become solver variables, kept
--     exactly as the user wrote them (a literal like `1ℚ` is never
--     unfolded into the emitted call), deduplicated up to whnf, and
--     grouped by the theory's sort key (see
--     `Tactic.Solver.Core.Indexing` for the binder-index conventions);
--   * encoding both sides and unifying the hole with the assembled
--     solver call.

{-# OPTIONS --without-K --safe #-}

module Tactic.Solver.Core.Frontend where

open import Agda.Builtin.Reflection using (withReduceDefs)

open import Data.Bool
open import Data.List as List
open import Data.Maybe as Maybe using (Maybe; just; nothing; _<∣>_)
open import Data.Nat
open import Data.Product
open import Data.String         using (String)
open import Data.Unit

open import Function

open import Class.Functor
open import Class.Monad.Instances

open import Reflection
open import Reflection.AST.AlphaEquality
open import Reflection.AST.Argument
open import Reflection.AST.DeBruijn
open import Reflection.AST.Term
open import Reflection.TCM.Syntax      hiding (_<$>_)
open import Reflection.Utils.Args
open import Reflection.Utils.Core
open import Reflection.Utils.AtomStore
open import Reflection.Utils.Goal
open import Reflection.Utils.Reduction

open import Tactic.Solver.Core.Indexing
open import Tactic.Solver.Core.Signature

------------------------------------------------------------------------
-- I. Numeral recognition.

-- How a (weak-head-reduced) goal subterm looks through the theory's
-- literal description.
data NumeralView : Set where
  natLit        : ℕ → NumeralView      -- the numeral `n`
  negsucLit     : ℕ → NumeralView      -- the numeral `-(1+n)`
  sucOf         : Term → NumeralView   -- `1# + ⟦payload⟧` (bare or wrapped suc)
  wrappedOpaque : Term → NumeralView   -- wrapper around a non-numeral;
                                       -- payload = whnf key for atomising
  notNumeral    : NumeralView

-- First match wins: numeral, negative numeral, bare `suc`, and —
-- the only TC case, since it must reduce under the wrapper — a
-- wrapper application.
numeralView : Maybe LiteralSpec → Term → TC NumeralView
numeralView nothing   _ = pure notNumeral
numeralView (just ls) t =
  case (natural <∣> negative <∣> bareSuc) of λ where
    (just v) → pure v
    nothing  → wrapper
  where
  open LiteralSpec ls

  natural : Maybe NumeralView
  natural = Maybe.map natLit (extractCarrierNat litCon t)

  negative : Maybe NumeralView
  negative = Maybe.map negsucLit (Maybe.maybe′ (λ C → peelLitCon C t) nothing negLitCon)

  bareSuc : Maybe NumeralView
  bareSuc = case (peelSuc , t) of λ where
    (true , con (quote suc) (arg (arg-info visible _) x ∷ [])) → just (sucOf x)
    _ → nothing

  -- `C (suc n)` peels to `1# + C n`; anything else under the wrapper
  -- is an atom, with the wrapper-of-reduced-tail as its whnf key.
  peelUnderWrapper : Name → Term → TC NumeralView
  peelUnderWrapper C inner = do
    inner' ← whnfIfReducible inner
    pure (case inner' of λ where
      (con (quote suc) (arg (arg-info visible _) x ∷ [])) → sucOf (con C (vArg x ∷ []))
      _ → wrappedOpaque (con C (vArg inner' ∷ [])))

  wrapper : TC NumeralView
  wrapper = case t of λ where
    (con C (arg (arg-info visible _) inner ∷ [])) →
      if peelWrappedSuc ∧ (just C ≡ᵐ litCon)
        then peelUnderWrapper C inner
        else pure notNumeral
    _ → pure notNumeral

------------------------------------------------------------------------
-- II. Parsing a goal side into its deferred backend encoding.

private
  fuel : ℕ
  fuel = 1024 -- Should be sufficient for anything practical

-- An `Encoding` is a backend expression awaiting the `EncodeEnv`
-- (only known once both sides are parsed). Parsing composes the
-- encodings directly — there is no intermediate syntax tree.
Encoding : Set
Encoding = EncodeEnv → Term

-- Parse a goal side, threading the sorted atom store through.
--
-- Each node is brought to weak-head normal form first — the caller
-- wraps this in `withReduceDefs` blocking the theory's names, so whnf
-- stops exactly when an operator, constant or numeral surfaces, while
-- aliases, β-redexes and other definitions unfold. A subterm that
-- exposes none of them is atomised with its original spelling.
--
-- Precondition: the theory's `constants` patterns have been weakened
-- to the context of the parsed term (`solveEquation` weakens them
-- past the goal's pi-prefix) — they are the one place detection
-- compares whole Terms rather than head names.
parseGoalTerm : DetectedTheory → Term → SortedAtomStore → TC (Encoding × SortedAtomStore)
parseGoalTerm det = parse fuel
  where
  open DetectedTheory det

  -- The numeral encodings are only formed when `numeralView` ran
  -- under `just` a literal spec, so the `unknown` fallback is
  -- unreachable.
  litEnc : (LiteralSpec → EncodeEnv → Term) → Encoding
  litEnc f = Maybe.maybe′ f (λ _ → unknown) literalSpec

  sortKeyOf : Term → TC Term
  sortKeyOf t = Maybe.maybe′ (λ f → f t) (pure unknown) sortOf

  -- The bottom of the recogniser cascade: every subterm in which
  -- `parse` finds no theory syntax ends up here. `orig` is the
  -- subterm exactly as the user wrote it — the only form that may
  -- appear in the emitted call; `whnf` is whatever reduced form the
  -- caller already has, used only as the store's second identity key
  -- (never emitted). The store-backed modes (`binder`, `indexed`)
  -- differ only in the reference builder applied to the atom's
  -- (group , slot) position; `embed` splices `orig` directly and
  -- leaves the store untouched.
  atomiseStore : (ref : EncodeEnv → (g s : ℕ) → Term)
               → (orig whnf : Term) → SortedAtomStore → TC (Encoding × SortedAtomStore)
  atomiseStore ref orig whnf acc = do
    key ← sortKeyOf orig
    let acc' = insertSortedStore key (orig , whnf) acc
    -- see `Reflection.Utils.AtomStore` for why we do this
    just (g , s) ← pure (sortedStoreIndex key (orig , whnf) acc')
      where nothing → typeError
                    ( strErr "Internal error in Tactic.Solver.Core: atom "
                    ∷ termErr orig
                    ∷ strErr " not found after insertion."
                    ∷ [])
    pure ((λ env → ref env g s) , acc')

  atomise : (orig whnf : Term) → SortedAtomStore → TC (Encoding × SortedAtomStore)
  atomise orig whnf acc = case atomEmission of λ where
    binder        → atomiseStore atomVar orig whnf acc
    (indexed ref) → atomiseStore ref orig whnf acc
    (embed emb)   → pure ((λ env → emb env orig) , acc)

  findConstant : Term → List Constant → Maybe (EncodeEnv → Term)
  findConstant t []       = nothing
  findConstant t (c ∷ cs) =
    if t =α= Constant.constTerm c then just (Constant.encode c) else findConstant t cs

  -- Constants are only consulted where a subterm would otherwise
  -- atomise; operator heads (`def`-headed by construction) and
  -- constant patterns (headless by construction) are disjoint.
  tryConstant : (orig whnf : Term) → SortedAtomStore → TC (Encoding × SortedAtomStore)
  tryConstant orig whnf acc = case findConstant whnf constants of λ where
    (just enc) → pure (enc , acc)
    nothing    → atomise orig whnf acc

  -- The ℕ argument is recursion-depth fuel (the per-node `reduce`
  -- makes the recursion non-structural); it bounds the *depth* of the
  -- recognised expression structure, so running out — at which point
  -- the subterm is atomised whole — is purely theoretical.
  mutual
    parse : ℕ → Term → SortedAtomStore → TC (Encoding × SortedAtomStore)
    parse zero    t acc = atomise t t acc
    parse (suc k) t acc = do
      t' ← whnfIfReducible t
      nv ← numeralView literalSpec t'
      case nv of λ where
        (natLit n)        → pure (litEnc (λ ls env → LiteralSpec.encodeNat ls env n) , acc)
        (negsucLit n)     → pure (litEnc (λ ls env → LiteralSpec.encodeNegSuc ls env n) , acc)
        (sucOf tail)      →
          (λ (e , acc') → litEnc (λ ls env → LiteralSpec.encodeSucPeel ls env (e env)) , acc')
            <$> parse k tail acc
        (wrappedOpaque w) → atomise t w acc
        notNumeral        → parseHead k t t' acc

    parseHead : ℕ → (orig whnf : Term) → SortedAtomStore → TC (Encoding × SortedAtomStore)
    parseHead k orig t'@(def nm xs) acc = case findOperator operators nm of λ where
      nothing → tryConstant orig t' acc
      (just o) → let open Operator o in case parseOcc xs of λ where
        -- No parseable occurrence (e.g. fewer than `arity` operands in
        -- the spine, possible when the carrier is a function type):
        -- atomise the whole term.
        nothing → atomise orig t' acc
        (just occ) → do
          es , acc' ← parseMany k (Occurrence.operands occ) acc
          pure ((λ env → encode env occ (List.map (λ e → e env) es)) , acc')

    parseHead k orig t' acc = tryConstant orig t' acc

    parseMany : ℕ → List Term → SortedAtomStore
              → TC (List Encoding × SortedAtomStore)
    parseMany k []       acc = pure ([] , acc)
    parseMany k (t ∷ ts) acc = do
      e  , acc'  ← parse k t acc
      es , acc'' ← parseMany k ts acc'
      pure (e ∷ es , acc'')

------------------------------------------------------------------------
-- III. The generic macro core.

private
  -- Build the solver call for the equation, `numPiVars` binders below
  -- the hole's context.
  solveEquation : String → DetectedTheory → Term → ℕ → Term → TC Term
  solveEquation macroName det `R numPiVars equation = do
    lhs , rhs ← requireEquationSides equation
    blockOnEquationMetas equation
    -- Commit now, after every blocking point: a caller-side commit
    -- before the blocks leaves each blocked run's fresh metas in the
    -- global state, and solving one wakes every other blocked solver
    -- call in the declaration — two or more such sites then re-run
    -- each other in an endless cascade.
    commitTC

    -- Constant patterns were resolved outside the pi-prefix; bring
    -- them to the equation's context.
    let det' = record det
          { constants = List.map
              (λ c → record c { constTerm = weaken numPiVars (Constant.constTerm c) })
              (DetectedTheory.constants det) }

    lhsEnc , store₀ ← parseGoalTerm det' lhs []
    rhsEnc , store  ← parseGoalTerm det' rhs store₀
    let atoms    = sortedSpellings store

    let env = record { R↓ = weaken numPiVars `R ; groupSizes = sortedGroupSizes store }
    let open DetectedTheory det
    let lambdaBody = encodeEq env (lhsEnc env) (rhsEnc env)
    let f          = prependVLams (replicate (EncodeEnv.numAtoms env) "x") lambdaBody
    pure (finishSolve env f atoms)

-- Precondition: `R` has been type-checked against the structure's
-- bundle type by the caller (e.g. via
-- `Tactic.Solver.Ring.Core.detectSide`).
solveByTheory : Theory → Term → Term → TC ⊤
solveByTheory thy `R hole = do
  let open Theory thy
  det ← detect `R
  holeTy ← inferType hole
  -- Only the goal *analysis* runs with the theory's names blocked
  final ← withReduceDefs (false , DetectedTheory.blockedNames det)
            (underPis fuel holeTy (solveEquation macroName det `R))
  unify hole final
