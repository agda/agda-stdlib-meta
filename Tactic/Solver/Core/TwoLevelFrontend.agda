------------------------------------------------------------------------
-- The generic driver for two-level solver frontends: goal syntax
-- whose leaves carry index terms of a second, ordinary
-- `DetectedTheory`, and whose atoms have theory-typed types from
-- which a signature is synthesised.
--
-- The model consumer is a coherence solver for monoidal categories:
-- morphisms are the goal level, and objects are the index level,
-- parsed by `parseGoalTerm` as usual. The driver:
--
--   * parses each goal side at the goal level: operator occurrences
--     recurse on their operands, their `indices` are parsed by the
--     index theory into a shared `SortedAtomStore`, and unrecognised
--     subterms become typed atoms in an α-keyed store;
--   * synthesises the signature: each atom's type is inferred and
--     weak-head reduced, `matchType` extracts its index terms, those
--     are parsed by the index theory, and `encodeSig` builds one
--     signature entry per atom;
--   * assembles the final call from both sides' encodings, the index
--     atoms' spellings, and the signature entries.
--
-- Occurrence parsing is TC-effectful: recognising e.g. a projected
-- bundled iso needs a weak-head reduction of an argument before
-- dispatch. For the same reason an occurrence carries its own
-- encoder, so one head can dispatch to several encodings. Index
-- terms, whose theory keeps the pure `Operator` interface, get the
-- `prepIndex` hook instead. The driver `commitTC`s after its blocking
-- points; consumers must not commit earlier.

{-# OPTIONS --without-K --safe #-}

module Tactic.Solver.Core.TwoLevelFrontend where

open import Data.Bool
open import Data.List as List
open import Data.Maybe as Maybe using (Maybe; just; nothing)
open import Data.Nat
open import Data.Product
open import Data.String using (String)
open import Data.Unit
import Data.Vec as Vec

open import Function

open import Class.Functor
open import Class.Monad.Instances

open import Reflection
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
open import Tactic.Solver.Core.Frontend

------------------------------------------------------------------------
-- I. Goal-level operators.

-- What an occurrence contributes: `operands` are recursed at the
-- goal level, `indices` are parsed by the index theory, and `encode`
-- receives both encoded lists in the same order.
record TwoLevelOccurrence : Set where
  field
    indices  : List Term
    operands : List Term
    encode   : EncodeEnv → (indices operands : List Term) → Term

record TwoLevelOperator : Set where
  field
    -- Pattern: goal subterms whose head Name matches `opTerm`'s
    -- (lambda-peeled) head are occurrences of this operator.
    opTerm   : Term
    -- `nothing` makes the driver atomise the whole subterm.
    parseOcc : Args Term → TC (Maybe TwoLevelOccurrence)

findTwoLevelOperator : List TwoLevelOperator → Name → Maybe TwoLevelOperator
findTwoLevelOperator []       _  = nothing
findTwoLevelOperator (o ∷ os) nm =
  if just nm ≡ᵐ headName (TwoLevelOperator.opTerm o)
    then just o
    else findTwoLevelOperator os nm

------------------------------------------------------------------------
-- Occurrence builders for the common operator shapes.

-- A plain operator: the last `arity` visible arguments are operands,
-- no indices.
fixedArity : (arity : ℕ) → (EncodeEnv → List Term → Term)
           → Args Term → TC (Maybe TwoLevelOccurrence)
fixedArity a enc as =
  pure (Maybe.map occ (takeLast a (vArgs as)))
  where
  occ : Vec.Vec Term a → TwoLevelOccurrence
  occ os = record
    { indices  = []
    ; operands = Vec.toList os
    ; encode   = λ env _ ops → enc env ops
    }

-- An indexed leaf: the last `k` hidden arguments are index terms, no
-- operands.
hiddenIndexLeaf : (k : ℕ) → (EncodeEnv → List Term → Term)
                → Args Term → TC (Maybe TwoLevelOccurrence)
hiddenIndexLeaf k enc as =
  pure (Maybe.map occ (takeLast k (hArgs as)))
  where
  occ : Vec.Vec Term k → TwoLevelOccurrence
  occ is = record
    { indices  = Vec.toList is
    ; operands = []
    ; encode   = λ env ixs _ → enc env ixs
    }

-- The head and argument spine under the last visible argument, after
-- a weak-head reduction — for occurrences of the shape `projection
-- (bundle args)`, where the outer head is the recognised operator and
-- dispatch happens on the bundle's head.
innerDef : Args Term → TC (Maybe (Name × Args Term))
innerDef as = case takeLast 1 (vArgs as) of λ where
  (just (inner Vec.∷ Vec.[])) → do
    inner' ← whnfIfReducible inner
    pure (case inner' of λ where
      (def g ias) → just (g , ias)
      _           → nothing)
  _ → pure nothing

------------------------------------------------------------------------
-- II. What a two-level-theory author writes.

record TwoLevelTheory : Set where
  field
    macroName    : String
    -- The index level: an ordinary theory, parsed by `parseGoalTerm`.
    indexTheory  : DetectedTheory
    -- TC pre-pass applied to every index term (goal-side and
    -- signature-side) before the index theory parses it. The index
    -- theory's `Operator.parseOcc` is pure, so an operator can never
    -- look through a neutral argument; this hook is where such spellings
    -- are reduced/rebuilt onto shapes the pure operators recognise.
    -- `pure` if no preparation is needed.
    prepIndex    : Term → TC Term
    operators    : List TwoLevelOperator
    -- Must cover both levels' operator heads (the index theory's own
    -- `blockedNames` field is not consulted here).
    blockedNames : List Name
    -- The reference emitted for the typed atom at store position `i`.
    atomRef      : EncodeEnv → ℕ → Term
    -- The index terms of an atom's inferred, weak-head-reduced type;
    -- `nothing` is an error.
    matchType    : Term → Maybe (List Term)
    -- One signature entry, from the atom's spelling and its encoded
    -- type indices.
    encodeSig    : EncodeEnv → (atom : Term) → (indices : List Term) → Term
    -- The final call, from the encoded sides, the index atoms'
    -- spellings and the signature entries.
    finishSolve  : EncodeEnv → (lhs rhs : Term)
                 → (indexAtoms sigEntries : List Term) → Term

------------------------------------------------------------------------
-- III. The driver.

private
  fuel : ℕ
  fuel = 1024 -- Should be sufficient for anything practical

module _ (theory : TwoLevelTheory) where
  open TwoLevelTheory theory

  private
    -- (index-theory atoms , typed atoms)
    Stores : Set
    Stores = SortedAtomStore × List Term

    applyEnv : EncodeEnv → List Encoding → List Term
    applyEnv env = List.map (λ e → e env)

    -- Every unrecognised subterm is a typed atom, kept in the α-keyed
    -- store with its original spelling.
    atomiseT : Term → Stores → TC (Encoding × Stores)
    atomiseT orig (ixs , atoms) = do
      let atoms' = insertAtom orig atoms
      -- see `Reflection.Utils.AtomStore` for why insert and index
      -- stay separate traversals
      just i ← pure (findAtomIndex orig atoms')
        where nothing → typeError
                ( strErr macroName
                ∷ strErr ": internal: atom not found after insertion."
                ∷ [])
      pure ((λ env → atomRef env i) , (ixs , atoms'))

    parseIxMany : DetectedTheory → List Term → SortedAtomStore
                → TC (List Encoding × SortedAtomStore)
    parseIxMany det []       acc = pure ([] , acc)
    parseIxMany det (t ∷ ts) acc = do
      t' ← prepIndex t
      e  , acc'  ← parseGoalTerm det t' acc
      es , acc'' ← parseIxMany det ts acc'
      pure (e ∷ es , acc'')

    parseGoal : DetectedTheory → ℕ → Term → Stores → TC (Encoding × Stores)
    parseGoalMany : DetectedTheory → ℕ → List Term → Stores → TC (List Encoding × Stores)

    parseGoal det zero    t st = atomiseT t st
    parseGoal det (suc k) t st = do
      t' ← whnfIfReducible t
      case t' of λ where
        (def nm xs) → case findTwoLevelOperator operators nm of λ where
          nothing  → atomiseT t st
          (just o) → do
            mocc ← TwoLevelOperator.parseOcc o xs
            case mocc of λ where
              nothing    → atomiseT t st
              (just occ) → do
                ies , ixs' ← parseIxMany det (TwoLevelOccurrence.indices occ) (proj₁ st)
                oes , st'' ← parseGoalMany det k (TwoLevelOccurrence.operands occ)
                               (ixs' , proj₂ st)
                pure ( (λ env → TwoLevelOccurrence.encode occ env
                                  (applyEnv env ies) (applyEnv env oes))
                     , st'')
        _ → atomiseT t st

    parseGoalMany det k []       st = pure ([] , st)
    parseGoalMany det k (t ∷ ts) st = do
      e  , st'  ← parseGoal det k t st
      es , st'' ← parseGoalMany det k ts st'
      pure (e ∷ es , st'')

    -- One signature entry per typed atom: infer the atom's type,
    -- extract its index terms, parse them with the index theory.
    sigEntriesOf : DetectedTheory → List Term → SortedAtomStore
                 → TC (List Encoding × SortedAtomStore)
    sigEntriesOf det []       ixs = pure ([] , ixs)
    sigEntriesOf det (b ∷ bs) ixs = do
      ty  ← inferType b
      ty' ← whnfIfReducible ty
      just is ← pure (matchType ty')
        where nothing → typeError
                ( strErr macroName ∷ strErr ": atom " ∷ termErr b
                ∷ strErr " has a type the theory does not recognise: "
                ∷ termErr ty' ∷ [])
      ies , ixs₁ ← parseIxMany det is ixs
      es  , ixs₂ ← sigEntriesOf det bs ixs₁
      pure ((λ env → encodeSig env b (applyEnv env ies)) ∷ es , ixs₂)

    solveTwoLevelEquation : Term → ℕ → Term → TC Term
    solveTwoLevelEquation `R numPiVars equation = do
      lhs , rhs ← requireEquationSides equation
      blockOnEquationMetas equation
      commitTC

      -- Constant patterns were resolved outside the pi-prefix; bring
      -- them to the equation's context.
      let det = record indexTheory
            { constants = List.map
                (λ c → record c { constTerm = weaken numPiVars (Constant.constTerm c) })
                (DetectedTheory.constants indexTheory) }

      lhsE , st₁            ← parseGoal det fuel lhs ([] , [])
      rhsE , (ixs , atoms)  ← parseGoal det fuel rhs st₁
      sigE , ixs'           ← sigEntriesOf det atoms ixs

      let env = record { R↓ = weaken numPiVars `R
                       ; groupSizes = sortedGroupSizes ixs' }
      pure (finishSolve env (lhsE env) (rhsE env)
              (sortedSpellings ixs') (applyEnv env sigE))

  -- Precondition: `R` has been type-checked against the structure's
  -- bundle type by the caller.
  solveByTwoLevelTheory : Term → Term → TC ⊤
  solveByTwoLevelTheory `R hole = solveWith blockedNames (solveTwoLevelEquation `R) hole
