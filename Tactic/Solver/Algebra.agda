------------------------------------------------------------------------
-- Generic core for reflection-based algebraic-structure solvers.
--
-- A `Theory` describes a particular algebraic structure by giving:
--   * the bundle type `R` is expected to inhabit;
--   * its operators (arities + Term patterns to detect them);
--   * an optional `LiteralMatch` for theories with literals;
--   * how to encode them into a backend polynomial AST.

{-# OPTIONS --without-K --safe #-}

module Tactic.Solver.Algebra where

open import Agda.Builtin.Reflection using (withReduceDefs)

open import Data.Bool
open import Data.List as List          using (List; _∷_; []; _++_; replicate; null)
open import Data.Maybe as Maybe        using (Maybe; just; nothing)
open import Data.Nat
open import Data.Nat.Reflection
open import Data.Product
open import Data.Unit
open import Data.Vec                   using (_∷_; [])

open import Function

open import Reflection
open import Reflection.AST.Argument
open import Reflection.AST.DeBruijn
import Reflection.AST.Name as Name
open import Reflection.AST.Term
open import Reflection.TCM.Syntax
open import Reflection.Utils.Args
open import Reflection.Utils.Core
open import Reflection.Utils.Metas
open import Reflection.Utils.TCM

------------------------------------------------------------------------
-- I. Reflection helpers

-- Peels leading λ-binders before reading the head Name.
headName : Term → Maybe Name
headName (def nm _)            = just nm
headName (lam _ (abs _ body))  = headName body
headName _                     = nothing

_≡ᵐ_ : Maybe Name → Maybe Name → Bool
just n  ≡ᵐ just m  = n Name.≡ᵇ m
nothing ≡ᵐ nothing = true
_       ≡ᵐ _       = false

-- For wrapped numeric carriers like ℤ's `+_`: peel one `con C (n ∷ [])` layer.
peelLitCon : Name → Term → Maybe ℕ
peelLitCon C (con nm xs) = case nm Name.≡ᵇ C of λ where
  false → nothing
  true  → case vArgs xs of λ where
    (a ∷ []) → extractNat a
    _        → nothing
peelLitCon _ _ = nothing

extractCarrierNat : Maybe Name → Term → Maybe ℕ
extractCarrierNat mC t = case extractNat t of λ where
  (just n) → just n
  nothing  → case mC of λ where
    (just C) → peelLitCon C t
    nothing  → nothing

------------------------------------------------------------------------
-- II. Theory specification.
--
-- `detect` and `encode` are separated so the macro can collect atoms
-- (which needs operator detection only) before the atom count is
-- known (which `encode` needs).

record OperatorMatch : Set where
  constructor opMatch
  field
    opTerm : Term
    arity  : ℕ

-- For theories with literal coefficients (the ring solvers). Other
-- theories supply `nothing`.
record LiteralMatch : Set where
  constructor litMatch
  field
    -- ℤ-style wrapper (e.g. ℤ's `+_`); `nothing` for unwrapped ℕ-style.
    litCon  : Maybe Name
    peelSuc : Bool

record TheoryDetect : Set where
  field
    -- The order chosen here is the source of truth: `opEncoders` in
    -- `TheoryEncode` must use the same order.
    operatorMatches : List OperatorMatch
    -- Names to feed `withReduceDefs` so the operator boundary stays
    -- opaque while the macro inspects the user's term.
    blockedNames    : List Name
    literalMatch    : Maybe LiteralMatch

record TheoryEncode : Set where
  field
    -- Parallel to `TheoryDetect.operatorMatches`.
    opEncoders  : List (List Term → Term)
    encodeNat   : ℕ → Term
    -- Maps `suc t` to the polynomial Term for `1 + t`.
    sucPeel     : Term → Term
    encodeVar   : ℕ → Term
    encodeEq    : Term → Term → Term
    -- Body has `numAtoms` polynomial-var binders introduced.
    finishSolve : (lambdaBody : Term) (atoms : List Term) → Term

-- Operator match paired with its encoder.
record OperatorEntry : Set where
  field
    opTerm  : Term
    arity   : ℕ
    encode  : List Term → Term

mkOperatorEntry : OperatorMatch → (List Term → Term) → OperatorEntry
mkOperatorEntry (opMatch t a) enc = record { opTerm = t ; arity = a ; encode = enc }

record Theory : Set₁ where
  field
    bundleType : Term
    State : Set
    detect : Term → TC (TheoryDetect × State)
    -- R↓↓ = R weakened past `numPiVars + numAtoms` lambdas (used
    -- inside the polynomial-λ body).
    -- R↓  = R weakened past `numPiVars` (used outside, by `finishSolve`).
    encode : (R↓↓ R↓ : Term) (numAtoms : ℕ) (state : State) → TheoryEncode

------------------------------------------------------------------------
-- III. Operator classification and conversion.

-- Generic classifier: pick the first entry whose `opTerm` has `nm`
-- as its (lambda-peeled) head `def`.
classifyOp : ∀ {A : Set} → (A → Term) → List A → Name → Maybe A
classifyOp _       []       _  = nothing
classifyOp getTerm (a ∷ as) nm =
  if just nm ≡ᵐ headName (getTerm a)
    then just a
    else classifyOp getTerm as nm

-- A projected operator like `def CSR._+_ (R ⟨∷⟩ a ⟨∷⟩ b ⟨∷⟩ [])`
-- carries the bundle as a leading visible arg; this returns how many
-- such prefix args to skip before reaching the operator's last
-- `arity` visibles.
opDrop : ℕ → Args Term → ℕ
opDrop arity xs = visibleCount xs ∸ arity

convertTerm : TheoryDetect → TheoryEncode → (Term → TC Term) → Term → TC Term
convertTerm det enc fallback = convert
  where
  open TheoryDetect det
  open TheoryEncode enc

  ops : List OperatorEntry
  ops = List.zipWith mkOperatorEntry operatorMatches opEncoders

  litCon : Maybe Name
  litCon = Maybe.maybe LiteralMatch.litCon nothing literalMatch

  peelSuc-on : Bool
  peelSuc-on = Maybe.maybe LiteralMatch.peelSuc false literalMatch

  mutual
    convert : Term → TC Term
    convert t = case (literalMatch , extractCarrierNat litCon t) of λ where
      (just _ , just n) → pure (encodeNat n)
      _                 → convertHead t

    convertHead : Term → TC Term
    convertHead t@(def nm xs) = case classifyOp OperatorEntry.opTerm ops nm of λ where
      nothing → fallback t
      (just e) → do
        let open OperatorEntry e
        args ← convertVisibleArgs (opDrop arity xs) xs
        pure (encode args)
    convertHead t@(con (quote suc) (arg (arg-info visible _) x ∷ [])) =
      if peelSuc-on then sucPeel <$> convert x else fallback t
    convertHead t = fallback t

    convertVisibleArgs : ℕ → Args Term → TC (List Term)
    convertVisibleArgs _       []                                = pure []
    convertVisibleArgs (suc d) (arg (arg-info visible _) _ ∷ xs) = convertVisibleArgs d xs
    convertVisibleArgs 0       (arg (arg-info visible _) x ∷ xs) = do
      x'  ← convert x
      xs' ← convertVisibleArgs 0 xs
      pure (x' ∷ xs')
    convertVisibleArgs d       (_ ∷ xs)                          = convertVisibleArgs d xs

collectAtoms : TheoryDetect → Term → List Term → TC (List Term)
collectAtoms det = collect
  where
  open TheoryDetect det

  litCon : Maybe Name
  litCon = Maybe.maybe LiteralMatch.litCon nothing literalMatch

  peelSuc-on : Bool
  peelSuc-on = Maybe.maybe LiteralMatch.peelSuc false literalMatch

  mutual
    collect : Term → List Term → TC (List Term)
    collect t acc = case (literalMatch , extractCarrierNat litCon t) of λ where
      (just _ , just _) → pure acc
      _                 → collectHead t acc

    collectHead : Term → List Term → TC (List Term)
    collectHead (def nm xs) acc = case classifyOp OperatorMatch.opTerm operatorMatches nm of λ where
      nothing → pure (insertAtom (def nm xs) acc)
      (just (opMatch _ arity)) → collectArgs (opDrop arity xs) xs acc
    collectHead t@(con (quote suc) ((arg (arg-info visible _) x ∷ []))) acc =
      if peelSuc-on then collect x acc else pure (insertAtom t acc)
    collectHead t acc = pure (insertAtom t acc)

    collectArgs : ℕ → Args Term → List Term → TC (List Term)
    collectArgs _       []                                acc = pure acc
    collectArgs (suc d) (arg (arg-info visible _) _ ∷ xs) acc = collectArgs d xs acc
    collectArgs 0       (arg (arg-info visible _) x ∷ xs) acc = collect x acc >>= collectArgs 0 xs
    collectArgs d       (_ ∷ xs)                          acc = collectArgs d xs acc

-- Used to seed `withReduceDefs`'s block list with the operator
-- names we'll encounter.
collectOpNames : TheoryDetect → Term → List Name → TC (List Name)
collectOpNames det = collect
  where
  open TheoryDetect det

  mutual
    collect : Term → List Name → TC (List Name)
    collect (def nm xs) acc = case classifyOp OperatorMatch.opTerm operatorMatches nm of λ where
      nothing → pure acc
      (just (opMatch _ arity)) → collectArgs (opDrop arity xs) xs (insertName nm acc)
    collect _ acc = pure acc

    collectArgs : ℕ → Args Term → List Name → TC (List Name)
    collectArgs _       []                                acc = pure acc
    collectArgs (suc d) (arg (arg-info visible _) _ ∷ xs) acc = collectArgs d xs acc
    collectArgs 0       (arg (arg-info visible _) x ∷ xs) acc = collect x acc >>= collectArgs 0 xs
    collectArgs d       (_ ∷ xs)                          acc = collectArgs d xs acc

------------------------------------------------------------------------
-- IV. The generic macro core.

malformedClosedEqError : ∀ {a} {A : Set a} → Term → TC A
malformedClosedEqError found = typeError
  ( strErr "Malformed call to algebraic solver."
  ∷ strErr "Expected target type to be of shape  LHS ≈ RHS."
  ∷ strErr "Instead: "
  ∷ termErr found
  ∷ [])

-- The `nothing` branch is unreachable on well-formed input —
-- `collectAtoms` already inserted every term `convertTerm` will
-- look up — but we error loudly rather than silently emit a default.
private
  atomFB : TheoryEncode → List Term → Term → TC Term
  atomFB enc atoms t = do
    just i ← pure (findAtomIndex t atoms)
      where nothing → typeError
                    ( strErr "Internal error in solve-≈: atom "
                    ∷ termErr t
                    ∷ strErr " was not found in the atom list."
                    ∷ [])
    pure (TheoryEncode.encodeVar enc i)

-- Precondition: `R` has been type-checked against `Theory.bundleType`
-- by the caller (e.g. via `Tactic.Solver.Ring.detectSide`).
solveByTheory : (thy : Theory) → Term → Term → TC ⊤
solveByTheory thy `R hole = do
  det , state ← Theory.detect thy `R
  let bundleNs = TheoryDetect.blockedNames det

  `hole₀ ← inferType hole
  let _ , equation₀ = stripPis `hole₀
  opNames ← case getVisibleArgs 2 equation₀ of λ where
    (just (lhs₀ ∷ rhs₀ ∷ [])) → collectOpNames det lhs₀ bundleNs >>= collectOpNames det rhs₀
    _ → pure bundleNs

  withReduceDefs (false , opNames) $ do
    -- `normalise`, not `reduce`: Agda's elaborator can leave the
    -- goal type wrapped in lambdas that need β-reducing first.
    `hole ← normalise `hole₀
    let variablesAndTypes , equation = stripPis `hole
    let sides = getVisibleArgs 2 equation

    -- Deadlock detection: if some side has a meta not shared with
    -- the other side, `blockOnMeta` would retry forever (only this
    -- macro could resolve it). Shared metas are fine — Agda
    -- propagates constraints across `≈`.
    case sides of λ where
      (just (lhs ∷ rhs ∷ [])) → do
        let bothStructured = not (isMeta lhs) ∧ not (isMeta rhs)
        let metasL         = findMetaIds lhs
        let metasR         = findMetaIds rhs
        let anyMetas       = not (null metasL ∧ null metasR)
        let sharedMeta     = shareMeta metasL metasR
        if bothStructured ∧ anyMetas ∧ not sharedMeta
          then typeError
            ( strErr "solve-≈: the goal `LHS ≈ RHS` has at least one side "
            ∷ strErr "containing a metavariable that could not be resolved. To run this "
            ∷ strErr "solver you must add type annotations to resolve these variables."
            ∷ [])
          else pure tt
      _ → pure tt

    case firstMeta `hole of λ where
      (just m) → blockOnMeta m
      nothing  → pure tt
    let variables = List.map proj₁ variablesAndTypes
    let numPiVars = List.length variables

    just (lhs ∷ rhs ∷ []) ← pure sides
      where nothing → malformedClosedEqError `hole

    atoms₀ ← collectAtoms det lhs []
    atoms  ← collectAtoms det rhs atoms₀
    let numAtoms = List.length atoms

    let `R↓↓ = weaken (numPiVars + numAtoms) `R
    let `R↓  = weaken numPiVars `R
    let enc  = Theory.encode thy `R↓↓ `R↓ numAtoms state

    `lhsExpr ← convertTerm det enc (atomFB enc atoms) lhs
    `rhsExpr ← convertTerm det enc (atomFB enc atoms) rhs

    let open TheoryEncode enc
    let lambdaBody = encodeEq `lhsExpr `rhsExpr
    let f          = prependVLams (replicate numAtoms "x") lambdaBody
    let solverCall = finishSolve f atoms

    -- Re-introduce the pi-binders the user didn't pattern-bind.
    let final = prependVLams variables solverCall
    unify hole final
