------------------------------------------------------------------------
-- A reflection-based ring solver for `CommutativeSemiring`.
--
-- `solve-≈` instantiates `Algebra.Solver.Ring.NaturalCoefficients.Default R`
-- (ℕ coefficients, no negation) by reflecting the user's bundle into
-- the polynomial AST and discharging the resulting equation.
--
-- Built on `Tactic.Solver.Algebra`. For a new structure (monoid,
-- lattice, …), write a fresh `Theory` and macro alongside this one.

{-# OPTIONS --without-K --safe #-}

module Tactic.Solver.Ring where

open import Algebra using (CommutativeSemiring)

open import Data.Bool                  using (Bool; true; false)
open import Data.Fin                   using (Fin)
open import Data.List as List          using (List; _∷_; []; map; foldr; length; drop; zip; filterᵇ; reverse)
open import Data.Maybe as Maybe        using (Maybe; just; nothing; maybe)
open import Data.Nat                   using (ℕ; suc; zero)
import Data.Vec as Vec
open import Data.Nat.Reflection
open import Data.Product               using (_,_; _×_; proj₁; proj₂; uncurry)
open import Data.Unit

open import Function

open import Class.Functor
open import Class.Monad.Instances
open import Class.Traversable

open import Reflection
open import Reflection.AST.Argument
import Reflection.AST.Name as Name
open import Reflection.AST.Term
open import Reflection.TCM.Syntax      hiding (_<$>_)
open import Reflection.Utils.Args      using (vArgs; takeFirst)
open import Reflection.Utils.Core      using (extractNat; pickDefName)
open import Reflection.Utils.TCM       using (headReduce)

open import Tactic.Solver.Algebra

------------------------------------------------------------------------
-- `Algebra.Solver.Ring.Polynomial`'s `con`, `var`, and `:-_` are
-- nested constructors inside a four-parameter module. Defining
-- top-level aliases lets the macro reflect them by name (with just
-- `R` as the visible argument) rather than reconstructing all four
-- module parameters.

module Solver {c ℓ} (R : CommutativeSemiring c ℓ) where
  open import Algebra.Solver.Ring.NaturalCoefficients.Default R public

  conP : ∀ {n} → ℕ → Polynomial n
  conP = con

  varP : ∀ {n} → Fin n → Polynomial n
  varP = var

------------------------------------------------------------------------
-- Backend reflection helpers (private).

private
  data LitStyle : Set where
    natStyle    : LitStyle           -- bare ℕ literals; peel `suc`.
    wrapped     : Name → LitStyle    -- `con C ⟨ n ⟩` (e.g. ℤ's `+_`).

  -- Threaded from `detect` to `encode`.
  record RingState : Set where
    field
      litStyle : Maybe LitStyle

------------------------------------------------------------------------
-- Operator-projection Terms from the user's bundle.

private
  projTerm : Name → Term → Term
  projTerm nm R = def nm (2 ⋯⟅∷⟆ R ⟨∷⟩ [])

  csrAdd  csrMul  csrZero csrOne  : Name
  csrAdd  = quote CommutativeSemiring._+_
  csrMul  = quote CommutativeSemiring._*_
  csrZero = quote CommutativeSemiring.0#
  csrOne  = quote CommutativeSemiring.1#

  `CommutativeSemiring : Term
  `CommutativeSemiring = def (quote CommutativeSemiring) (2 ⋯⟨∷⟩ [])

------------------------------------------------------------------------
-- Polynomial-AST Term builders. Calling shape:
--   `def NAME (2 hidden + R-bundle ⟨∷⟩ numVars ⟅∷⟆ ⟨args…⟩)`,
-- pulling NAMEs from `Solver.*`.

private
  defP : (R `n : Term) → Name → List (Arg Term) → Term
  defP R `n nm args =
    def nm (2 ⋯⟅∷⟆ R ⟨∷⟩ `n ⟅∷⟆ args)

  `con : (R `n : Term) → Term → Term
  `con R `n c = defP R `n (quote Solver.conP) (c ⟨∷⟩ [])

  `var : (R `n : Term) → Term → Term
  `var R `n i = defP R `n (quote Solver.varP) (i ⟨∷⟩ [])

  `:+ : (R `n : Term) → Term → Term → Term
  `:+ R `n x y = defP R `n (quote Solver._:+_) (x ⟨∷⟩ y ⟨∷⟩ [])

  `:* : (R `n : Term) → Term → Term → Term
  `:* R `n x y = defP R `n (quote Solver._:*_) (x ⟨∷⟩ y ⟨∷⟩ [])

  `:= : (R `n : Term) → Term → Term → Term
  `:= R `n x y = defP R `n (quote Solver._:=_) (x ⟨∷⟩ y ⟨∷⟩ [])

  `refl : (R : Term) → Term
  `refl R = def (quote CommutativeSemiring.refl) (2 ⋯⟅∷⟆ R ⟨∷⟩ 1 ⋯⟅∷⟆ [])

------------------------------------------------------------------------
-- Literal-style recognition from the bundle's `0#` and `1#` Terms.

private
  detectLitStyle : Term → Term → Maybe LitStyle
  detectLitStyle (con cz argsZ) (con co argsO) =
    case (cz Name.≡ᵇ co) of λ where
      true → case (vArgs argsZ , vArgs argsO) of λ where
        ((z₀ ∷ []) , (o₀ ∷ [])) → case (extractNat z₀ , extractNat o₀) of λ where
          (just 0 , just 1) → just (wrapped cz)
          _ → fallthrough
        _ → fallthrough
      false → fallthrough
    where
    fallthrough : Maybe LitStyle
    fallthrough = case (extractNat (con cz argsZ) , extractNat (con co argsO)) of λ where
      (just 0 , just 1) → just natStyle
      _ → nothing
  detectLitStyle z o = case (extractNat z , extractNat o) of λ where
    (just 0 , just 1) → just natStyle
    _ → nothing

------------------------------------------------------------------------
-- Operator detection: concrete record peek + abstract-projection
-- fallback.

private
  collectDefNames : List Term → List Name
  collectDefNames = List.foldr pickDefName []

  -- A slot's role. `op` is a generic concrete operator field;
  -- `zeroLit` and `oneLit` mark literals. (`derived` exists for
  -- structures with non-field operators; CSR has none.)
  data SlotKind : Set where
    op zeroLit oneLit derived : SlotKind

  -- An operator slot: `(projection-name , arity , kind)`. The slot
  -- order is the source of truth for `operatorMatches` (and so must
  -- align with `opEncoders` in `mkEncode`).
  Slot : Set
  Slot = Name × ℕ × SlotKind

  slotProj : Slot → Name
  slotProj s = proj₁ s

  slotArity : Slot → ℕ
  slotArity s = proj₁ (proj₂ s)

  slotKind : Slot → SlotKind
  slotKind s = proj₂ (proj₂ s)

  slotIsConcrete : Slot → Bool
  slotIsConcrete s with slotKind s
  ... | derived = false
  ... | _       = true

  csrSlots : List Slot
  csrSlots = (csrAdd  , 2 , op)
           ∷ (csrMul  , 2 , op)
           ∷ (csrZero , 0 , zeroLit)
           ∷ (csrOne  , 0 , oneLit)
           ∷ []

  mkLitMatch : Maybe LitStyle → Maybe LiteralMatch
  mkLitMatch nothing             = nothing
  mkLitMatch (just natStyle)     = just (litMatch nothing  true)
  mkLitMatch (just (wrapped C))  = just (litMatch (just C) false)

  -- Pull the `0` and `1` slot Terms by kind. Returns `nothing` if
  -- either is missing from the slot list.
  findZeroOne : List (Slot × Term) → Maybe (Term × Term)
  findZeroOne = go nothing nothing
    where
    go : Maybe Term → Maybe Term → List (Slot × Term) → Maybe (Term × Term)
    go (just z) (just o) _  = just (z , o)
    go _        _        [] = nothing
    go mz mo ((s , t) ∷ rest) with slotKind s
    ... | zeroLit = go (just t) mo rest
    ... | oneLit  = go mz (just t) rest
    ... | _       = go mz mo rest

  detectCSR : Term → TC (TheoryDetect × RingState)
  detectCSR R = do
    R' ← headReduce 16 R
    let slots         = csrSlots
    let concreteN     = length (filterᵇ slotIsConcrete slots)
    case R' of λ where
      (con _ args) → case Maybe.map Vec.toList (takeFirst concreteN (drop 2 (vArgs args))) of λ where
        (just rawOps) → do
          concOps ← traverse ⦃ Functor-List ⦄ (headReduce 16) rawOps
          slotted ← zipSlots slots concOps
          let blockNs = collectDefNames concOps
          let ls = maybe (uncurry detectLitStyle) nothing (findZeroOne slotted)
          pure
            ( record
                { operatorMatches = List.map (λ (s , t) → opMatch t (slotArity s)) slotted
                ; blockedNames    = blockNs
                ; literalMatch    = mkLitMatch ls
                }
            , record { litStyle = ls }
            )
        nothing → abstractPath slots
      _ → abstractPath slots
    where
    zipSlots : List Slot → List Term → TC (List (Slot × Term))
    zipSlots []         _   = pure []
    zipSlots (s ∷ rest) ops = case slotKind s of λ where
      derived → do
        t ← normalise (projTerm (slotProj s) R)
        rs ← zipSlots rest ops
        pure ((s , t) ∷ rs)
      _ → case ops of λ where
        (t ∷ ops') → do
          rs ← zipSlots rest ops'
          pure ((s , t) ∷ rs)
        [] → pure []

    abstractPath : List Slot → TC (TheoryDetect × RingState)
    abstractPath slots = do
      ts ← traverse ⦃ Functor-List ⦄ normalise (List.map (λ s → projTerm (slotProj s) R) slots)
      pure
        ( record
            { operatorMatches = List.map (λ (s , t) → opMatch t (slotArity s)) (zip slots ts)
            ; blockedNames    = []
            ; literalMatch    = nothing
            }
        , record { litStyle = nothing }
        )

------------------------------------------------------------------------
-- Encoder construction.

private
  mkEncode : (R↓↓ R↓ : Term)
           → (numAtoms : ℕ) → Maybe LitStyle → TheoryEncode
  mkEncode R↓↓ R↓ numAtoms litStyle = record
    { opEncoders  = opAdd ∷ opMul ∷ opZero ∷ opOne ∷ []
    ; encodeNat   = encNat
    ; sucPeel     = sucPeelFn
    ; encodeVar   = encVar
    ; encodeEq    = `:= R↓↓ `n
    ; finishSolve = finish
    }
    where
    `n = toTerm numAtoms

    opAdd : List Term → Term
    opAdd (x ∷ y ∷ _) = `:+ R↓↓ `n x y
    opAdd _           = unknown

    opMul : List Term → Term
    opMul (x ∷ y ∷ _) = `:* R↓↓ `n x y
    opMul _           = unknown

    opZero : List Term → Term
    opZero _ = `con R↓↓ `n (toTerm 0)

    opOne : List Term → Term
    opOne _ = `con R↓↓ `n (toTerm 1)

    encNat : ℕ → Term
    encNat n = `con R↓↓ `n (toTerm n)

    sucPeelFn : Term → Term
    sucPeelFn inner =
      `:+ R↓↓ `n (`con R↓↓ `n (toTerm 1)) inner

    encVar : ℕ → Term
    encVar i = `var R↓↓ `n (toFinTerm i)

    finish : Term → List Term → Term
    finish lambdaBody atoms =
      def (quote Solver.solve) (2 ⋯⟅∷⟆ R↓ ⟨∷⟩ `n ⟨∷⟩ lambdaBody ⟨∷⟩ `refl R↓ ⟨∷⟩ List.map vArg atoms)

------------------------------------------------------------------------
-- The macro.

private
  csrTheory : Theory
  csrTheory = record
    { bundleType = `CommutativeSemiring
    ; State      = RingState
    ; detect     = detectCSR
    ; encode     = λ R↓↓ R↓ n st → mkEncode R↓↓ R↓ n (RingState.litStyle st)
    }

solve-≈-macro : Term → Term → TC ⊤
solve-≈-macro R hole = do
  -- `commitTC` locks in `checkType`'s metavariable resolutions
  -- before further work that depends on `R`'s type being settled.
  -- `solveByTheory` deliberately doesn't redo the `checkType`.
  R' ← checkType R `CommutativeSemiring
  commitTC
  solveByTheory csrTheory R' hole

macro
  solve-≈ : Term → Term → TC ⊤
  solve-≈ = solve-≈-macro
