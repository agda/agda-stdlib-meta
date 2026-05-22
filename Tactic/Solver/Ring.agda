------------------------------------------------------------------------
-- A reflection-based ring solver.
--
-- `solve-≈` accepts either a `CommutativeSemiring` or a
-- `CommutativeRing` and dispatches to the appropriate backend:
--   * CSR → `Algebra.Solver.Ring.NaturalCoefficients.Default R`
--     (ℕ coefficients, no negation);
--   * CR  → `Tactic.Solver.Ring.IntegerCoefficients R` (ℤ
--     coefficients, real negation; recognises `_-_` and `-_`).
--
-- Built on `Tactic.Solver.Algebra`. For a new structure (monoid,
-- lattice, …), write a fresh `Theory` and macro alongside this one.

{-# OPTIONS --without-K --safe #-}

module Tactic.Solver.Ring where

open import Algebra using (CommutativeSemiring; CommutativeRing)

open import Data.Bool                  using (Bool; true; false)
open import Data.Fin                   using (Fin)
open import Data.Integer               using (ℤ; +_)
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
open import Reflection.Utils.TCM       using (headReduce; headReducePeel)

open import Tactic.Solver.Algebra
import Tactic.Solver.Ring.IntegerCoefficients as IntC

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
  data RingSide : Set where
    csr cr : RingSide

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

  crAdd  crMul  crSub  crNeg  crZero crOne  : Name
  crAdd  = quote CommutativeRing._+_
  crMul  = quote CommutativeRing._*_
  crSub  = quote CommutativeRing._-_
  crNeg  = quote (CommutativeRing.-_)
  crZero = quote CommutativeRing.0#
  crOne  = quote CommutativeRing.1#

  bundleTypeOf : RingSide → Term
  bundleTypeOf csr = def (quote CommutativeSemiring) (2 ⋯⟨∷⟩ [])
  bundleTypeOf cr  = def (quote CommutativeRing)     (2 ⋯⟨∷⟩ [])

------------------------------------------------------------------------
-- Polynomial-AST Term builders. Calling shape:
--   `def NAME (2 hidden + R-bundle ⟨∷⟩ numVars ⟅∷⟆ ⟨args…⟩)`,
-- pulling NAMEs from `Solver.*` for CSR and `IntC.*` for CR.

private
  defP : (R `n : Term) → Name → List (Arg Term) → Term
  defP R `n nm args =
    def nm (2 ⋯⟅∷⟆ R ⟨∷⟩ `n ⟅∷⟆ args)

  conName varName addName mulName eqName solveName reflName
    : RingSide → Name
  conName   csr = quote Solver.conP        ; conName   cr = quote IntC.conP
  varName   csr = quote Solver.varP        ; varName   cr = quote IntC.varP
  addName   csr = quote Solver._:+_        ; addName   cr = quote IntC._:+_
  mulName   csr = quote Solver._:*_        ; mulName   cr = quote IntC._:*_
  eqName    csr = quote Solver._:=_        ; eqName    cr = quote IntC._:=_
  solveName csr = quote Solver.solve       ; solveName cr = quote IntC.solve
  reflName  csr = quote CommutativeSemiring.refl
  reflName  cr  = quote CommutativeRing.refl

  `con : RingSide → (R `n : Term) → Term → Term
  `con s R `n c = defP R `n (conName s) (c ⟨∷⟩ [])

  `var : RingSide → (R `n : Term) → Term → Term
  `var s R `n i = defP R `n (varName s) (i ⟨∷⟩ [])

  `:+ : RingSide → (R `n : Term) → Term → Term → Term
  `:+ s R `n x y = defP R `n (addName s) (x ⟨∷⟩ y ⟨∷⟩ [])

  `:* : RingSide → (R `n : Term) → Term → Term → Term
  `:* s R `n x y = defP R `n (mulName s) (x ⟨∷⟩ y ⟨∷⟩ [])

  `:- : (R `n : Term) → Term → Term → Term
  `:- R `n x y = defP R `n (quote IntC._:-_) (x ⟨∷⟩ y ⟨∷⟩ [])

  `:-‿ : (R `n : Term) → Term → Term
  `:-‿ R `n x = defP R `n (quote IntC.negP) (x ⟨∷⟩ [])

  `:= : RingSide → (R `n : Term) → Term → Term → Term
  `:= s R `n x y = defP R `n (eqName s) (x ⟨∷⟩ y ⟨∷⟩ [])

  `refl : RingSide → (R : Term) → Term
  `refl s R = def (reflName s) (2 ⋯⟅∷⟆ R ⟨∷⟩ 1 ⋯⟅∷⟆ [])

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
  -- `derived` is additional syntax that isn't a field; `zeroLit` and
  -- `oneLit` mark literals.
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

  crSlots : List Slot
  crSlots = (crAdd  , 2 , op)
          ∷ (crMul  , 2 , op)
          ∷ (crSub  , 2 , derived)
          ∷ (crNeg  , 1 , op)
          ∷ (crZero , 0 , zeroLit)
          ∷ (crOne  , 0 , oneLit)
          ∷ []

  slotsFor : RingSide → List Slot
  slotsFor csr = csrSlots
  slotsFor cr  = crSlots

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

  detectFor : RingSide → Term → TC (TheoryDetect × RingState)
  detectFor side R = do
    R' ← headReduce 16 R
    let slots         = slotsFor side
    let concreteN     = length (filterᵇ slotIsConcrete slots)
    case R' of λ where
      (con _ args) → case Maybe.map Vec.toList (takeFirst concreteN (drop 2 (vArgs args))) of λ where
        (just rawOps) → do
          concOps ← traverse ⦃ Functor-List ⦄ (headReducePeel 16) rawOps
          slotted ← zipSlots slots concOps
          slottedLit ← traverse ⦃ Functor-List ⦄ (λ (s , t) → (s ,_) <$> headReduce 16 t) slotted
          let blockNs = collectDefNames concOps
          let ls = maybe (uncurry detectLitStyle) nothing (findZeroOne slottedLit)
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
  -- ℕ literal `n` rendered at the polynomial-coefficient type:
  -- ℕ for CSR (`toTerm n`), ℤ for CR (wrapped with `+_`).
  natLitTerm : RingSide → ℕ → Term
  natLitTerm csr n = toTerm n
  natLitTerm cr  n = con (quote +_) (toTerm n ⟨∷⟩ [])

  mkEncode : (s : RingSide) → (R↓↓ R↓ : Term)
           → (numAtoms : ℕ) → Maybe LitStyle → TheoryEncode
  mkEncode s R↓↓ R↓ numAtoms litStyle = record
    { opEncoders  = ops s
    ; encodeNat   = encNat
    ; sucPeel     = sucPeelFn
    ; encodeVar   = encVar
    ; encodeEq    = `:= s R↓↓ `n
    ; finishSolve = finish
    }
    where
    `n = toTerm numAtoms

    opAdd : List Term → Term
    opAdd (x ∷ y ∷ _) = `:+ s R↓↓ `n x y
    opAdd _           = unknown

    opMul : List Term → Term
    opMul (x ∷ y ∷ _) = `:* s R↓↓ `n x y
    opMul _           = unknown

    opSub : List Term → Term
    opSub (x ∷ y ∷ _) = `:- R↓↓ `n x y
    opSub _           = unknown

    opNeg : List Term → Term
    opNeg (x ∷ _) = `:-‿ R↓↓ `n x
    opNeg _       = unknown

    opZero : List Term → Term
    opZero _ = `con s R↓↓ `n (natLitTerm s 0)

    opOne : List Term → Term
    opOne _ = `con s R↓↓ `n (natLitTerm s 1)

    -- The order here MUST match what `detectCSR`/`detectCR` emit
    -- for `operatorMatches`.
    ops : RingSide → List (List Term → Term)
    ops csr = opAdd ∷ opMul ∷ opZero ∷ opOne ∷ []
    ops cr  = opAdd ∷ opMul ∷ opSub ∷ opNeg ∷ opZero ∷ opOne ∷ []

    encNat : ℕ → Term
    encNat n = `con s R↓↓ `n (natLitTerm s n)

    sucPeelFn : Term → Term
    sucPeelFn inner =
      `:+ s R↓↓ `n (`con s R↓↓ `n (natLitTerm s 1)) inner

    encVar : ℕ → Term
    encVar i = `var s R↓↓ `n (toFinTerm i)

    finish : Term → List Term → Term
    finish lambdaBody atoms =
      def (solveName s) (2 ⋯⟅∷⟆ R↓ ⟨∷⟩ `n ⟨∷⟩ lambdaBody ⟨∷⟩ `refl s R↓ ⟨∷⟩ List.map vArg atoms)

------------------------------------------------------------------------
-- The macro.

private
  ringTheory : RingSide → Theory
  ringTheory s = record
    { bundleType = bundleTypeOf s
    ; State      = RingState
    ; detect     = detectFor s
    ; encode     = λ R↓↓ R↓ n st → mkEncode s R↓↓ R↓ n (RingState.litStyle st)
    }

  detectSide : Term → TC (RingSide × Term)
  detectSide R =
    ((cr ,_) <$> checkType R (bundleTypeOf cr))
    <|> ((csr ,_) <$> checkType R (bundleTypeOf csr))
    <|> typeError
        ( strErr "solve-≈: the bundle argument must be a "
        ∷ strErr "`CommutativeSemiring` or a `CommutativeRing`, but "
        ∷ termErr R
        ∷ strErr " is neither."
        ∷ [])

solve-≈-macro : Term → Term → TC ⊤
solve-≈-macro R hole = do
  -- `commitTC` locks in `detectSide`'s metavariable resolutions
  -- before further work that depends on `R`'s type being settled.
  -- `solveByTheory` deliberately doesn't redo the `checkType`.
  side , R' ← detectSide R
  commitTC
  solveByTheory (ringTheory side) R' hole

macro
  solve-≈ : Term → Term → TC ⊤
  solve-≈ = solve-≈-macro
