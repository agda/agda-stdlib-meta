------------------------------------------------------------------------
-- Reflective solvers for the monoid family.
--
-- `solve-∙-macro` accepts a `Monoid`, a `CommutativeMonoid` or an
-- `IdempotentCommutativeMonoid` and dispatches to the corresponding
-- stdlib backend (`Algebra.Solver.Monoid` and friends); the most
-- specific structure is tried first, since its normal forms equate
-- the most goals.

{-# OPTIONS --without-K --safe #-}

module Tactic.Solver.Monoid where

open import Algebra

open import Data.List as List
open import Data.Maybe using (nothing)
open import Data.Nat
open import Data.Nat.Reflection
open import Data.Product
open import Data.Unit
open import Data.Vec as Vec

open import Class.Functor
open import Class.Monad.Instances

open import Reflection
open import Reflection.AST.Argument
open import Reflection.AST.Term
open import Reflection.TCM.Syntax hiding (_<$>_)

open import Tactic.Solver.Core
open import Tactic.Solver.Core.StdlibBackend

------------------------------------------------------------------------
-- Backend wrappers. Re-exporting the stdlib solver through a
-- parameterized module gives every backend name the uniform telescope
-- `{c ℓ} (M) {n} → …`, so the encoders below can splice `M` and the
-- atom count explicitly.

module MonS {c ℓ} (M : Monoid c ℓ) where
  open import Algebra.Solver.Monoid M public

  εP : ∀ {n} → Expr n
  εP = id

  _∙P_ : ∀ {n} → Expr n → Expr n → Expr n
  _∙P_ = _⊕_

module CMonS {c ℓ} (M : CommutativeMonoid c ℓ) where
  open import Algebra.Solver.CommutativeMonoid M public

  εP : ∀ {n} → Expr n
  εP = id

  _∙P_ : ∀ {n} → Expr n → Expr n → Expr n
  _∙P_ = _⊕_

module ICMonS {c ℓ} (M : IdempotentCommutativeMonoid c ℓ) where
  open import Algebra.Solver.IdempotentCommutativeMonoid M public

  εP : ∀ {n} → Expr n
  εP = id

  _∙P_ : ∀ {n} → Expr n → Expr n → Expr n
  _∙P_ = _⊕_

------------------------------------------------------------------------
-- The three monoid flavours and their backend names.

private
  data MonoidSide : Set where
    mon cmon icmon : MonoidSide

  bundleTypeOf : MonoidSide → Term
  bundleTypeOf mon   = def (quote Monoid)                       (2 ⋯⟨∷⟩ [])
  bundleTypeOf cmon  = def (quote CommutativeMonoid)            (2 ⋯⟨∷⟩ [])
  bundleTypeOf icmon = def (quote IdempotentCommutativeMonoid)  (2 ⋯⟨∷⟩ [])

  ∙FieldName εFieldName : MonoidSide → Name
  ∙FieldName mon   = quote Monoid._∙_
  ∙FieldName cmon  = quote CommutativeMonoid._∙_
  ∙FieldName icmon = quote IdempotentCommutativeMonoid._∙_
  εFieldName mon   = quote Monoid.ε
  εFieldName cmon  = quote CommutativeMonoid.ε
  εFieldName icmon = quote IdempotentCommutativeMonoid.ε

  ∙Name εName eqName solveName reflName : MonoidSide → Name
  ∙Name     mon   = quote MonS._∙P_
  ∙Name     cmon  = quote CMonS._∙P_
  ∙Name     icmon = quote ICMonS._∙P_
  εName     mon   = quote MonS.εP
  εName     cmon  = quote CMonS.εP
  εName     icmon = quote ICMonS.εP
  eqName    mon   = quote MonS._⊜_
  eqName    cmon  = quote CMonS._⊜_
  eqName    icmon = quote ICMonS._⊜_
  solveName mon   = quote MonS.solve
  solveName cmon  = quote CMonS.solve
  solveName icmon = quote ICMonS.solve
  reflName  mon   = quote Monoid.refl
  reflName  cmon  = quote CommutativeMonoid.refl
  reflName  icmon = quote IdempotentCommutativeMonoid.refl

------------------------------------------------------------------------
-- The slot tables: monoid syntax is just `_∙_` and `ε`.

private
  slotsFor : MonoidSide → List Slot
  slotsFor side =
      mkSlot (∙FieldName side) 2 op (opEnc (∙Name side))
    ∷ mkSlot (εFieldName side) 0 op (λ env _ → defP env (εName side) [])
    ∷ []

------------------------------------------------------------------------
-- Detection and the final `solve M n (λ xs → lhs ⊜ rhs) refl` call.

private
  detectFor : MonoidSide → Term → TC DetectedTheory
  detectFor side M = do
    slotted ← resolveSlots numParams (slotsFor side) M
    pure (record
      { operators    = operatorsOf slotted
      ; constants    = constantsOf slotted
      ; literalSpec  = nothing
      ; blockedNames = blockedOf slotted
      ; sortOf       = nothing
      ; embedAtom    = nothing
      ; encodeEq     = λ env x y → defP env (eqName side) (x ∷ y ∷ [])
      ; finishSolve  = finishViaSolve (solveName side) (reflName side)
      })
    where
    numParams : ℕ
    numParams = 2

------------------------------------------------------------------------
-- The macro.

private
  monoidTheory : MonoidSide → Theory
  monoidTheory s = record
    { macroName = "solve-∙"
    ; detect    = detectFor s
    }

  detectSide : Term → TC (MonoidSide × Term)
  detectSide M =
    ((icmon ,_) <$> checkType M (bundleTypeOf icmon))
    <|> ((cmon ,_) <$> checkType M (bundleTypeOf cmon))
    <|> ((mon ,_) <$> checkType M (bundleTypeOf mon))
    <|> typeError
        ( strErr "solve-∙: the bundle argument must be a `Monoid`, a "
        ∷ strErr "`CommutativeMonoid` or an `IdempotentCommutativeMonoid`, but "
        ∷ termErr M
        ∷ strErr " is none of these."
        ∷ [])

solve-∙-macro : Term → Term → TC ⊤
solve-∙-macro M hole = do
  -- `commitTC` locks in `detectSide`'s metavariable resolutions, as
  -- in the ring solver.
  side , M' ← detectSide M
  commitTC
  solveByTheory (monoidTheory side) M' hole

macro
  solve-∙ : Term → Term → TC ⊤
  solve-∙ = solve-∙-macro
