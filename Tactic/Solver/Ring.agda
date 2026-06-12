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
-- Built on `Tactic.Solver.Algebra`, which owns the generic pipeline;
-- this module only says what a ring is:
--
--   * the *slot table* (`csrSlots`/`crSlots`): one entry per piece of
--     ring syntax, pairing the bundle field it is detected from with
--     the encoder producing its polynomial-AST Term;
--   * how literals look on the carrier (`detectLitStyle`,
--     `mkLiteralSpec`);
--   * how to assemble the final `solve n (λ xs → lhs := rhs) refl`
--     call (`finishSolve`).

{-# OPTIONS --without-K --safe #-}

module Tactic.Solver.Ring where

open import Algebra using (CommutativeSemiring; CommutativeRing)

open import Data.Bool                  using (Bool; true; false; if_then_else_)
open import Data.Integer               using (ℤ; +_; -[1+_])
open import Data.List as List          using (List; _∷_; [])
open import Data.Maybe as Maybe        using (Maybe; just; nothing; maybe)
open import Data.Nat                   using (ℕ; suc; zero)
open import Data.Nat.Reflection        using (toTerm)
open import Data.Product               using (_,_; _×_)
open import Data.Unit
open import Data.Vec as Vec            using (Vec)

open import Function

open import Class.Functor
open import Class.Monad.Instances

open import Reflection
open import Reflection.AST.Argument
import Reflection.AST.Name as Name
open import Reflection.AST.Term
open import Reflection.TCM.Syntax      hiding (_<$>_)
open import Reflection.Utils.Args      using (vArgs)
open import Reflection.Utils.Core      using (extractNat)
open import Reflection.Utils.Records
  using (fieldProjection; projectField)

open import Tactic.Solver.Algebra
import Tactic.Solver.Ring.IntegerCoefficients as IntC

module NatC {c ℓ} (R : CommutativeSemiring c ℓ) where
  open import Algebra.Solver.Ring.NaturalCoefficients.Default R public

  conP : ∀ {n} → ℕ → Polynomial n
  conP = con

------------------------------------------------------------------------
-- The two ring flavours and their backend names.

private
  data RingSide : Set where
    csr cr : RingSide

  bundleTypeOf : RingSide → Term
  bundleTypeOf csr = def (quote CommutativeSemiring) (2 ⋯⟨∷⟩ [])
  bundleTypeOf cr  = def (quote CommutativeRing)     (2 ⋯⟨∷⟩ [])

  conName addName mulName eqName solveName reflName zeroName oneName : RingSide → Name
  conName   csr = quote NatC.conP                ; conName   cr = quote IntC.conP
  addName   csr = quote NatC._:+_                ; addName   cr = quote IntC._:+_
  mulName   csr = quote NatC._:*_                ; mulName   cr = quote IntC._:*_
  eqName    csr = quote NatC._:=_                ; eqName    cr = quote IntC._:=_
  solveName csr = quote NatC.solve               ; solveName cr = quote IntC.solve
  zeroName  csr = quote CommutativeSemiring.0#   ; zeroName  cr = quote CommutativeRing.0#
  oneName   csr = quote CommutativeSemiring.1#   ; oneName   cr = quote CommutativeRing.1#
  reflName  csr = quote CommutativeSemiring.refl ; reflName  cr = quote CommutativeRing.refl

------------------------------------------------------------------------
-- Polynomial-AST encoders. Every backend name re-exported by
-- `NatC`/`IntC` has telescope `{c ℓ} (R) {n} → … Polynomial n …`,
-- where the hidden `n` is the expression type's variable-count
-- index — equal to the atom count. Each emitted node instantiates
-- `R` and `n` explicitly:
--   `def NAME (2 hidden ∷ R ⟨∷⟩ numAtoms ⟅∷⟆ ⟨args…⟩)`.

private
  defP : EncodeEnv → Name → List Term → Term
  defP env nm args =
    def nm (2 ⋯⟅∷⟆ EncodeEnv.R↓↓ env ⟨∷⟩ toTerm (EncodeEnv.numAtoms env) ⟅∷⟆ List.map vArg args)

  -- A `def`-headed backend operator, applied to the encoded operands.
  opEnc : ∀ {n} → Name → EncodeEnv → Vec Term n → Term
  opEnc nm env args = defP env nm (Vec.toList args)

  -- ℕ literal `n` rendered at the polynomial-coefficient type:
  -- ℕ for CSR (`toTerm n`), ℤ for CR (wrapped with `+_`).
  natLitTerm : RingSide → ℕ → Term
  natLitTerm csr n = toTerm n
  natLitTerm cr  n = con (quote +_) (toTerm n ⟨∷⟩ [])

  -- The polynomial constant `n`.
  constEnc : RingSide → ℕ → EncodeEnv → Term
  constEnc s n env = defP env (conName s) (natLitTerm s n ∷ [])

------------------------------------------------------------------------
-- The slot tables: all ring syntax, each piece pairing the bundle
-- field it is detected from with its encoder.

private
  csrSlots : List Slot
  csrSlots =
      mkSlot (quote CommutativeSemiring._+_) 2 op (opEnc (addName csr))
    ∷ mkSlot (quote CommutativeSemiring._*_) 2 op (opEnc (mulName csr))
    ∷ mkSlot (zeroName csr)                  0 op (λ env _ → constEnc csr 0 env)
    ∷ mkSlot (oneName  csr)                  0 op (λ env _ → constEnc csr 1 env)
    ∷ []

  crSlots : List Slot
  crSlots =
      mkSlot (quote CommutativeRing._+_)   2 op      (opEnc (addName cr))
    ∷ mkSlot (quote CommutativeRing._*_)   2 op      (opEnc (mulName cr))
    ∷ mkSlot (quote CommutativeRing._-_)   2 derived (opEnc (quote IntC._:-_))
    ∷ mkSlot (quote (CommutativeRing.-_))  1 op      (opEnc (quote IntC.negP))
    ∷ mkSlot (zeroName cr)                 0 op      (λ env _ → constEnc cr 0 env)
    ∷ mkSlot (oneName  cr)                 0 op      (λ env _ → constEnc cr 1 env)
    ∷ []

  slotsFor : RingSide → List Slot
  slotsFor csr = csrSlots
  slotsFor cr  = crSlots

------------------------------------------------------------------------
-- Literal-style recognition from the bundle's `0#` and `1#` Terms.

private
  data LitStyle : Set where
    natStyle : LitStyle           -- bare ℕ literals; peel `suc`.
    wrapped  : Name → LitStyle    -- `con C ⟨ n ⟩` (e.g. ℤ's `+_`).

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

  -- ℤ's `+_` wrapper is special: it is an additive homomorphism, so
  -- the parser may peel `suc`s under it, and (on the CR side, whose
  -- coefficients are ℤ) `-[1+_]` is its negative counterpart.
  mkLiteralSpec : RingSide → Maybe LitStyle → Maybe LiteralSpec
  mkLiteralSpec _ nothing = nothing
  mkLiteralSpec s (just style) = just (record
    { litCon         = litConOf style
    ; negLitCon      = negConOf s style
    ; peelSuc        = isNat style
    ; peelWrappedSuc = isPos style
    ; encodeNat      = λ env n → constEnc s n env
    ; encodeNegSuc   = λ env n → defP env (conName s) (con (quote -[1+_]) (toTerm n ⟨∷⟩ []) ∷ [])
    ; encodeSucPeel  = λ env t → defP env (addName s) (constEnc s 1 env ∷ t ∷ [])
    })
    where
    litConOf : LitStyle → Maybe Name
    litConOf natStyle    = nothing
    litConOf (wrapped C) = just C

    isNat : LitStyle → Bool
    isNat natStyle = true
    isNat _        = false

    isPos : LitStyle → Bool
    isPos (wrapped C) = C Name.≡ᵇ quote +_
    isPos _           = false

    negConOf : RingSide → LitStyle → Maybe Name
    negConOf cr (wrapped C) = if C Name.≡ᵇ quote +_ then just (quote -[1+_]) else nothing
    negConOf _  _           = nothing

------------------------------------------------------------------------
-- Detection: resolve the slot table against the bundle
-- (`resolveSlots`/`projectField` handle the bundle's possible shapes
-- — constructor, copattern-compiled record expression, abstract
-- value — uniformly).

private
  detectFor : RingSide → Term → TC DetectedTheory
  detectFor side R = do
    slotted ← resolveSlots numParams (slotsFor side) R
    ls ← litStyleOf slotted
    pure (record
      { operators    = operatorsOf slotted
      ; literalSpec  = mkLiteralSpec side ls
      ; blockedNames = blockedOf slotted
      ; encodeEq     = λ env x y → defP env (eqName side) (x ∷ y ∷ [])
      ; finishSolve  = finish
      })
    where
    numParams : ℕ
    numParams = 2

    -- Plain whnf before `detectLitStyle`: it only needs the head
    -- constructor, and a step-wise head reduction is pathologically
    -- slow on carriers like ℚ whose literals unfold into
    -- proof-carrying terms.
    litStyleOf : List (Slot × Term) → TC (Maybe LitStyle)
    litStyleOf slotted =
      case (lookupSlot (zeroName side) slotted , lookupSlot (oneName side) slotted) of λ where
        (just z , just o) → do
          z' ← reduce z
          o' ← reduce o
          pure (detectLitStyle z' o')
        _ → pure nothing

    finish : EncodeEnv → Term → List Term → Term
    finish env body atoms =
      def (solveName side)
        (2 ⋯⟅∷⟆ R↓ ⟨∷⟩ toTerm (EncodeEnv.numAtoms env) ⟨∷⟩ body ⟨∷⟩ `refl ⟨∷⟩ List.map vArg atoms)
      where
      R↓ = EncodeEnv.R↓ env
      `refl = def (reflName side) (2 ⋯⟅∷⟆ R↓ ⟨∷⟩ 1 ⋯⟅∷⟆ [])

------------------------------------------------------------------------
-- The macro.

private
  ringTheory : RingSide → Theory
  ringTheory s = record
    { macroName = "solve-≈"
    ; detect    = detectFor s
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
