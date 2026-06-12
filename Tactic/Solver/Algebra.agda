------------------------------------------------------------------------
-- Generic core for reflection-based algebraic-structure solver
-- frontends: turns a description of a structure (a `Theory`) into a
-- working solver macro. `Tactic.Solver.Ring` is the model instance.
--
-- To add a solver for a new structure (monoid, lattice, …), write:
--
--   * a `Theory`, whose main content is `detect`: given the user's
--     bundle Term, produce a `DetectedTheory` —
--       · `operators`: one entry per piece of syntax, pairing a Term
--         whose head identifies goal occurrences (usually
--         `projectField` of the bundle, see
--         `Reflection.Utils.Records`) with its arity and its encoder
--         into the backend solver's expression AST;
--       · `literalSpec`: how numerals look on the carrier, if the
--         backend supports literal coefficients;
--       · `blockedNames`: the operator/constant heads, to be kept
--         opaque while the goal is analysed;
--       · `encodeEq`/`finishSolve`: the equation node and the final
--         solver call;
--
--   * a macro that type-checks its bundle argument against the
--     structure's bundle type and calls `solveByTheory`.
--
-- `solveByTheory` takes care of everything else:
--
--   * the goal type: walking under its pi-prefix (type aliases,
--     binder visibility), splitting the equation, and the
--     metavariable retry/error policy;
--   * inspecting the goal without ever normalising it: each step is
--     a weak-head reduction with `blockedNames` opaque, so reduction
--     stops exactly when recognised syntax surfaces;
--   * atoms: unrecognised subterms become solver variables, kept
--     exactly as the user wrote them (a literal like `1ℚ` is never
--     unfolded into the emitted call) and deduplicated up to whnf;
--   * encoding both sides and unifying the hole with the assembled
--     solver call.

{-# OPTIONS --without-K --safe #-}

module Tactic.Solver.Algebra where

open import Agda.Builtin.Reflection using (withReduceDefs)

open import Data.Bool
open import Data.List as List          using (List; _∷_; []; replicate; filterᵇ)
open import Data.Maybe as Maybe        using (Maybe; just; nothing; _<∣>_)
open import Data.Nat
open import Data.Product
open import Data.String                using (String)
open import Data.Unit
open import Data.Vec as Vec            using (Vec)

open import Function

open import Class.Functor
open import Class.Monad.Instances
open import Class.Traversable

open import Reflection
open import Reflection.AST.AlphaEquality using (_=α=_)
open import Reflection.AST.Argument
open import Reflection.AST.DeBruijn
import Reflection.AST.Name as Name
open import Reflection.AST.Term
open import Reflection.TCM.Syntax      hiding (_<$>_)
open import Reflection.Utils.Args
open import Reflection.Utils.Core
open import Reflection.Utils.Records   using (fieldProjection; projectField)
open import Reflection.Utils.AtomStore using (Atom; AtomStore; insertAtomStore; atomStoreIndex; atomSpellings)
open import Reflection.Utils.Goal      using (underPis; requireEquationSides; blockOnEquationMetas)

------------------------------------------------------------------------
-- I. Classification helpers.

-- A projected operator like `def CSR._+_ (R ⟨∷⟩ a ⟨∷⟩ b ⟨∷⟩ [])`
-- carries the bundle as a leading visible arg; this returns how many
-- such prefix args to skip before reaching the operator's last
-- `arity` visibles.
opDrop : ℕ → Args Term → ℕ
opDrop arity xs = visibleCount xs ∸ arity

------------------------------------------------------------------------
-- II. Theory specification.
--
-- The proof term the driver emits has the shape
--
--   λ p₁ … pₖ → solve R n (λ x₁ … xₙ → lhs′ := rhs′) refl a₁ … aₙ
--
-- with k binders for the goal's pi-prefix, n the number of atoms,
-- the aᵢ the atoms themselves, and lhs′/rhs′ the goal's two sides
-- re-encoded as backend expressions over the variables xᵢ, joined by
-- the backend's equation former (`_:=_` for the ring backends).
-- Atom i appears in the body as a reference to binder xᵢ₊₁ (the
-- backend's `solve` applies this n-ary function to the variable
-- expressions `var 0F … var (n−1)F`, in atom-store order — matching
-- the trailing aᵢ). The
-- encoders below build the pieces of this term, and `EncodeEnv`
-- carries the two things they
-- need but that are only known once both sides of the goal have been
-- parsed: the atom count n, and the bundle Term at the right de
-- Bruijn depth for the splice position. (Encoders take the env as an
-- argument — rather than being constructed after parsing — so that
-- `detect` can return each operator's detection pattern and encoder
-- as one value, with no ordering invariant between separate lists.)
--
-- The explicit `R`/`n` splices possible via passing `EncodeEnv` into
-- the `encode` functions earn their keep: inferring them is
-- semantically fine but measured ~11× slower on the test suite.

record EncodeEnv : Set where
  field
    -- The bundle, weakened past the k pi-binders, for splicing at the
    -- solver call.
    R↓       : Term
    numAtoms : ℕ     -- n

  -- The bundle for splicing inside the `λ x₁ … xₙ → …` body.
  R↓↓ : Term
  R↓↓ = weaken numAtoms R↓

record Operator : Set where
  field
    -- Pattern: goal subterms whose head Name matches `opTerm`'s
    -- (lambda-peeled) head are occurrences of this operator.
    opTerm : Term
    arity  : ℕ
    -- Builds the backend expression for an occurrence of this
    -- operator: given Terms of the backend's expression type for the
    -- operands, produce one for the operator applied to them — e.g.
    -- the ring `_+_` maps operand encodings x, y to the Term `x :+ y`.
    encode : EncodeEnv → Vec Term arity → Term

-- The first operator whose `opTerm` has head `nm`.
findOperator : List Operator → Name → Maybe Operator
findOperator []       _  = nothing
findOperator (o ∷ os) nm =
  if just nm ≡ᵐ headName (Operator.opTerm o)
    then just o
    else findOperator os nm

-- A slot declares one piece of the structure's syntax: the bundle
-- field it is detected from, paired with its `Operator` content.
-- `derived` marks syntax that is not a field (e.g. a ring's `_-_`):
-- it is resolved by *normalising* its projection, so occurrences
-- match via their unfolding.
data SlotKind : Set where
  op derived : SlotKind

record Slot : Set where
  field
    fieldName : Name
    arity     : ℕ
    kind      : SlotKind
    encode    : EncodeEnv → Vec Term arity → Term

mkSlot : (nm : Name) (a : ℕ) → SlotKind → (EncodeEnv → Vec Term a → Term) → Slot
mkSlot nm a k e = record { fieldName = nm ; arity = a ; kind = k ; encode = e }

slotIsConcrete : Slot → Bool
slotIsConcrete s = case Slot.kind s of λ where
  derived → false
  op      → true

-- Resolve each slot against the bundle (`k` = the bundle type's
-- parameter count): concrete fields by name-preserving projection,
-- derived syntax by normalisation.
resolveSlots : ℕ → List Slot → Term → TC (List (Slot × Term))
resolveSlots k slots R = traverse (λ s → (s ,_) <$> slotTerm s) slots
  where
  slotTerm : Slot → TC Term
  slotTerm s = case Slot.kind s of λ where
    derived → normalise (fieldProjection k R (Slot.fieldName s))
    op      → projectField k R (Slot.fieldName s)

operatorsOf : List (Slot × Term) → List Operator
operatorsOf = List.map λ (s , t) →
  record { opTerm = t ; arity = Slot.arity s ; encode = Slot.encode s }

-- The concrete slots' head names: see `DetectedTheory.blockedNames`.
blockedOf : List (Slot × Term) → List Name
blockedOf = List.foldr pickDefName []
          ∘ List.map proj₂
          ∘ filterᵇ (slotIsConcrete ∘ proj₁)

-- The resolved Term of the slot declared from the given field.
lookupSlot : Name → List (Slot × Term) → Maybe Term
lookupSlot nm []               = nothing
lookupSlot nm ((s , t) ∷ rest) =
  if nm Name.≡ᵇ Slot.fieldName s then just t else lookupSlot nm rest

-- For theories with literal coefficients (the ring solvers).
record LiteralSpec : Set where
  field
    -- Wrapper constructor for numerals (ℤ's `+_`); `nothing` for
    -- carriers whose numerals are bare ℕ literals.
    litCon         : Maybe Name
    -- Constructor for negative numerals (ℤ's `-[1+_]`), for theories
    -- whose coefficients support negation; its payload `n` denotes
    -- the value `-(1+n)`.
    negLitCon      : Maybe Name
    -- Peel bare `suc`s (ℕ-style carriers): `suc t ≈ 1# + t`.
    peelSuc        : Bool
    -- Peel `suc`s under the wrapper: sound iff the wrapper is an
    -- additive homomorphism, `C (suc n) ≈ 1# + C n` (true for `+_`).
    peelWrappedSuc : Bool
    -- Encoders for the above. `encodeSucPeel` maps an encoded `t` to
    -- the encoding of `1# + t`.
    encodeNat      : EncodeEnv → ℕ → Term
    encodeNegSuc   : EncodeEnv → ℕ → Term
    encodeSucPeel  : EncodeEnv → Term → Term

-- Everything `detect` learned about the user's bundle.
record DetectedTheory : Set where
  field
    operators    : List Operator
    literalSpec  : Maybe LiteralSpec
    -- Names that must stay opaque while the goal is inspected, fed
    -- to `withReduceDefs`. Must contain every operator's
    -- (lambda-peeled) head name.
    blockedNames : List Name
    encodeEq     : EncodeEnv → Term → Term → Term
    finishSolve  : EncodeEnv → (lambdaBody : Term) (atoms : List Term) → Term

record Theory : Set where
  field
    -- Used in error messages.
    macroName : String
    detect    : Term → TC DetectedTheory

------------------------------------------------------------------------
-- III. Numeral recognition.

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
    inner' ← reduce inner
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
-- V. Parsing a goal side into its deferred backend encoding.

-- An `Encoding` is a backend expression awaiting the `EncodeEnv`
-- (only known once both sides are parsed). Parsing composes the
-- encodings directly — there is no intermediate syntax tree.
Encoding : Set
Encoding = EncodeEnv → Term

-- Parse a goal side, threading the atom store through.
--
-- Each node is brought to weak-head normal form first — the caller
-- wraps this in `withReduceDefs` blocking the theory's names, so whnf
-- stops exactly when an operator or numeral surfaces, while aliases,
-- β-redexes and other definitions unfold. A subterm that exposes
-- neither is atomised with its original spelling (section IV).
parseGoalTerm : DetectedTheory → Term → AtomStore → TC (Encoding × AtomStore)
parseGoalTerm det = parse 1024
  where
  open DetectedTheory det

  -- The numeral encodings are only formed when `numeralView` ran
  -- under `just` a literal spec, so the `unknown` fallback is
  -- unreachable.
  litEnc : (LiteralSpec → EncodeEnv → Term) → Encoding
  litEnc f = Maybe.maybe′ f (λ _ → unknown) literalSpec

  -- The bottom of the recogniser cascade: every subterm in which
  -- `parse` finds no theory syntax ends up here. `orig` is the
  -- subterm exactly as the user wrote it — the only form that may
  -- appear in the emitted call; `whnf` is whatever reduced form the
  -- caller already has, used only as the store's second identity key
  -- (never emitted). Returns the encoding referencing the atom's
  -- solver binder.
  atomise : (orig whnf : Term) → AtomStore → TC (Encoding × AtomStore)
  atomise orig whnf acc = do
    let acc' = insertAtomStore (orig , whnf) acc
    -- see `Reflection.Utils.AtomStore` for why we do this
    just i ← pure (atomStoreIndex (orig , whnf) acc')
      where nothing → typeError
                    ( strErr "Internal error in Tactic.Solver.Algebra: atom "
                    ∷ termErr orig
                    ∷ strErr " not found after insertion."
                    ∷ [])
    -- Atom i refers to the i-th of the n binders wrapped around the
    -- body by the driver; the outermost binder is atom 0.
    pure ((λ env → var (EncodeEnv.numAtoms env ∸ suc i) []) , acc')

  -- The ℕ argument is recursion-depth fuel (the per-node `reduce`
  -- makes the recursion non-structural); it bounds the *depth* of the
  -- recognised expression structure, so running out — at which point
  -- the subterm is atomised whole — is purely theoretical.
  mutual
    parse : ℕ → Term → AtomStore → TC (Encoding × AtomStore)
    parse zero    t acc = atomise t t acc
    parse (suc k) t acc = do
      t' ← reduce t
      nv ← numeralView literalSpec t'
      case nv of λ where
        (natLit n)        → pure (litEnc (λ ls env → LiteralSpec.encodeNat ls env n) , acc)
        (negsucLit n)     → pure (litEnc (λ ls env → LiteralSpec.encodeNegSuc ls env n) , acc)
        (sucOf tail)      →
          (λ (e , acc') → litEnc (λ ls env → LiteralSpec.encodeSucPeel ls env (e env)) , acc')
            <$> parse k tail acc
        (wrappedOpaque w) → atomise t w acc
        notNumeral        → parseHead k t t' acc

    parseHead : ℕ → (orig whnf : Term) → AtomStore → TC (Encoding × AtomStore)
    parseHead k orig t'@(def nm xs) acc = case findOperator operators nm of λ where
      nothing → atomise orig t' acc
      (just o) → let open Operator o in do
        (just (es , acc')) ← parseVisibleArgs k arity (opDrop arity xs) xs acc
          -- Fewer than `arity` operands in the spine (possible when
          -- the carrier is a function type): atomise the whole term.
          where nothing → atomise orig t' acc
        pure ((λ env → encode env (Vec.map (λ e → e env) es)) , acc')

    parseHead k orig t' acc = atomise orig t' acc

    -- Skip `d` visible arguments, then parse exactly `n`.
    parseVisibleArgs : ℕ → (n d : ℕ) → Args Term → AtomStore
                     → TC (Maybe (Vec Encoding n × AtomStore))
    parseVisibleArgs k zero    _       _                                 acc =
      pure (just (Vec.[] , acc))
    parseVisibleArgs k (suc n) (suc d) (arg (arg-info visible _) _ ∷ xs) acc =
      parseVisibleArgs k (suc n) d xs acc
    parseVisibleArgs k (suc n) 0       (arg (arg-info visible _) x ∷ xs) acc = do
      e , acc' ← parse k x acc
      m ← parseVisibleArgs k n 0 xs acc'
      pure (Maybe.map (λ (es , acc'') → (e Vec.∷ es) , acc'') m)
    parseVisibleArgs k (suc n) d       (_ ∷ xs)                          acc =
      parseVisibleArgs k (suc n) d xs acc
    parseVisibleArgs k (suc n) _       []                                acc =
      pure nothing

------------------------------------------------------------------------
-- VI. The generic macro core.

private
  -- Build the solver call for the equation, `numPiVars` binders below
  -- the hole's context.
  solveEquation : String → DetectedTheory → Term → ℕ → Term → TC Term
  solveEquation macroName det `R numPiVars equation = do
    lhs , rhs ← requireEquationSides equation
    blockOnEquationMetas macroName equation lhs rhs

    lhsEnc , store₀ ← parseGoalTerm det lhs []
    rhsEnc , store  ← parseGoalTerm det rhs store₀
    let atoms    = atomSpellings store
    let numAtoms = List.length atoms

    let env = record { R↓ = weaken numPiVars `R ; numAtoms = numAtoms }
    let open DetectedTheory det
    let lambdaBody = encodeEq env (lhsEnc env) (rhsEnc env)
    let f          = prependVLams (replicate numAtoms "x") lambdaBody
    pure (finishSolve env f atoms)

-- Precondition: `R` has been type-checked against the structure's
-- bundle type by the caller (e.g. via `Tactic.Solver.Ring.detectSide`).
solveByTheory : Theory → Term → Term → TC ⊤
solveByTheory thy `R hole = do
  let open Theory thy
  det ← detect `R
  holeTy ← inferType hole
  -- Only the goal *analysis* runs with the theory's names blocked
  final ← withReduceDefs (false , DetectedTheory.blockedNames det)
            (underPis 1024 holeTy (solveEquation macroName det `R))
  unify hole final
