------------------------------------------------------------------------
-- Theory descriptions for `Tactic.Solver.Core`: what a solver author
-- writes. A `Theory`'s main content is `detect`: given the user's
-- bundle Term, produce a `DetectedTheory`:
--
--   * `operators`: one entry per piece of applied syntax, pairing a
--     Term whose head identifies goal occurrences (usually
--     `projectField` of the bundle, see `Reflection.Utils.Records`)
--     with an occurrence parser and an encoder into the backend
--     solver's expression AST;
--   * `constants`: nullary syntax whose resolved value has no `def`
--     head (a literal like ℕ's `0`, a constructor like List's `[]`),
--     recognised by α-equality instead of by head name;
--   * `literalSpec`: how numerals look on the carrier, if the backend
--     supports literal coefficients;
--   * `blockedNames`: the operator/constant heads, to be kept opaque
--     while the goal is analysed;
--   * `sortOf`: how to compute an atom's sort key, for multi-sorted
--     theories (`nothing` = single-sorted: one atom group);
--   * `atomEmission`: how atoms reach the emitted call — a binder
--     reference, a store-indexed reference, or spliced in place;
--   * `encodeEq`/`finishSolve`: the equation node and the final
--     solver call.
--
-- Simple theories declare their syntax as a *slot table* (`mkSlot`:
-- bundle field name, arity, encoder) and let `resolveSlots` +
-- `operatorsOf`/`constantsOf`/`blockedOf` derive the above; see
-- `Tactic.Solver.Ring.Core` and `Tactic.Solver.Monoid`.

{-# OPTIONS --without-K --safe #-}

module Tactic.Solver.Core.Signature where

open import Data.Bool
open import Data.List as List
open import Data.Maybe as Maybe
open import Data.Nat
open import Data.Product
open import Data.String
open import Data.Vec as Vec

open import Function

open import Class.Functor
open import Class.Monad.Instances
open import Class.Traversable

open import Reflection
open import Reflection.AST.Argument
import Reflection.AST.Name as Name
open import Reflection.AST.Term
open import Reflection.TCM.Syntax      hiding (_<$>_)
open import Reflection.Utils.Args
open import Reflection.Utils.Core
open import Reflection.Utils.Records

open import Tactic.Solver.Core.Indexing

------------------------------------------------------------------------
-- I. Occurrences and operators.

-- A projected operator like `def CSR._+_ (R ⟨∷⟩ a ⟨∷⟩ b ⟨∷⟩ [])`
-- carries the bundle as a leading visible arg; this returns how many
-- such prefix args to skip before reaching the operator's last
-- `arity` visibles.
--
-- This assumes any extra visibles beyond `arity` are a *prefix*
-- (bundle arguments). That holds for the operators of a bundle over
-- a `Set` carrier. It fails for a *function* carrier (`A → B`, with
-- pointwise `_≈_`): there `_+_ f g x` over-applies the operator with
-- the point `x` as a trailing arg, which `opDrop` would mistake for
-- a bundle prefix and so misread the operands. Function-typed
-- carriers are therefore unsupported.
opDrop : ℕ → Args Term → ℕ
opDrop arity xs = visibleCount xs ∸ arity

-- What an operator's occurrence parser extracts from an application's
-- argument spine: the operand subterms (parsed recursively into
-- backend expressions) and, for indexed theories, index metadata
-- (e.g. a composite's endpoint objects, read off the hidden args)
-- that the encoder may splice but that is never parsed.
record Occurrence : Set where
  field
    operands : List Term
    indices  : List Term

record Operator : Set where
  field
    -- Pattern: goal subterms whose head Name matches `opTerm`'s
    -- (lambda-peeled) head are occurrences of this operator.
    opTerm   : Term
    -- Extract an occurrence from the argument spine; `nothing` makes
    -- the driver atomise the whole subterm.
    parseOcc : Args Term → Maybe Occurrence
    -- Build the backend expression for an occurrence: given the
    -- occurrence and Terms of the backend's expression type for the
    -- (recursively encoded) operands, produce one for the operator
    -- applied to them — e.g. the ring `_+_` maps operand encodings
    -- x, y to the Term `x :+ y`.
    encode   : EncodeEnv → Occurrence → List Term → Term

-- The first operator whose `opTerm` has head `nm`.
findOperator : List Operator → Name → Maybe Operator
findOperator []       _  = nothing
findOperator (o ∷ os) nm =
  if just nm ≡ᵐ headName (Operator.opTerm o)
    then just o
    else findOperator os nm

record Constant : Set where
  field
    -- Pattern: goal subterms α-equal to `constTerm` are occurrences
    -- of this constant. For nullary syntax with no `def` head — ℕ's
    -- `0`, List's `[]` — which `findOperator`'s head-name keying
    -- cannot see.
    constTerm : Term
    encode    : EncodeEnv → Term

------------------------------------------------------------------------
-- II. Slot tables: the simple, single-sorted way to declare syntax.

-- The default occurrence parser: skip the `opDrop` bundle prefix,
-- then take exactly `arity` visible operands (no index metadata).
defaultParseOcc : ℕ → Args Term → Maybe Occurrence
defaultParseOcc arity xs = Maybe.map mk (takeVis arity (opDrop arity xs) xs)
  where
  mk : List Term → Occurrence
  mk es = record { operands = es ; indices = [] }

  -- Skip `d` visible arguments, then take exactly `a`.
  takeVis : (a d : ℕ) → Args Term → Maybe (List Term)
  takeVis zero    _       _                                 = just []
  takeVis (suc a) (suc d) (arg (arg-info visible _) _ ∷ xs) = takeVis (suc a) d xs
  takeVis (suc a) 0       (arg (arg-info visible _) x ∷ xs) = Maybe.map (x ∷_) (takeVis a 0 xs)
  takeVis (suc a) d       (_ ∷ xs)                          = takeVis (suc a) d xs
  takeVis (suc a) _       []                                = nothing

-- A slot declares one piece of the structure's syntax: the bundle
-- field it is detected from, paired with its arity and encoder.
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

private
  slotEncode : Slot → EncodeEnv → List Term → Term
  slotEncode s env es =
    Maybe.maybe′ (Slot.encode s env) unknown (takeFirst (Slot.arity s) es)

-- Every resolved slot as an operator. Entries whose resolved Term has
-- no `def` head are dead here (`findOperator` is head-keyed) —
-- `constantsOf` picks the nullary ones up instead.
operatorsOf : List (Slot × Term) → List Operator
operatorsOf = List.map λ (s , t) → record
  { opTerm   = t
  ; parseOcc = defaultParseOcc (Slot.arity s)
  ; encode   = λ env _ es → slotEncode s env es
  }

-- The nullary slots with no `def` head: ℕ's `0`, List's `[]`, ….
constantsOf : List (Slot × Term) → List Constant
constantsOf =
    List.map (λ (s , t) → record { constTerm = t ; encode = λ env → slotEncode s env [] })
  ∘ filterᵇ (λ (s , t) → (Slot.arity s ≡ᵇ 0) ∧ not (is-just (headName t)))

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

------------------------------------------------------------------------
-- III. Literals (for theories with literal coefficients).

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

------------------------------------------------------------------------
-- IV. How an atom reaches the emitted call.
--
-- `binder` and `indexed` collect atoms in the store: occurrences are
-- deduplicated, the reference is minted from the atom's
-- (group , slot) position — stable, since groups appear in
-- first-discovery order and grow by appending — and the spellings
-- reach `finishSolve`. `embed` bypasses the store.

data AtomEmission : Set where
  -- a de Bruijn reference into the emitted call's `λ x₁ … xₙ` prefix
  -- (`Indexing.atomVar`)
  binder  : AtomEmission
  -- a theory-supplied reference — e.g. `gen i` with a `Fin` literal
  -- pointing into a signature vector
  indexed : (EncodeEnv → (group slot : ℕ) → Term) → AtomEmission
  -- the subterm spliced in place, for backends whose expression type
  -- is indexed by the carrier itself
  embed   : (EncodeEnv → Term → Term) → AtomEmission

------------------------------------------------------------------------
-- V. Everything `detect` learned about the user's bundle.

record DetectedTheory : Set where
  field
    operators    : List Operator
    constants    : List Constant
    literalSpec  : Maybe LiteralSpec
    -- Names that must stay opaque while the goal is inspected, fed
    -- to `withReduceDefs`. Must contain every operator's
    -- (lambda-peeled) head name.
    blockedNames : List Name
    -- Sort key of an atom, for multi-sorted theories; atoms whose
    -- keys are α-equal share a binder group. `nothing` = one group.
    sortOf       : Maybe (Term → TC Term)
    -- How an atom reaches the emitted call; see `AtomEmission`.
    atomEmission : AtomEmission
    encodeEq     : EncodeEnv → Term → Term → Term
    finishSolve  : EncodeEnv → (lambdaBody : Term) (atoms : List Term) → Term

record Theory : Set where
  field
    -- Used in error messages.
    macroName : String
    detect    : Term → TC DetectedTheory
