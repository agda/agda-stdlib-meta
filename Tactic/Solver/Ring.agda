------------------------------------------------------------------------
-- An improved ring solver, based on the stdlib's one
--
-- Automatically handles variable introduction as required, properly
-- deals with most literals, has sensible defaults and a few other
-- bells and whistles. Also has an extensive test suite.

{-# OPTIONS --without-K --safe #-}

module Tactic.Solver.Ring where

open import Algebra using (CommutativeSemiring)
open import Data.Fin.Base   as Fin     using (Fin; toℕ)
open import Data.Vec.Base   as Vec     using (Vec; _∷_; [])
open import Data.List.Base  as List    using (List; _∷_; []; _++_; replicate; foldr; findIndexᵇ; null)
open import Data.Bool.ListAction        using (any)
open import Data.Maybe.Base as Maybe   using (Maybe; just; nothing)
open import Data.Nat.Base              using (ℕ; suc; zero; _+_)
open import Data.Bool.Base             using (Bool; if_then_else_; true; false; _∨_; _∧_; not)
open import Data.Unit.Base             using (⊤; tt)
open import Data.Product.Base          using (_,_; _×_; proj₁)
open import Function.Base

open import Reflection
open import Reflection.AST.Argument
open import Reflection.AST.Term
open import Reflection.AST.AlphaEquality
open import Reflection.AST.DeBruijn using (weaken)
import Reflection.AST.Name as Name
import Reflection.AST.Meta as Meta
open import Reflection.TCM.Syntax
import Agda.Builtin.Reflection as B
  using (withReduceDefs)
open import Data.Nat.Reflection
import Data.Vec.Reflection as Vec

------------------------------------------------------------------------
-- I. Generic reflection utilities.
--
-- Everything in this section is independent of `CommutativeSemiring`
-- (and the polynomial layer): plain helpers for inspecting and
-- manipulating reflected `Term`s, deduplicating name/atom lists,
-- chasing metavariables, and reducing `def`-chains further than
-- Agda's primitive `reduce` does.
------------------------------------------------------------------------

private
  ----------------------------------------------------------------------
  -- Arg/Term inspection
  ----------------------------------------------------------------------

  getVisible : Arg Term → Maybe Term
  getVisible (arg (arg-info visible _) x) = just x
  getVisible _                            = nothing

  -- Extract the head `Name` of a term, peeling off any leading λ-binders.
  headName : Term → Maybe Name
  headName (def nm _)            = just nm
  headName (lam _ (abs _ body))  = headName body
  headName _                     = nothing

  _≡ᵐ_ : Maybe Name → Maybe Name → Bool
  just n  ≡ᵐ just m  = n Name.≡ᵇ m
  nothing ≡ᵐ nothing = true
  _       ≡ᵐ _       = false

  -- Try to extract a ℕ value from an iterated `suc`/`zero`
  -- constructor chain (or a built-in `lit (nat n)` literal).
  -- Returns `nothing` if the term is not a ℕ literal.
  extractNat : Term → Maybe ℕ
  extractNatArgs : Args Term → Maybe ℕ

  extractNat (lit (nat n)) = just n
  extractNat (con nm xs) =
    if nm Name.≡ᵇ quote zero then just 0
    else if nm Name.≡ᵇ quote suc then extractNatArgs xs
    else nothing
  extractNat _ = nothing

  extractNatArgs (arg (arg-info visible _) x ∷ []) = Maybe.map suc (extractNat x)
  extractNatArgs (_ ∷ xs) = extractNatArgs xs
  extractNatArgs []       = nothing

  -- Try `extractNat` first; if that fails and we have a wrapping
  -- constructor name (e.g. ℤ's `+_ : ℕ → ℤ`), peel one layer of
  -- `con C (arg ∷ [])` and try again.  Used to recognise `(+ n)`
  -- on ℤ as a polynomial constant.
  peelLitCon : Name → Term → Maybe ℕ
  peelLitCon C (con nm xs) with nm Name.≡ᵇ C
  ... | false = nothing
  ... | true  = case List.mapMaybe getVisible xs of λ where
    (a ∷ []) → extractNat a
    _        → nothing
  peelLitCon _ _ = nothing

  extractCarrierNat : Maybe Name → Term → Maybe ℕ
  extractCarrierNat mC t = case extractNat t of λ where
    (just n) → just n
    nothing  → case mC of λ where
      (just C) → peelLitCon C t
      nothing  → nothing

  getVisibleArgs : ∀ n → Term → Maybe (Vec Term n)
  getVisibleArgs n (def _ xs) = Maybe.map Vec.reverse
    (List.foldl f c (List.mapMaybe getVisible xs) n)
    where
    f : (∀ n → Maybe (Vec Term n)) → Term → ∀ n → Maybe (Vec Term n)
    f xs x zero    = just []
    f xs x (suc n) = Maybe.map (x ∷_) (xs n)

    c : ∀ n → Maybe (Vec Term n)
    c zero     = just []
    c (suc _ ) = nothing
  getVisibleArgs _ _ = nothing

  ----------------------------------------------------------------------
  -- List dedup/lookup
  ----------------------------------------------------------------------

  insertName : Name → List Name → List Name
  insertName n []       = n ∷ []
  insertName n (m ∷ ms) = if n Name.≡ᵇ m then m ∷ ms else m ∷ insertName n ms

  -- Insert `t` into `xs` if not already present (α-equality).
  insertAtom : Term → List Term → List Term
  insertAtom t [] = t ∷ []
  insertAtom t (a ∷ as) =
    if t =α= a then a ∷ as else a ∷ insertAtom t as

  findAtomIndex : Term → List Term → Maybe ℕ
  findAtomIndex t xs = Maybe.map Fin.toℕ (findIndexᵇ (t =α=_) xs)

  ----------------------------------------------------------------------
  -- Definition inspection
  ----------------------------------------------------------------------

  noArgBody : Definition → Maybe Term
  noArgBody (function (clause [] [] body ∷ _)) = just body
  noArgBody _                                  = nothing

  -- Pick the def-Name out of a Term, potentially under η-expansion.
  pickDefName : Term → List Name → List Name
  pickDefName (def n _)            xs = insertName n xs
  pickDefName (lam _ (abs _ body)) xs = pickDefName body xs
  pickDefName _                    xs = xs

mutual
  headReduce : ℕ → Term → TC Term
  headReduce 0       t = pure t
  headReduce (suc k) (def nm [])   = do
    d ← getDefinition nm
    case noArgBody d of λ where
      (just body) → headReduce k body
      nothing     → pure (def nm [])
  headReduce (suc k) (def nm args) = do
    args' ← reduceArgs k args
    t' ← B.withReduceDefs (true , nm ∷ []) (reduce (def nm args'))
    if t' =α= def nm args'
      then pure t' -- no progress
      else headReduce k t'
  headReduce (suc _) t = pure t

  reduceArgs : ℕ → Args Term → TC (Args Term)
  reduceArgs _ []             = pure []
  reduceArgs k (arg i t ∷ as) = do
    t'  ← headReduce k t
    as' ← reduceArgs k as
    pure (arg i t' ∷ as')

----------------------------------------------------------------------
-- Metavariable inspection (depth-first walk).
----------------------------------------------------------------------

mutual
  collectMetasT : Term → List Meta → List Meta
  collectMetasT (var _ xs)              acc = collectMetasArgs xs acc
  collectMetasT (con _ xs)              acc = collectMetasArgs xs acc
  collectMetasT (def _ xs)              acc = collectMetasArgs xs acc
  collectMetasT (lam _ (abs _ t))       acc = collectMetasT t acc
  collectMetasT (pat-lam _ _)           acc = acc
  collectMetasT (pi (arg _ a) (abs _ b)) acc = collectMetasT b (collectMetasT a acc)
  collectMetasT (agda-sort s)           acc = collectMetasSort s acc
  collectMetasT (lit _)                 acc = acc
  collectMetasT (meta x _)              acc = x ∷ acc
  collectMetasT unknown                 acc = acc

  collectMetasArgs : Args Term → List Meta → List Meta
  collectMetasArgs []             acc = acc
  collectMetasArgs (arg _ x ∷ xs) acc = collectMetasArgs xs (collectMetasT x acc)

  collectMetasSort : Sort → List Meta → List Meta
  collectMetasSort (set t)     acc = collectMetasT t acc
  collectMetasSort (lit _)     acc = acc
  collectMetasSort (prop t)    acc = collectMetasT t acc
  collectMetasSort (propLit _) acc = acc
  collectMetasSort (inf _)     acc = acc
  collectMetasSort unknown     acc = acc

metasOf : Term → List Meta
metasOf t = collectMetasT t []

firstMeta : Term → Maybe Meta
firstMeta t = case metasOf t of λ where
  []      → nothing
  (m ∷ _) → just m

-- Do two meta-lists share an element?  Used to distinguish
-- "deadlock" goals (no shared meta — blocking won't propagate
-- between the equation's sides) from goals where `blockOnMeta`
-- can be expected to succeed.
shareMeta : List Meta → List Meta → Bool
shareMeta xs ys = any (λ x → any (Meta._≡ᵇ_ x) ys) xs

bareMeta : Term → Bool
bareMeta (meta _ _) = true
bareMeta _          = false

----------------------------------------------------------------------
-- Append a list of Terms as visible args to an existing `def`.
----------------------------------------------------------------------

applyVisibleArgs : Term → List Term → Term
applyVisibleArgs (def nm xs) atoms = def nm (xs ++ foldr _⟨∷⟩_ [] atoms)
applyVisibleArgs t           _     = t   -- shouldn't happen for our use

------------------------------------------------------------------------
-- II. CommutativeSemiring-specific machinery.
------------------------------------------------------------------------

module Solver {c ℓ} (R : CommutativeSemiring c ℓ) where
  open import Algebra.Solver.Ring.NaturalCoefficients.Default R public

  -- Constructor wrappers (using `con` directly via `quote` is
  -- ambiguous because of name collisions across the imported chain).
  conP : ∀ {n} → ℕ → Polynomial n
  conP = con

  varP : ∀ {n} → Fin n → Polynomial n
  varP = var

`CommutativeSemiring : Term
`CommutativeSemiring = def (quote CommutativeSemiring) (2 ⋯⟨∷⟩ [])

record RingOperatorTerms : Set where
  constructor add⇒_mul⇒_zero⇒_one⇒_
  field
    add mul zero# one# : Term

-- Try to detect a "carrier-nat constructor": a single-argument
-- constructor `C : ℕ → Carrier` that wraps ℕ literals (e.g. ℤ's
-- `+_`).  We find it by checking that `zero#` and `one#` both have
-- shape `con C (n ∷ [])` with extracted ℕ values `0` and `1`.
litConstructor : RingOperatorTerms → Maybe Name
litConstructor (add⇒ _ mul⇒ _ zero⇒ con cz argsZ one⇒ con co argsO) =
  check (cz Name.≡ᵇ co) (List.mapMaybe getVisible argsZ) (List.mapMaybe getVisible argsO)
  where
  check : Bool → List Term → List Term → Maybe Name
  check true (z₀ ∷ []) (o₀ ∷ []) with extractNat z₀ | extractNat o₀
  ... | just 0 | just 1 = just cz
  ... | _      | _      = nothing
  check _ _ _ = nothing
litConstructor _ = nothing

data RingOpKind : Set where
  isAdd isMul isZero isOne otherOp : RingOpKind

-- Match a `Name` against the four operator Terms.
classifyOp : RingOperatorTerms → Name → TC RingOpKind
classifyOp ops nm = do
  nameTerm ← normalise (def nm [])
  let nmH = just nm
  let match : Term → Bool
      match t = (nameTerm =α= t) ∨ (nmH ≡ᵐ headName t)
  pure (if match (RingOperatorTerms.add   ops) then isAdd
        else if match (RingOperatorTerms.mul   ops) then isMul
        else if match (RingOperatorTerms.zero# ops) then isZero
        else if match (RingOperatorTerms.one#  ops) then isOne
        else otherOp)

checkIsRing : Term → TC Term
checkIsRing ring = checkType ring `CommutativeSemiring

module RingReflection (`R : Term) where

  -- `nm $ʳ args` produces `def nm (2 hidden ⊕ R ⊕ args)`, mirroring
  -- the calling convention of every `Solver` re-export.
  infixr 6 _$ʳ_
  _$ʳ_ : Name → Args Term → Term
  nm $ʳ args = def nm (2 ⋯⟅∷⟆ `R ⟨∷⟩ args)

  -- Fallback `RingOperatorTerms` for abstract bundles (e.g. a module
  -- parameter): each operator is the bundle projection applied to
  -- `R`. Used when `R` is not a concrete top-level `def`, so we can't
  -- `getDefinition` it to peek at the fields.
  abstractRingOperatorTerms : TC RingOperatorTerms
  abstractRingOperatorTerms = ⦇
    add⇒  normalise (def (quote CommutativeSemiring._+_) (2 ⋯⟅∷⟆ `R ⟨∷⟩ []))
    mul⇒  normalise (def (quote CommutativeSemiring._*_) (2 ⋯⟅∷⟆ `R ⟨∷⟩ []))
    zero⇒ normalise (def (quote CommutativeSemiring.0#)  (2 ⋯⟅∷⟆ `R ⟨∷⟩ []))
    one⇒  normalise (def (quote CommutativeSemiring.1#)  (2 ⋯⟅∷⟆ `R ⟨∷⟩ []))
    ⦈

  `refl : Term
  `refl = def (quote CommutativeSemiring.refl) (2 ⋯⟅∷⟆ `R ⟨∷⟩ 1 ⋯⟅∷⟆ [])

------------------------------------------------------------------------
-- Reflection utilities for the polynomial layer.

module RingSolverReflection (`R : Term) (numberOfVariables : ℕ) where
  open RingReflection `R

  `numberOfVariables : Term
  `numberOfVariables = toTerm numberOfVariables

  infix -1 _$ᵖ_
  _$ᵖ_ : Name → List (Arg Term) → Term
  nm $ᵖ xs = def nm (2 ⋯⟅∷⟆ `R ⟨∷⟩ `numberOfVariables ⟅∷⟆ xs)

  `con : Term → Term
  `con n = quote Solver.conP $ᵖ (n ⟨∷⟩ [])

  `var : Term → Term
  `var i = quote Solver.varP $ᵖ (i ⟨∷⟩ [])

  `:+ : Term → Term → Term
  `:+ x y = quote Solver._:+_ $ᵖ (x ⟨∷⟩ y ⟨∷⟩ [])

  `:* : Term → Term → Term
  `:* x y = quote Solver._:*_ $ᵖ (x ⟨∷⟩ y ⟨∷⟩ [])

  `:= : Term → Term → Term
  `:= x y = quote Solver._:=_ $ᵖ (x ⟨∷⟩ y ⟨∷⟩ [])

  `solver : Term → Term → Term
  `solver `f `eq = def (quote Solver.solve)
                       (2 ⋯⟅∷⟆ `R ⟨∷⟩ `numberOfVariables ⟨∷⟩ `f ⟨∷⟩ `eq ⟨∷⟩ [])

  toVarTerm : ℕ → Term
  toVarTerm i = `var (toFinTerm i)

  -- Convert raw user-Term to a Polynomial Term.
  --
  -- We recognise:
  --   * `_+_` / `_*_` as ring operators, including bundle-projection
  --     forms used in parameterised modules;
  --   * `0#` / `1#` as the polynomial constants `con 0` / `con 1`;
  --   * `lit (nat n)`, `con suc^k zero`, and `con C (lit n)` for a
  --     detected carrier-nat constructor `C` (e.g. ℤ's `+_`) — each
  --     decoded into `con n`;
  --   * `suc t` where `t` is non-literal — peeled into `con 1 :+ t`.
  --
  -- For anything else we call the supplied `fallback`, which `solve-≈`
  -- uses to look the term up in an atom table and emit
  -- `varP (Fin i)` for the matching atom (auto-quantification).
  convertTerm : RingOperatorTerms → (Term → Term) → Term → TC Term
  convertTerm operatorTerms fallback = convert
    where
    litCon : Maybe Name
    litCon = litConstructor operatorTerms

    mutual
      -- Try literal recognition first; then strip a `suc` and emit
      -- `con 1 :+ convert inner`; otherwise dispatch on the head.
      convert : Term → TC Term
      convert t with extractCarrierNat litCon t
      ... | just n  = pure (`con (toTerm n))
      ... | nothing = convertHead t

      convertHead : Term → TC Term
      convertHead (def nm xs) = do
        kind ← classifyOp operatorTerms nm
        case kind of λ where
          isAdd   → convertOp₂ `:+ xs
          isMul   → convertOp₂ `:* xs
          isZero  → pure (`con (toTerm 0))
          isOne   → pure (`con (toTerm 1))
          otherOp → pure (fallback (def nm xs))
      convertHead t@(con nm xs) with nm Name.≡ᵇ quote suc | xs
      ... | true | arg (arg-info visible _) x ∷ [] = do
        inner ← convert x
        pure (`:+ (`con (toTerm 1)) inner)
      ... | _    | _ = pure (fallback t)
      convertHead t = pure (fallback t)

      convertOp₂ : (Term → Term → Term) → Args Term → TC Term
      convertOp₂ mk (x ⟨∷⟩ y ⟨∷⟩ []) = do
        x' ← convert x
        y' ← convert y
        pure (mk x' y')
      convertOp₂ mk (x ∷ xs) = convertOp₂ mk xs
      convertOp₂ _  _        = pure (`con (toTerm 0))

------------------------------------------------------------------------

open RingReflection
open RingSolverReflection

-- Collect the def-Names of every recognised ring-operator occurrence
-- in the user term (used to seed the `withReduceDefs` block list).
collectOpNames : RingOperatorTerms → Term → List Name → TC (List Name)
collectOpNames operatorTerms = collect
  where
  mutual
    collect : Term → List Name → TC (List Name)
    collect (def nm xs) acc = do
      kind ← classifyOp operatorTerms nm
      case kind of λ where
        otherOp → pure acc
        isZero  → pure (insertName nm acc)
        isOne   → pure (insertName nm acc)
        isAdd   → collectArgs xs (insertName nm acc)
        isMul   → collectArgs xs (insertName nm acc)
    collect _ acc = pure acc

    collectArgs : Args Term → List Name → TC (List Name)
    collectArgs []                                acc = pure acc
    collectArgs (arg (arg-info visible _) x ∷ xs) acc = do
      acc1 ← collect x acc
      collectArgs xs acc1
    collectArgs (_ ∷ xs)                          acc = collectArgs xs acc

-- Walk a Term, accumulating atomic subterms into the supplied list.
-- Operators and ℕ literals are decomposed/skipped; anything else
-- becomes an atom.
collectAtoms : RingOperatorTerms → Term → List Term → TC (List Term)
collectAtoms operatorTerms = collect
  where
  litCon : Maybe Name
  litCon = litConstructor operatorTerms

  mutual
    collect : Term → List Term → TC (List Term)
    collect t acc with extractCarrierNat litCon t
    ... | just _  = pure acc
    ... | nothing = collectHead t acc

    collectHead : Term → List Term → TC (List Term)
    collectHead (def nm xs) acc = do
      kind ← classifyOp operatorTerms nm
      case kind of λ where
        isAdd   → collectOp₂ xs acc
        isMul   → collectOp₂ xs acc
        isZero  → pure acc
        isOne   → pure acc
        otherOp → pure (insertAtom (def nm xs) acc)
    collectHead t@(con nm xs) acc with nm Name.≡ᵇ quote suc | xs
    ... | true | arg (arg-info visible _) x ∷ [] = collect x acc
    ... | _    | _ = pure (insertAtom t acc)
    collectHead t acc = pure (insertAtom t acc)

    collectOp₂ : Args Term → List Term → TC (List Term)
    collectOp₂ (x ⟨∷⟩ y ⟨∷⟩ []) acc = do
      acc1 ← collect x acc
      collect y acc1
    collectOp₂ (x ∷ xs) acc = collectOp₂ xs acc
    collectOp₂ []       acc = pure acc

------------------------------------------------------------------------
-- Inspect a bundle term `R` and produce its `RingOperatorTerms`
-- plus the list of underlying field-value Names to block via
-- `withReduceDefs`.

ringOperatorTerms : Term → TC (RingOperatorTerms × List Name)
ringOperatorTerms `R = do
  `R' ← headReduce 16 `R
  case `R' of λ where
    (con _ args) → case List.mapMaybe getVisible args of λ where
      (_ ∷ _ ∷ a ∷ m ∷ z ∷ o ∷ _ ∷ []) → do
        a' ← headReduce 16 a
        m' ← headReduce 16 m
        z' ← headReduce 16 z
        o' ← headReduce 16 o
        let ops = add⇒ a' mul⇒ m' zero⇒ z' one⇒ o'
        pure (ops , pickDefName a' (pickDefName m' (pickDefName z' (pickDefName o' []))))
      _ → fallback
    _ → fallback
  where
  fallback : TC (RingOperatorTerms × List Name)
  fallback = do
    ops ← RingReflection.abstractRingOperatorTerms `R
    pure (ops , [])

------------------------------------------------------------------------
-- `solve-≈`: closed-equation form with auto-quantification.

malformedClosedEqError : ∀ {a} {A : Set a} → Term → TC A
malformedClosedEqError found = typeError
  ( strErr "Malformed call to solve-≈."
  ∷ strErr "Expected target type to be of shape  LHS ≈ RHS."
  ∷ strErr "Instead: "
  ∷ termErr found
  ∷ [])

-- Atom-lookup fallback: given a Term, return its polynomial-var
-- form if it appears in the atoms list, else `con 0`.
atomFallback : Term → ℕ → List Term → Term → Term
atomFallback `R↑ numAtoms atoms t with findAtomIndex t atoms
... | just i  = toVarTerm `R↑ numAtoms i
... | nothing = `con `R↑ numAtoms (toTerm 0)

solve-≈-macro : Term → Term → TC ⊤
solve-≈-macro `R hole = do
  `R' ← checkIsRing `R
  commitTC
  operatorTerms , bundleNs ← ringOperatorTerms `R'

  `hole₀ ← inferType hole
  let _ , equation₀ = stripPis `hole₀
  opNamesFromGoal ← case getVisibleArgs 2 equation₀ of λ where
    (just (lhs₀ ∷ rhs₀ ∷ [])) → do
      ns ← collectOpNames operatorTerms lhs₀ []
      collectOpNames operatorTerms rhs₀ ns
    _ → pure []
  let opNames = bundleNs ++ opNamesFromGoal

  B.withReduceDefs (false , opNames) $ do
    -- Use `normalise` (not `reduce`) here: Agda's elaborator can
    -- leave the goal type wrapped in lambdas; `normalise` β-reduces
    -- those away.
    `hole ← normalise `hole₀

    -- Detect the deadlock: the goal contains metavariables that
    -- only this macro could resolve, so `blockOnMeta` would retry
    -- forever. We flag this when both sides have structure (so
    -- neither is a bare meta `blockOnMeta` could fill in via sibling
    -- constraints), some side has metas, AND no meta is shared
    -- across the equation.
    --
    -- A meta shared between LHS and RHS can be resolved by Agda
    -- propagating constraints across the equation, so we defer those
    -- to `blockOnMeta` instead of erroring.
    let _ , equationProbe = stripPis `hole
    case getVisibleArgs 2 equationProbe of λ where
      (just (lhs₀ ∷ rhs₀ ∷ [])) → do
        let bothStructured = not (bareMeta lhs₀) ∧ not (bareMeta rhs₀)
        let metasL         = metasOf lhs₀
        let metasR         = metasOf rhs₀
        let anyMetas       = not (null metasL ∧ null metasR)
        let sharedMeta     = shareMeta metasL metasR
        case bothStructured ∧ anyMetas ∧ not sharedMeta of λ where
          true  → typeError
            ( strErr "solve-≈: the goal `LHS ≈ RHS` has at least one side "
            ∷ strErr "containing an metavariable that could not be resolved. To run this "
            ∷ strErr "solver you must add type annotations to resolve these variables."
            ∷ [])
          false → pure tt
      _ → pure tt

    -- Block on any unresolved meta in the goal type so Agda's
    -- elaborator has a chance to resolve it via adjacent constraints.
    case firstMeta `hole of λ where
      (just m) → blockOnMeta m
      nothing  → pure tt
    let variablesAndTypes , equation = stripPis `hole
    let variables = List.map proj₁ variablesAndTypes
    let numPiVars = List.length variables

    just (lhs ∷ rhs ∷ []) ← pure (getVisibleArgs 2 equation)
      where nothing → malformedClosedEqError `hole

    -- Pass 1: collect atoms from LHS, then from RHS (preserving order).
    atoms₀ ← collectAtoms operatorTerms lhs []
    atoms  ← collectAtoms operatorTerms rhs atoms₀
    let numAtoms = List.length atoms

    -- Pass 2: convert with an atom-lookup fallback. The polynomial
    -- body lives at depth `numPiVars + numAtoms` relative to the
    -- macro's call-site (the wrapper lambdas re-introducing the
    -- pi-binders, then the polynomial-lambda's binders inside).
    let `R↓↓ = weaken (numPiVars + numAtoms) `R
    `lhsExpr ← convertTerm `R↓↓ numAtoms operatorTerms (atomFallback `R↓↓ numAtoms atoms) lhs
    `rhsExpr ← convertTerm `R↓↓ numAtoms operatorTerms (atomFallback `R↓↓ numAtoms atoms) rhs

    -- Build the lambda body and the `solve R N f refl atoms` term.
    -- At the wrapper-lambda level, depth is `numPiVars`; we use
    -- `R↓ = weaken numPiVars R` for `solver`/`refl`.
    let `R↓        = weaken numPiVars `R
    let lambdaBody = `:= `R↓↓ numAtoms `lhsExpr `rhsExpr
    let f          = prependVLams (replicate numAtoms "x") lambdaBody
    let bare       = `solver `R↓ numAtoms f (`refl `R↓)
    let solverCall = applyVisibleArgs bare atoms

    -- Wrap with the pi-binders that the user didn't introduce as patterns
    unify hole (prependVLams variables solverCall)

macro
  solve-≈ : Term → Term → TC ⊤
  solve-≈ = solve-≈-macro
