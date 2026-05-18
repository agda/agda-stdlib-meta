------------------------------------------------------------------------
-- An improved ring solver, based on the stdlib's one
--
-- Automatically handles variable introduction as required, properly
-- deals with most literals, has sensible defaults and a few other
-- bells and whistles. Also has an extensive test suite.

{-# OPTIONS --without-K --safe #-}

module Tactic.Solver.Ring where

open import Algebra using (CommutativeSemiring)
open import Data.Fin.Base              using (Fin)
open import Data.Vec.Base   as Vec     using (Vec; _∷_; [])
open import Data.List.Base  as List    using (List; _∷_; []; _++_; replicate; foldr; null)
open import Data.Bool.ListAction        using (any)
open import Data.Maybe.Base as Maybe   using (Maybe; just; nothing)
open import Data.Nat.Base              using (ℕ; suc; zero; _+_)
open import Data.Bool.Base             using (Bool; if_then_else_; true; false; _∧_; not)
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
open import Reflection.Utils.Args using (getVisibleArgs; vArgs)
open import Reflection.Utils.Core using (extractNat; pickDefName; insertName; insertAtom; findAtomIndex)
open import Reflection.Utils.Metas using (isMeta; firstMeta; findMetaIds)
open import Reflection.Utils.TCM using (headReduce)

private
  -- Try `extractNat` first; if that fails and we have a wrapping
  -- constructor name (e.g. ℤ's `+_ : ℕ → ℤ`), peel one layer of
  -- `con C (arg ∷ [])` and try again.  Used to recognise `(+ n)`
  -- on ℤ as a polynomial constant.
  peelLitCon : Name → Term → Maybe ℕ
  peelLitCon C (con nm xs) with nm Name.≡ᵇ C
  ... | false = nothing
  ... | true  = case vArgs xs of λ where
    (a ∷ []) → extractNat a
    _        → nothing
  peelLitCon _ _ = nothing

  extractCarrierNat : Maybe Name → Term → Maybe ℕ
  extractCarrierNat nothing  t = extractNat t
  extractCarrierNat (just C) t with extractNat t
  ... | just n  = just n
  ... | nothing = peelLitCon C t

------------------------------------------------------------------------
-- CommutativeSemiring-specific machinery.
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
  check (cz Name.≡ᵇ co) (vArgs argsZ) (vArgs argsO)
  where
  check : Bool → List Term → List Term → Maybe Name
  check true (z₀ ∷ []) (o₀ ∷ []) with extractNat z₀ | extractNat o₀
  ... | just 0 | just 1 = just cz
  ... | _      | _      = nothing
  check _ _ _ = nothing
litConstructor _ = nothing

data RingOpKind : Set where
  isAdd isMul isZero isOne otherOp : RingOpKind

-- Match a `Name` against the four operator Terms. Peels leading
-- λ-binders so η-expanded operators match too.
classifyOp : RingOperatorTerms → Name → RingOpKind
classifyOp (add⇒ a mul⇒ m zero⇒ z one⇒ o) nm =
  if match a then isAdd
  else if match m then isMul
  else if match z then isZero
  else if match o then isOne
  else otherOp
  where
  match : Term → Bool
  match (def nm' _)           = nm' Name.≡ᵇ nm
  match (lam _ (abs _ body))  = match body
  match _                     = false

checkIsRing : Term → TC Term
checkIsRing ring = checkType ring `CommutativeSemiring

-- Fallback `RingOperatorTerms` for abstract bundles (e.g. a module
-- parameter): each operator is the bundle projection applied to
-- `R`. Used when `R` is not a concrete top-level `def`, so we can't
-- `getDefinition` it to peek at the fields.
abstractRingOperatorTerms : Term → TC RingOperatorTerms
abstractRingOperatorTerms `R = ⦇
  add⇒  normalise (def (quote CommutativeSemiring._+_) (2 ⋯⟅∷⟆ `R ⟨∷⟩ []))
  mul⇒  normalise (def (quote CommutativeSemiring._*_) (2 ⋯⟅∷⟆ `R ⟨∷⟩ []))
  zero⇒ normalise (def (quote CommutativeSemiring.0#)  (2 ⋯⟅∷⟆ `R ⟨∷⟩ []))
  one⇒  normalise (def (quote CommutativeSemiring.1#)  (2 ⋯⟅∷⟆ `R ⟨∷⟩ []))
  ⦈

`refl : Term → Term
`refl `R = def (quote CommutativeSemiring.refl) (2 ⋯⟅∷⟆ `R ⟨∷⟩ 1 ⋯⟅∷⟆ [])

------------------------------------------------------------------------
-- Reflection utilities for the polynomial layer.

module RingSolverReflection (`R : Term) (numberOfVariables : ℕ) where

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

  `solver : Term → Term → List Term → Term
  `solver `f `eq atoms = def (quote Solver.solve)
                             (2 ⋯⟅∷⟆ `R ⟨∷⟩ `numberOfVariables ⟨∷⟩ `f ⟨∷⟩ `eq ⟨∷⟩ foldr _⟨∷⟩_ [] atoms)

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
  convertTerm : RingOperatorTerms → (Term → Term) → Term → Term
  convertTerm operatorTerms fallback = convert
    where
    litCon : Maybe Name
    litCon = litConstructor operatorTerms

    mutual
      -- Try literal recognition first; then strip a `suc` and emit
      -- `con 1 :+ convert inner`; otherwise dispatch on the head.
      convert : Term → Term
      convert t with extractCarrierNat litCon t
      ... | just n  = `con (toTerm n)
      ... | nothing = convertHead t

      convertHead : Term → Term
      convertHead (def nm xs) = case classifyOp operatorTerms nm of λ where
        isAdd   → convertOp₂ `:+ xs
        isMul   → convertOp₂ `:* xs
        isZero  → `con (toTerm 0)
        isOne   → `con (toTerm 1)
        otherOp → fallback (def nm xs)
      convertHead t@(con nm xs) with nm Name.≡ᵇ quote suc | xs
      ... | true | arg (arg-info visible _) x ∷ [] = `:+ (`con (toTerm 1)) (convert x)
      ... | _    | _ = fallback t
      convertHead t = fallback t

      convertOp₂ : (Term → Term → Term) → Args Term → Term
      convertOp₂ mk (x ⟨∷⟩ y ⟨∷⟩ []) = mk (convert x) (convert y)
      convertOp₂ mk (x ∷ xs) = convertOp₂ mk xs
      convertOp₂ _  _        = `con (toTerm 0)

------------------------------------------------------------------------

open RingSolverReflection

-- Collect the def-Names of every recognised ring-operator occurrence
-- in the user term (used to seed the `withReduceDefs` block list).
collectOpNames : RingOperatorTerms → Term → List Name → List Name
collectOpNames operatorTerms = collect
  where
  mutual
    collect : Term → List Name → List Name
    collect (def nm xs) acc = case classifyOp operatorTerms nm of λ where
      otherOp → acc
      isZero  → insertName nm acc
      isOne   → insertName nm acc
      isAdd   → collectArgs xs (insertName nm acc)
      isMul   → collectArgs xs (insertName nm acc)
    collect _ acc = acc

    collectArgs : Args Term → List Name → List Name
    collectArgs []                                acc = acc
    collectArgs (arg (arg-info visible _) x ∷ xs) acc = collectArgs xs (collect x acc)
    collectArgs (_ ∷ xs)                          acc = collectArgs xs acc

-- Walk a Term, accumulating atomic subterms into the supplied list.
-- Operators and ℕ literals are decomposed/skipped; anything else
-- becomes an atom.
collectAtoms : RingOperatorTerms → Term → List Term → List Term
collectAtoms operatorTerms = collect
  where
  litCon : Maybe Name
  litCon = litConstructor operatorTerms

  mutual
    collect : Term → List Term → List Term
    collect t acc with extractCarrierNat litCon t
    ... | just _  = acc
    ... | nothing = collectHead t acc

    collectHead : Term → List Term → List Term
    collectHead (def nm xs) acc = case classifyOp operatorTerms nm of λ where
      isAdd   → collectOp₂ xs acc
      isMul   → collectOp₂ xs acc
      isZero  → acc
      isOne   → acc
      otherOp → insertAtom (def nm xs) acc
    collectHead t@(con nm xs) acc with nm Name.≡ᵇ quote suc | xs
    ... | true | arg (arg-info visible _) x ∷ [] = collect x acc
    ... | _    | _ = insertAtom t acc
    collectHead t acc = insertAtom t acc

    collectOp₂ : Args Term → List Term → List Term
    collectOp₂ (x ⟨∷⟩ y ⟨∷⟩ []) acc = collect y (collect x acc)
    collectOp₂ (x ∷ xs) acc = collectOp₂ xs acc
    collectOp₂ []       acc = acc

------------------------------------------------------------------------
-- Inspect a bundle term `R` and produce its `RingOperatorTerms`
-- plus the list of underlying field-value Names to block via
-- `withReduceDefs`.

ringOperatorTerms : Term → TC (RingOperatorTerms × List Name)
ringOperatorTerms `R = do
  `R' ← headReduce 16 `R
  case `R' of λ where
    (con _ args) → case vArgs args of λ where
      (_ ∷ _ ∷ a ∷ m ∷ z ∷ o ∷ _ ∷ []) → do
        a' ← headReduce 16 a
        m' ← headReduce 16 m
        z' ← headReduce 16 z
        o' ← headReduce 16 o
        let ops = add⇒ a' mul⇒ m' zero⇒ z' one⇒ o'
        pure (ops , foldr pickDefName [] (a' ∷ m' ∷ z' ∷ o' ∷ []))
      _ → fallback
    _ → fallback
  where
  fallback : TC (RingOperatorTerms × List Name)
  fallback = do
    ops ← abstractRingOperatorTerms `R
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
  let opNamesFromGoal = case getVisibleArgs 2 equation₀ of λ where
        (just (lhs₀ ∷ rhs₀ ∷ [])) → collectOpNames operatorTerms rhs₀ (collectOpNames operatorTerms lhs₀ [])
        _ → []
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
        let bothStructured = not (isMeta lhs₀) ∧ not (isMeta rhs₀)
        let metasL         = findMetaIds lhs₀
        let metasR         = findMetaIds rhs₀
        let anyMetas       = not (null metasL ∧ null metasR)
        let sharedMeta     = any (λ x → any (Meta._≡ᵇ_ x) metasR) metasL
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
      where _ → malformedClosedEqError `hole

    -- Pass 1: collect atoms from LHS, then from RHS (preserving order).
    let atoms = collectAtoms operatorTerms rhs (collectAtoms operatorTerms lhs [])
    let numAtoms = List.length atoms

    -- Pass 2: convert with an atom-lookup fallback. The polynomial
    -- body lives at depth `numPiVars + numAtoms` relative to the
    -- macro's call-site (the wrapper lambdas re-introducing the
    -- pi-binders, then the polynomial-lambda's binders inside).
    let `R↓↓ = weaken (numPiVars + numAtoms) `R
    let `lhsExpr = convertTerm `R↓↓ numAtoms operatorTerms (atomFallback `R↓↓ numAtoms atoms) lhs
    let `rhsExpr = convertTerm `R↓↓ numAtoms operatorTerms (atomFallback `R↓↓ numAtoms atoms) rhs

    -- Build the lambda body and the `solve R N f refl atoms` term.
    -- At the wrapper-lambda level, depth is `numPiVars`; we use
    -- `R↓ = weaken numPiVars R` for `solver`/`refl`.
    let `R↓        = weaken numPiVars `R
    let lambdaBody = `:= `R↓↓ numAtoms `lhsExpr `rhsExpr
    let f          = prependVLams (replicate numAtoms "x") lambdaBody
    let solverCall = `solver `R↓ numAtoms f (`refl `R↓) atoms

    -- Wrap with the pi-binders that the user didn't introduce as patterns
    unify hole (prependVLams variables solverCall)

macro
  solve-≈ : Term → Term → TC ⊤
  solve-≈ = solve-≈-macro
