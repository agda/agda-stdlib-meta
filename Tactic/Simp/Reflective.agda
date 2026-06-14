-- SPIKE (round 2): single-macro-call frontend for the multi-sorted
-- reflective simplifier.
--
-- `simp! (quote rule₁ ∷ … ∷ [])` proves an equational goal by:
--   1. reifying the goal's two sides and every rule's lhs/rhs into
--      `Core.Expr` over shared value-level *sort* and *operation*
--      tables (no datatypes declared anywhere);
--   2. emitting one application of the verified object-level solver
--      `Core.Eval.solveAt`, extracted with `from-just!` — the
--      rewriting search runs by *evaluation* during type checking.
--
-- Reification:
--   * a sort is a normalised type, paired with a witness (any goal
--     subterm of that type) to serve as the cast-default;
--   * an application with visible arguments becomes an operation;
--     its implementation is a canonical λ-wrapped term with the
--     (closed) non-visible arguments baked in, e.g.
--     `λ x₁ x₂ → _++_ {ℓ} {ℕ} x₁ x₂`;
--   * anything else (literals, context variables, unapplied
--     constructors, partially-visible applications) is an opaque
--     arity-0 operation of its own sort — including function-typed
--     atoms like `suc` as an argument of `map`.
--
-- Rule soundness witnesses are `λ τ → rule (τ s₁ i₁) … (τ sₖ iₖ)`,
-- which typecheck by computation of `evalAt`.  Nothing here can
-- prove a false goal: every emitted term is fully re-checked.
--
-- Polymorphic rules (Phase C): leading parameter binders (sorts,
-- levels, and anything later binder types depend on — e.g. the
-- {a} {A : Set a} of ++-identityʳ, or lifted module parameters) are
-- instantiated by speculatively unifying the rule's lhs against the
-- goal's same-headed subterms; each distinct instantiation yields one
-- specialised rule.  A wrong match is harmless (the rule just never
-- fires) — soundness never depends on the matcher.
--
-- Spike restrictions: all sorts at one universe level; parameter
-- binders must precede pattern binders; unconditional ≡-rules.
-- Notably, `--lossy-unification` is NOT needed.

{-# OPTIONS --safe #-}

module Tactic.Simp.Reflective where

open import Class.DecEq
open import Class.Functor
open import Class.MonadReader.Instances
open import Class.MonadTC.Instances
open import Class.Show
open import Class.Traversable

open import Data.Bool hiding (_≤_; _<_)
open import Data.Maybe hiding (_>>=_; map; zip)
open import Data.Unit
open import Data.List
open import Data.Nat
open import Data.Nat.Properties
open import Data.Product hiding (map; zip)

open import Function

open import Relation.Binary.PropositionalEquality

open import Meta.Init
open import Meta.Prelude
open import Reflection.AST.Literal using (nat)
open import Reflection.AlphaEquality
open import Reflection.Tactic
open import Reflection.Utils hiding (args; headName)
open import Reflection.Utils.TCI using (unifyStrict)

open import Class.Monad
open import Class.MonadError
open import Class.MonadReader

import Tactic.Simp.Reflective.Core as RC

open MonadError ⦃...⦄

-- Extensible rule dictionaries.  Declare a dummy type
--   data MyDict : Set where
-- and register rules as instances
--   instance myRule : Simp MyDict; myRule = mkSimp (quote myLemma)
-- then call `simpD! MyDict`.  Declared fresh here (no dependency on the
-- lossy `Tactic.Simp` module, which has its own `Simp` of the same name).
record Simp (D : Set) : Set where
  constructor mkSimp
  field ruleName : Name

-- Carries the goal relation's transitivity and reflexivity witnesses
-- for `simpRel!` (declared fresh; no dependency on the lossy
-- `Tactic.Simp`, which has its own `RelInfo`).
record RelInfo : Set where
  constructor mkRelInfo
  field relTrans relRefl : Name

private

  ----------------------------------------------------------------
  -- Reification state: sort table + operation table.
  ----------------------------------------------------------------

  -- sorts: (normalised type , witness term valid in the goal context)
  -- ops:   (canonical impl term , argument sorts , result sort)
  record St : Set where
    constructor mkSt
    field sorts  : List (Term × Maybe Term)
          ops    : List (Term × List ℕ × ℕ)
          -- The goal relation's bundle parameter `M` (e.g. an abstract
          -- `Monoid`), if any.  A bundle operation `R.op M args…` is a
          -- record projection whose FIRST explicit arg is the bundle;
          -- it is dropped during reification (baked into the impl like
          -- a hidden arg) so that `M` — whose type sits at a higher
          -- universe level than the carrier — never becomes a sort.
          bundle : Maybe Term

  keepW : Maybe Term → Maybe Term → Maybe Term
  keepW (just w) _ = just w
  keepW nothing  w = w

  addSort : Term → Maybe Term → St → ℕ × St
  addSort ty w (mkSt sorts ops b) =
    let (i , sorts′) = go sorts in (i , mkSt sorts′ ops b)
    where
      go : List (Term × Maybe Term) → ℕ × List (Term × Maybe Term)
      go [] = 0 , (ty , w) ∷ []
      go ((ty′ , w′) ∷ rest) =
        if ty =α= ty′
          then (0 , (ty′ , keepW w′ w) ∷ rest)
          else (let (i , rest′) = go rest in suc i , (ty′ , w′) ∷ rest′)

  eqSorts : List ℕ → List ℕ → Bool
  eqSorts []       []       = true
  eqSorts (a ∷ as) (b ∷ bs) = (Data.Nat._≡ᵇ_ a b) ∧ eqSorts as bs
  eqSorts _        _        = false

  addOp : Term → List ℕ → ℕ → St → ℕ × St
  addOp im as r (mkSt sorts ops b) =
    let (i , ops′) = go ops in (i , mkSt sorts ops′ b)
    where
      go : List (Term × List ℕ × ℕ) → ℕ × List (Term × List ℕ × ℕ)
      go [] = 0 , (im , as , r) ∷ []
      go (e@(im′ , as′ , r′) ∷ rest) =
        if (im =α= im′) ∧ eqSorts as as′ ∧ (Data.Nat._≡ᵇ_ r r′)
          then (0 , e ∷ rest)
          else (let (i , rest′) = go rest in suc i , e ∷ rest′)

  -- Look up an operation by its (α-equal) impl, returning its flat
  -- index and result sort.  The result sort of an application is
  -- determined by its impl (the head plus baked-in implicit/level
  -- args), so a repeat occurrence can reuse the stored sort instead of
  -- re-running the (expensive) `inferType >>= normalise` in `inferSort`.
  findOpByImpl : Term → List (Term × List ℕ × ℕ) → Maybe (ℕ × ℕ)
  findOpByImpl im []                   = nothing
  findOpByImpl im ((im′ , _ , r′) ∷ rest) =
    if im =α= im′
      then just (0 , r′)
      else (case findOpByImpl im rest of λ where
        (just (i , r)) → just (suc i , r)
        nothing        → nothing)

  -- The type stored at a sort index (for re-merging a witness on the
  -- op-reuse fast path without re-inferring the type).
  sortTypeAt : ℕ → List (Term × Maybe Term) → Maybe Term
  sortTypeAt _       []            = nothing
  sortTypeAt zero    ((ty , _) ∷ _) = just ty
  sortTypeAt (suc n) (_ ∷ rest)    = sortTypeAt n rest

  -- Merge a witness for an already-present sort (cheap: scans the small
  -- sort table, no `inferType`).  `addSort` on the same type hits and
  -- `keepW`-merges the witness.
  mergeW : ℕ → Maybe Term → St → St
  mergeW s w st = case sortTypeAt s (St.sorts st) of λ where
    (just ty) → proj₂ (addSort ty w st)
    nothing   → st

  ----------------------------------------------------------------
  -- de Bruijn utilities.
  ----------------------------------------------------------------

  -- Does t mention a free variable with (depth-adjusted) index < thr?
  mutual
    uvb : ℕ → ℕ → Term → Bool
    uvb thr k (var x as)           = ((k ≤ᵇ x) ∧ (x <ᵇ k + thr)) ∨ uvbArgs thr k as
    uvb thr k (def _ as)           = uvbArgs thr k as
    uvb thr k (con _ as)           = uvbArgs thr k as
    uvb thr k (lam _ (abs _ t))    = uvb thr (suc k) t
    uvb thr k (pi (arg _ a) (abs _ b)) = uvb thr k a ∨ uvb thr (suc k) b
    uvb thr k (meta _ as)          = uvbArgs thr k as
    uvb thr k (sort (set t))       = uvb thr k t
    uvb thr k (sort (prop t))      = uvb thr k t
    uvb thr k (pat-lam _ _)        = true   -- conservative
    uvb thr k _                    = false

    uvbArgs : ℕ → ℕ → Args Term → Bool
    uvbArgs thr k []             = false
    uvbArgs thr k (arg _ t ∷ as) = uvb thr k t ∨ uvbArgs thr k as

  usesVarBelow : ℕ → Term → Bool
  usesVarBelow thr = uvb thr 0

  -- Remove d rule binders from a term known not to mention them.
  strengthenBy : ℕ → Term → Term
  strengthenBy d = mapVars (_∸ d)

  -- Canonicalize ℕ numerals: `zero`/`suc (lit n)` constructor spellings
  -- and literals denote the same values but are distinct reflected
  -- terms, which would give distinct atom keys (a rule stated with `0`
  -- would not match a goal written with `zero`).  Normalise every term
  -- entering the reifier to the literal spelling.
  mutual
    canonNums : Term → Term
    canonNums (con c as) = canonCon c (canonNumsArgs as)
    canonNums (def f as) = def f (canonNumsArgs as)
    canonNums (var x as) = var x (canonNumsArgs as)
    canonNums (lam v (abs s t)) = lam v (abs s (canonNums t))
    canonNums (pi (arg i a) (abs s b)) =
      pi (arg i (canonNums a)) (abs s (canonNums b))
    canonNums t = t

    canonNumsArgs : Args Term → Args Term
    canonNumsArgs []             = []
    canonNumsArgs (arg i t ∷ as) = arg i (canonNums t) ∷ canonNumsArgs as

    canonCon : Name → Args Term → Term
    canonCon c [] =
      if c == quote ℕ.zero then lit (nat 0) else con c []
    canonCon c as@(arg _ (lit (nat n)) ∷ []) =
      if c == quote ℕ.suc then lit (nat (suc n)) else con c as
    canonCon c as = con c as

  -- Does t mention the free variable with (depth-adjusted) index i?
  mutual
    mvT : ℕ → ℕ → Term → Bool
    mvT i k (var x as)               = (Data.Nat._≡ᵇ_ (k + i) x) ∨ mvArgs i k as
    mvT i k (def _ as)               = mvArgs i k as
    mvT i k (con _ as)               = mvArgs i k as
    mvT i k (lam _ (abs _ t))        = mvT i (suc k) t
    mvT i k (pi (arg _ a) (abs _ b)) = mvT i k a ∨ mvT i (suc k) b
    mvT i k (meta _ as)              = mvArgs i k as
    mvT i k (sort (set t))           = mvT i k t
    mvT i k (sort (prop t))          = mvT i k t
    mvT i k (pat-lam _ _)            = true   -- conservative
    mvT i k _                        = false

    mvArgs : ℕ → ℕ → Args Term → Bool
    mvArgs i k []             = false
    mvArgs i k (arg _ t ∷ as) = mvT i k t ∨ mvArgs i k as

  mentionsVar : ℕ → Term → Bool
  mentionsVar i = mvT i 0

  -- All def/con-headed subterms (not descending under binders).
  mutual
    subApps : Term → List Term
    subApps t@(def _ as) = t ∷ subAppsArgs as
    subApps t@(con _ as) = t ∷ subAppsArgs as
    subApps (var _ as)   = subAppsArgs as
    subApps _            = []

    subAppsArgs : Args Term → List Term
    subAppsArgs []             = []
    subAppsArgs (arg _ t ∷ as) = subApps t ++ subAppsArgs as

  headName : Term → Maybe Name
  headName (def f _) = just f
  headName (con c _) = just c
  headName _         = nothing

  ----------------------------------------------------------------
  -- Quoting helpers.
  ----------------------------------------------------------------

  quoteList : List Term → Term
  quoteList []       = con (quote List.[]) []
  quoteList (t ∷ ts) = con (quote List._∷_) (vArg t ∷ vArg (quoteList ts) ∷ [])

  quotePair : Term → Term → Term
  quotePair a b = con (quote _,_) (vArg a ∷ vArg b ∷ [])

  `ℕ : ℕ → Term
  `ℕ n = lit (nat n)

  ----------------------------------------------------------------
  -- Canonical operation implementations.
  ----------------------------------------------------------------

  rebuild : Term → Args Term → Term
  rebuild (def f _) as = def f as
  rebuild (con c _) as = con c as
  rebuild t         _  = t

  wrapLams : ℕ → Term → Term
  wrapLams zero    b = b
  wrapLams (suc n) b = `λ "x" ⇒ wrapLams n b

  countVisible : Args Term → ℕ
  countVisible []                                  = 0
  countVisible (arg (arg-info visible _) _ ∷ as)   = suc (countVisible as)
  countVisible (_ ∷ as)                            = countVisible as

  filterVisible : Args Term → List Term
  filterVisible []                                 = []
  filterVisible (arg (arg-info visible _) t ∷ as)  = t ∷ filterVisible as
  filterVisible (_ ∷ as)                           = filterVisible as

  anyHiddenOpen : ℕ → Args Term → Bool
  anyHiddenOpen depth []                                 = false
  anyHiddenOpen depth (arg (arg-info visible _) _ ∷ as)  = anyHiddenOpen depth as
  anyHiddenOpen depth (arg _ t ∷ as)                     =
    usesVarBelow depth t ∨ anyHiddenOpen depth as

  -- First/last visible argument of an application's arg list.
  firstVisibleArg : Args Term → Maybe Term
  firstVisibleArg []                                = nothing
  firstVisibleArg (arg (arg-info visible _) t ∷ _)  = just t
  firstVisibleArg (_ ∷ as)                          = firstVisibleArg as

  lastVisibleArg : Args Term → Maybe Term
  lastVisibleArg = go nothing
    where
      go : Maybe Term → Args Term → Maybe Term
      go acc []                                 = acc
      go acc (arg (arg-info visible _) t ∷ as)  = go (just t) as
      go acc (_ ∷ as)                           = go acc as

  -- Should this application's first visible arg be dropped as the
  -- bundle?  Yes iff the goal has a bundle `M` and the arg (strengthened
  -- out of the rule telescope) is α-equal to it.
  shouldDrop : ℕ → Maybe Term → Args Term → Bool
  shouldDrop depth (just bM) as = case firstVisibleArg as of λ where
    (just t) → strengthenBy depth t =α= bM
    nothing  → false
  shouldDrop _ nothing _ = false

  -- λ x₁ … xₙ → head {hidden…} x₁ … xₙ  with the closed non-visible
  -- arguments strengthened out of the rule telescope and shifted under
  -- the new lambdas.  When `dropFst`, the FIRST visible arg is also
  -- baked in (the bundle `M`), not bound — so the op has one fewer
  -- operand.
  mkImpl : ℕ → Bool → Term → Args Term → Term
  mkImpl depth dropFst hd as = wrapLams n (rebuild hd (go 0 false as))
    where
      n : ℕ
      n = countVisible as ∸ (if dropFst then 1 else 0)

      go : ℕ → Bool → Args Term → Args Term
      go k seen []                                   = []
      go k seen (arg i@(arg-info visible _) t ∷ rest) =
        if dropFst ∧ not seen
          then arg i (mapVars (λ v → v ∸ depth + n) t) ∷ go k true rest
          else arg i (var (n ∸ 1 ∸ k) []) ∷ go (suc k) seen rest
      go k seen (arg i t ∷ rest)                     =
        arg i (mapVars (λ v → v ∸ depth + n) t) ∷ go k seen rest

  ----------------------------------------------------------------
  -- Reification: Term → Core.Expr, growing the tables.
  -- `depth` is the rule telescope length (0 for goal terms); de
  -- Bruijn vars below it are pattern variables with sorts `pats`.
  ----------------------------------------------------------------

  -- quoteTC under normalisation = false (the TCEnv default) reifies
  -- the unevaluated computation graph of the value as syntax — for
  -- our lazily-built Exprs that yields astronomically large terms.
  -- Quote the normal form instead.
  quoteNorm : RC.Expr → TC Term
  quoteNorm e = local (λ env → record env { normalisation = true }) (quoteTC e)

  inferSort : ℕ → St → Term → Maybe Term → TC (ℕ × St)
  inferSort depth st t w = do
    ty ← inferType t >>= normalise
    case usesVarBelow depth ty of λ where
      true  → error1 ("simp!: subterm type depends on rule variables (unsupported): " <+> show ty)
      false → return (addSort (strengthenBy depth ty) w st)

  witnessOf : ℕ → Term → Maybe Term
  witnessOf depth t =
    if usesVarBelow depth t then nothing else just (strengthenBy depth t)

  mutual
    conv : ℕ → List ℕ → St → Term → TC (RC.Expr × St)
    conv depth pats st t@(var j as) =
      if j <ᵇ depth
        then (case as of λ where
          [] → case pats ⁉ j of λ where
            (just s) → return (RC.Expr.var j s , st)
            nothing  → error1 "simp!: internal error: missing pattern variable sort"
          _ → error1 "simp!: higher-order patterns unsupported")
        else convAtom depth st t
    conv depth pats st t@(def f as) = convApp depth pats st t (def f []) as
    conv depth pats st t@(con c as) = convApp depth pats st t (con c []) as
    conv depth pats st t            = convAtom depth st t

    convApp : ℕ → List ℕ → St → (orig hd : Term) → Args Term
            → TC (RC.Expr × St)
    convApp depth pats st orig hd as =
      case countVisible as of λ where
        0 → convAtom depth st orig
        _ → if anyHiddenOpen depth as
          then error1 ("simp!: hidden arguments mention rule variables (polymorphic rule? use a monomorphic wrapper): " <+> show orig)
          else (do
            let drop = shouldDrop depth (St.bundle st) as
            (es , st₁) ← convArgs depth pats st drop as
            let im = mkImpl depth drop hd as
            case findOpByImpl im (St.ops st₁) of λ where
              -- Repeat operator: result sort already known, skip inferType;
              -- still merge a witness this occurrence may supply.
              (just (o , r)) → return (RC.Expr.op o r es , mergeW r (witnessOf depth orig) st₁)
              nothing → do
                (r  , st₂) ← inferSort depth st₁ orig (witnessOf depth orig)
                let (o , st₃) = addOp im (map RC.sortOf es) r st₂
                return (RC.Expr.op o r es , st₃))

    -- Converts the visible arguments only (structural recursion on the
    -- arg list).  `drop` skips the first visible arg (the bundle).
    convArgs : ℕ → List ℕ → St → Bool → Args Term → TC (List RC.Expr × St)
    convArgs depth pats st drop [] = return ([] , st)
    convArgs depth pats st drop (arg (arg-info visible _) t ∷ as) =
      if drop
        then convArgs depth pats st false as
        else (do
          (e  , st₁) ← conv depth pats st t
          (es , st₂) ← convArgs depth pats st₁ false as
          return (e ∷ es , st₂))
    convArgs depth pats st drop (_ ∷ as) = convArgs depth pats st drop as

    convAtom : ℕ → St → Term → TC (RC.Expr × St)
    convAtom depth st t =
      case usesVarBelow depth t of λ where
        true  → error1 ("simp!: opaque subterm mentions rule variables (unsupported): " <+> show t)
        false → do
          let t′ = strengthenBy depth t
          case findOpByImpl t′ (St.ops st) of λ where
            -- Repeat atom: sort already known, skip inferType;
            -- still merge this atom as a witness for its sort.
            (just (o , s)) → return (RC.Expr.op o s [] , mergeW s (just t′) st)
            nothing → do
              (s , st₁) ← inferSort depth st t (just t′)
              let (o , st₂) = addOp t′ [] s st₁
              return (RC.Expr.op o s [] , st₂)

  ----------------------------------------------------------------
  -- Rule processing.
  ----------------------------------------------------------------

  -- Binder classification: a binder is a *parameter* if its type is
  -- a sort/Level, or if a later binder's type mentions it.  Parameter
  -- binders get instantiated from the goal (Phase C); the remaining
  -- (pattern) binders become engine pattern variables.
  anyB : {A : Set} → (A → Bool) → List A → Bool
  anyB f []       = false
  anyB f (x ∷ xs) = f x ∨ anyB f xs

  isParamType : Term → Bool
  isParamType (def f _) = f == quote Level
  isParamType (sort _)  = true
  isParamType _         = false

  classify : List (ArgInfo × Term) → List Bool
  classify tel = go 0 tel
    where
      laterMentions : ℕ → Bool
      laterMentions k = anyB
        (λ p → (k <ᵇ proj₁ p) ∧ mentionsVar (proj₁ p ∸ 1 ∸ k) (proj₂ (proj₂ p)))
        (enumerate tel)
      go : ℕ → List (ArgInfo × Term) → List Bool
      go k []               = []
      go k ((_ , ty) ∷ tel′) = (isParamType ty ∨ laterMentions k) ∷ go (suc k) tel′

  countLeading : List Bool → ℕ
  countLeading (true ∷ bs) = suc (countLeading bs)
  countLeading _           = 0

  -- Strip the Pi telescope, reducing at every step (so type aliases
  -- like RightIdentity unfold), inside the appropriately extended
  -- context.  Fueled because the recursion is on `reduce` output.
  stripAndReduce : ℕ → Term → TC (Term × List (ArgInfo × Term))
  stripAndReduce 0          ty = return (ty , [])
  stripAndReduce (suc fuel) ty = do
    ty′ ← reduce ty
    case ty′ of λ where
      (pi a@(arg i dom) (abs x b)) → do
        (body , tel) ← extendContext (x , a) (stripAndReduce fuel b)
        return (body , (i , canonNums dom) ∷ tel)
      _ → return (canonNums ty′ , [])

  -- Pure first-order matching of a rule lhs (over d binders) against
  -- a goal subterm: rule-binder variables are wildcards, bound
  -- consistently up to =α=; everything else must match literally
  -- (modulo the de Bruijn shift d on goal-context variables).
  -- A wrong instantiation is harmless: the engine re-verifies all.
  lookupB : List (ℕ × Term) → ℕ → Maybe Term
  lookupB []            _ = nothing
  lookupB ((j , t) ∷ σ) i =
    if Data.Nat._≡ᵇ_ i j then just t else lookupB σ i

  mutual
    matchT : ℕ → Term → Term → List (ℕ × Term) → Maybe (List (ℕ × Term))
    matchT d (var j []) t σ =
      if j <ᵇ d
        then (case lookupB σ j of λ where
          (just t′) → if t =α= t′ then just σ else nothing
          nothing   → just ((j , t) ∷ σ))
        else (case t of λ where
          (var j′ []) → if Data.Nat._≡ᵇ_ (j ∸ d) j′ then just σ else nothing
          _           → nothing)
    matchT d (def f as) (def f′ as′) σ =
      if f == f′ then matchAs d as as′ σ else nothing
    matchT d (con c as) (con c′ as′) σ =
      if c == c′ then matchAs d as as′ σ else nothing
    matchT d t@(lit _) t′ σ = if t =α= t′ then just σ else nothing
    matchT d _ _ _ = nothing

    matchAs : ℕ → Args Term → Args Term → List (ℕ × Term)
            → Maybe (List (ℕ × Term))
    matchAs d []             []               σ = just σ
    matchAs d (arg _ t ∷ as) (arg _ t′ ∷ as′) σ = case matchT d t t′ σ of λ where
      (just σ′) → matchAs d as as′ σ′
      nothing   → nothing
    matchAs d _ _ _ = nothing

  -- Read off the bindings of the first p (parameter) binders.
  collectP : ℕ → ℕ → ℕ → List (ℕ × Term) → Maybe (List Term)
  collectP d zero    k σ = just []
  collectP d (suc r) k σ = case lookupB σ (d ∸ 1 ∸ k) of λ where
    (just t) → (case collectP d r (suc k) σ of λ where
      (just ts) → just (t ∷ ts)
      nothing   → nothing)
    nothing  → nothing

  tryCandS : ℕ → ℕ → Term → Term → Maybe (List Term)
  tryCandS d p lhs cand = case matchT d lhs cand [] of λ where
    (just σ) → collectP d p 0 σ
    nothing  → nothing

  eqTermList : List Term → List Term → Bool
  eqTermList []       []       = true
  eqTermList (a ∷ as) (b ∷ bs) = (a =α= b) ∧ eqTermList as bs
  eqTermList _        _        = false

  addUnique : List Term → List (List Term) → List (List Term)
  addUnique vs [] = vs ∷ []
  addUnique vs (vs′ ∷ rest) =
    if eqTermList vs vs′ then vs′ ∷ rest else vs′ ∷ addUnique vs rest

  findAssignments : ℕ → ℕ → Name → Term → List Term → List (List Term)
  findAssignments d p hd lhs [] = []
  findAssignments d p hd lhs (c ∷ cs) =
    let rest = findAssignments d p hd lhs cs
        r    = case headName c of λ where
          (just h) → if h == hd then tryCandS d p lhs c else nothing
          nothing  → nothing
    in case r of λ where
      (just vs) → addUnique vs rest
      nothing   → rest

  ----------------------------------------------------------------
  -- Instantiation enrichment (item 10).  Polymorphic-rule
  -- instantiation (`findAssignments`) only scans goal subterms, so a
  -- candidate that appears solely in another rule's instantiated rhs is
  -- invisible.  Before processing, we grow the candidate pool: for each
  -- rule we load its GENERIC lhs/rhs at the Term level (all telescope
  -- binders as wildcards), match the lhs against each existing
  -- candidate, and on a FULL binding (every variable used in the rhs is
  -- bound) substitute into the rhs to obtain a new closed goal-context
  -- term, adding its `subApps`.  Iterated to a fixpoint with hard caps.
  -- Enlarging the pool is SAFE: a wrong candidate just never fires.
  ----------------------------------------------------------------

  -- Append extra args to a head term (no de Bruijn shift here).
  applyTerm : Term → Args Term → Term
  applyTerm (var k as) extra = var k (as ++ extra)
  applyTerm (def f as) extra = def f (as ++ extra)
  applyTerm (con c as) extra = con c (as ++ extra)
  applyTerm t          _     = t

  -- Substitute meta-level bindings (rule-index → goal Term) into a rule
  -- body term: rule-binder vars (j < d) get replaced by their binding;
  -- goal-context vars (j ≥ d) are strengthened by d.  Used by Option B
  -- and the enrichment pass.
  mutual
    substRuleVars : ℕ → List (ℕ × Term) → Term → Term
    substRuleVars d σ (var j as) =
      if j <ᵇ d
        then (case lookupB σ j of λ where
          (just t) → applyTerm t (substRuleArgs d σ as)
          nothing  → var j (substRuleArgs d σ as))    -- (shouldn't happen if fully matched)
        else var (j ∸ d) (substRuleArgs d σ as)
    substRuleVars d σ (def f as) = def f (substRuleArgs d σ as)
    substRuleVars d σ (con c as) = con c (substRuleArgs d σ as)
    substRuleVars d σ t          = t

    substRuleArgs : ℕ → List (ℕ × Term) → Args Term → Args Term
    substRuleArgs d σ []             = []
    substRuleArgs d σ (arg i t ∷ as) = arg i (substRuleVars d σ t) ∷ substRuleArgs d σ as

  -- The free rule-binder variables (index < d) mentioned in a term.
  mutual
    fvb : ℕ → ℕ → Term → List ℕ
    fvb d k (var x as) =
      let here = if (k ≤ᵇ x) ∧ (x <ᵇ k + d) then (x ∸ k) ∷ [] else []
      in here ++ fvbArgs d k as
    fvb d k (def _ as)            = fvbArgs d k as
    fvb d k (con _ as)            = fvbArgs d k as
    fvb d k (lam _ (abs _ t))     = fvb d (suc k) t
    fvb d k (pi (arg _ a) (abs _ b)) = fvb d k a ++ fvb d (suc k) b
    fvb d k _                     = []

    fvbArgs : ℕ → ℕ → Args Term → List ℕ
    fvbArgs d k []             = []
    fvbArgs d k (arg _ t ∷ as) = fvb d k t ++ fvbArgs d k as

  -- Every variable in `needed` is bound by σ.
  coversAll : List ℕ → List (ℕ × Term) → Bool
  coversAll []       σ = true
  coversAll (i ∷ is) σ = is-just (lookupB σ i) ∧ coversAll is σ

  -- α-dedup append of a single candidate term into a pool.
  addUniqueT : Term → List Term → List Term
  addUniqueT t []       = t ∷ []
  addUniqueT t (u ∷ us) = if t =α= u then u ∷ us else u ∷ addUniqueT t us

  -- One enrichment rule: telescope length + generic lhs/rhs (Term).
  data EnrichRule : Set where
    mkEnrichRule : (d : ℕ) (lhs rhs : Term) → EnrichRule

  loadEnrichRule : Name → TC EnrichRule
  loadEnrichRule n = do
    ty ← getType n
    (body , tel) ← stripAndReduce 100 ty
    case body of λ where
      (def (quote _≡_) (hArg _ ∷ hArg _ ∷ vArg lhs ∷ vArg rhs ∷ [])) →
        return (mkEnrichRule (length tel) lhs rhs)
      _ → return (mkEnrichRule 0 unknown unknown)   -- not an equation: inert

  -- Match one rule's lhs against one candidate; on a full binding emit
  -- the instantiated rhs (a closed goal-context term).
  enrichAt : EnrichRule → Term → Maybe Term
  enrichAt (mkEnrichRule d lhs rhs) cand =
    case matchT d lhs cand [] of λ where
      (just σ) → if coversAll (fvb d 0 rhs) σ
                   then just (substRuleVars d σ rhs)
                   else nothing
      nothing  → nothing

  -- One round: for every (rule, candidate) pair, add the subApps of any
  -- instantiated rhs to the pool (deduped).  Caps the pool size.
  enrichRound : ℕ → List EnrichRule → List Term → List Term → List Term
  enrichRound cap rs []         pool = pool
  enrichRound cap rs (c ∷ cs)   pool =
    let pool′ = goRules rs pool
    in enrichRound cap rs cs pool′
    where
      addAll : List Term → List Term → List Term
      addAll []       p = p
      addAll (t ∷ ts) p = if cap ≤ᵇ length p then p else addAll ts (addUniqueT t p)
      goRules : List EnrichRule → List Term → List Term
      goRules []       p = p
      goRules (r ∷ rs) p = case enrichAt r c of λ where
        (just inst) → goRules rs (addAll (subApps inst) p)
        nothing     → goRules rs p

  -- Fixpoint over ≤ `rounds` iterations or until the pool stops growing.
  enrich : ℕ → ℕ → List EnrichRule → List Term → List Term
  enrich 0          cap rs pool = pool
  enrich (suc more) cap rs pool =
    let pool′ = enrichRound cap rs pool pool
    in if length pool′ ≤ᵇ length pool
         then pool′
         else enrich more cap rs pool′

  -- Build the enrichment rules for a name list and enrich a pool.
  enrichCandidates : List Name → List Term → TC (List Term)
  enrichCandidates names pool = do
    rs ← traverse loadEnrichRule names
    return (enrich 3 100 rs pool)

  extendCtxTel : {A : Set} → List (ArgInfo × Term) → TC A → TC A
  extendCtxTel []             m = m
  extendCtxTel ((i , t) ∷ tel) m =
    extendContext ("x" , arg i t) (extendCtxTel tel m)

  -- Sorts of the rule binders, outermost-first.  Each binder type
  -- must not depend on earlier binders.
  goBinders : ℕ → St → List (ArgInfo × Term) → TC (List ℕ × St)
  goBinders k st [] = return ([] , st)
  goBinders k st ((_ , ty) ∷ tel) =
    case usesVarBelow k ty of λ where
      true  → error1 ("simp!: rule binder type depends on earlier binders (polymorphic rule? use a monomorphic wrapper): " <+> show ty)
      false → do
        ty′ ← normalise (strengthenBy k ty)
        let (s , st₁) = addSort ty′ nothing st
        (ss , st₂) ← goBinders (suc k) st₁ tel
        return (s ∷ ss , st₂)

  -- The applied head of a rule's soundness witness.  For a named lemma
  -- it is `def n …`; for a local hypothesis it is the hypothesis term
  -- itself, with the extra (τ-applied) arguments appended.
  data Head : Set where
    hName : Name → Head
    hTerm : Term → Head

  applyHead : Head → Args Term → Term
  applyHead (hName n) extra = def n extra
  applyHead (hTerm t) extra = applyTerm (mapVars suc t) extra

  -- λ τ → head pre… (τ s₁ i₁) … (τ sₖ iₖ): binder k (outermost-first,
  -- of d binders, with sort sₖ) is pattern variable d∸1∸k.  `pre` is
  -- the parameter instantiation (goal-context terms, hence shifted
  -- under the λ).  A hypothesis head carries no `pre` (`[]`) and is
  -- itself shifted under the λ by `applyHead`.  Typechecks by
  -- computation of `evalAt`.
  ----------------------------------------------------------------
  -- Permutativity auto-detection.  A rule is *permutative* iff its lhs
  -- and rhs Exprs are equal up to a BIJECTIVE renaming of pattern
  -- variables: same tree shape, same op indices and sorts, with a
  -- var-to-var correspondence that is consistent in BOTH directions.
  -- `+-comm` (x + y ≡ y + x) and left-commutativity qualify;
  -- associativity (different tree shape) does not.  Threading two
  -- binding maps (lhs-var → rhs-var and back) over the structure.
  ----------------------------------------------------------------

  lookupℕ : List (ℕ × ℕ) → ℕ → Maybe ℕ
  lookupℕ []            _ = nothing
  lookupℕ ((a , b) ∷ m) i = if Data.Nat._≡ᵇ_ i a then just b else lookupℕ m i

  -- m : lhs-var → rhs-var ; m⁻ : rhs-var → lhs-var.  Extend both maps
  -- consistently or fail (already-bound to a different partner ⇒ fail).
  bindVar : ℕ → ℕ → List (ℕ × ℕ) → List (ℕ × ℕ)
          → Maybe (List (ℕ × ℕ) × List (ℕ × ℕ))
  bindVar i j m m⁻ with lookupℕ m i | lookupℕ m⁻ j
  ... | just j′ | just i′ = if Data.Nat._≡ᵇ_ j j′ ∧ Data.Nat._≡ᵇ_ i i′
                              then just (m , m⁻) else nothing
  ... | nothing | nothing = just ((i , j) ∷ m , (j , i) ∷ m⁻)
  ... | _       | _       = nothing   -- one bound, one free ⇒ not bijective

  mutual
    permMatch : RC.Expr → RC.Expr → List (ℕ × ℕ) → List (ℕ × ℕ)
              → Maybe (List (ℕ × ℕ) × List (ℕ × ℕ))
    permMatch (RC.Expr.var i s) (RC.Expr.var j s′) m m⁻ =
      if Data.Nat._≡ᵇ_ s s′ then bindVar i j m m⁻ else nothing
    permMatch (RC.Expr.op o s es) (RC.Expr.op o′ s′ es′) m m⁻ =
      if (Data.Nat._≡ᵇ_ o o′) ∧ (Data.Nat._≡ᵇ_ s s′)
        then permMatchs es es′ m m⁻ else nothing
    permMatch _ _ _ _ = nothing

    permMatchs : List RC.Expr → List RC.Expr → List (ℕ × ℕ) → List (ℕ × ℕ)
               → Maybe (List (ℕ × ℕ) × List (ℕ × ℕ))
    permMatchs []       []       m m⁻ = just (m , m⁻)
    permMatchs (a ∷ as) (b ∷ bs) m m⁻ = case permMatch a b m m⁻ of λ where
      (just (m′ , m⁻′)) → permMatchs as bs m′ m⁻′
      nothing           → nothing
    permMatchs _ _ _ _ = nothing

  allId : List (ℕ × ℕ) → Bool
  allId []            = true
  allId ((a , b) ∷ r) = Data.Nat._≡ᵇ_ a b ∧ allId r

  -- True iff lhs and rhs match up to a bijective variable renaming AND
  -- the rule is genuinely permutative (the renaming is not the identity;
  -- otherwise an ordinary already-oriented rule would be wrongly gated).
  isPerm : RC.Expr → RC.Expr → Bool
  isPerm lhs rhs = case permMatch lhs rhs [] [] of λ where
    (just (m , _)) → not (allId m)
    nothing        → false

  -- The quoted Bool used for the `perm` field of an emitted `mkRule`.
  permFlag : Bool → Term
  permFlag true  = con (quote Data.Bool.true)  []
  permFlag false = con (quote Data.Bool.false) []

  mkSoundTerm : Head → Args Term → List (ArgInfo × ℕ) → Term
  mkSoundTerm hd pre is =
    let d = length is
    in `λ "τ" ⇒ applyHead hd (map-Args (mapVars suc) pre ++ zipWithIndex
         (λ k p → arg (proj₁ p)
            (var 0 (vArg (`ℕ (proj₂ p)) ∷ vArg (`ℕ (d ∸ 1 ∸ k)) ∷ [])))
         is)

  elemName : Name → List Name → Bool
  elemName f []       = false
  elemName f (g ∷ gs) = (f == g) ∨ elemName f gs

  headsOf : List Term → List Name
  headsOf []       = []
  headsOf (c ∷ cs) = case headName c of λ where
    (just f) → f ∷ headsOf cs
    nothing  → headsOf cs

  -- Re-align a rule side whose head spelling differs from the goal's:
  -- rules re-exported through module applications state their operator
  -- as a record projection (e.g. ⊔-comm's `MaxOperator._⊔_ … x y`
  -- instead of `x ⊔ y`), which would never match.  If the side's head
  -- does not occur among the goal's heads, try one `reduce`; keep the
  -- reduced form only if its head DOES occur (this protects rules
  -- about definitional constants, whose original head occurs in the
  -- goal and must stay folded).
  realign : List Name → Term → TC Term
  realign gh t = case headName t of λ where
    (just f) → if elemName f gh
      then return t
      else (do
        t′ ← reduce t
        case headName t′ of λ where
          (just f′) → if elemName f′ gh then return (canonNums t′) else return t
          nothing   → return t)
    nothing → return t

  processRuleMono : List Name → Head → Args Term → List (ArgInfo × Term) → Term → St
                  → TC (Term × St)
  processRuleMono gh hd pre tel body st = do
    (def (quote _≡_) (hArg _ ∷ hArg _ ∷ vArg lhs ∷ vArg rhs ∷ [])) ← return body
      where _ → error1 ("simp!: not an equation: " <+> show body)
    let depth = length tel
    (bs , st₁) ← goBinders 0 st tel
    let pats = reverse bs
    (lhsE , rhsE , st₂) ← extendCtxTel tel (do
      lhs′ ← realign gh lhs
      rhs′ ← realign gh rhs
      (lhsE , sta) ← conv depth pats st₁ lhs′
      (rhsE , stb) ← conv depth pats sta rhs′
      return (lhsE , rhsE , stb))
    lhsT ← quoteNorm lhsE
    rhsT ← quoteNorm rhsE
    return ( con (quote RC.Eval.mkRule)
               ( vArg lhsT ∷ vArg rhsT ∷ vArg (con (quote refl) [])
               ∷ vArg (mkSoundTerm hd pre (zip (map proj₁ tel) bs))
               ∷ vArg (permFlag (isPerm lhsE rhsE)) ∷ [] )
           , st₂ )

  -- Specialise the rule at one parameter assignment: apply the lemma
  -- to the instantiation and let Agda compute the remaining type.
  processAssign : List Name → Name → List ArgInfo → St → List Term → TC (Term × St)
  processAssign gh n infos st vals = do
    let pre = Data.List.zipWith arg infos vals
    specTy ← inferType (def n pre)
    (body , tel) ← stripAndReduce 100 specTy
    processRuleMono gh (hName n) pre tel body st

  processAssigns : List Name → Name → List ArgInfo → St → List (List Term)
                 → TC (List Term × St)
  processAssigns gh n infos st []       = return ([] , st)
  processAssigns gh n infos st (v ∷ vs) = do
    (r  , st₁) ← processAssign gh n infos st v
    (rs , st₂) ← processAssigns gh n infos st₁ vs
    return (r ∷ rs , st₂)

  processRule : List Term → St → Name → TC (List Term × St)
  processRule cands st n = do
    ty ← getType n
    (body , tel) ← stripAndReduce 100 ty
    let flags = classify tel
        p     = countLeading flags
    if anyB id (drop p flags)
      then error1 ("simp!: rule parameters appear after pattern binders (unsupported): " <+> show n)
      else (case p of λ where
        zero → do
          (r , st₁) ← processRuleMono (headsOf cands) (hName n) [] tel body st
          return (r ∷ [] , st₁)
        _ → do
          (def (quote _≡_) (hArg _ ∷ hArg _ ∷ vArg lhs ∷ vArg _ ∷ [])) ← return body
            where _ → error1 ("simp!: not an equation: " <+> show body)
          (just hd) ← return (headName lhs)
            where nothing → error1 ("simp!: cannot instantiate a rule whose lhs is not an application: " <+> show n)
          case findAssignments (length tel) p hd lhs cands of λ where
            []    → error1 ("simp!: could not instantiate polymorphic rule from the goal: " <+> show n)
            asgns → processAssigns (headsOf cands) n (map proj₁ (take p tel)) st asgns)

  processRules : List Term → List Name → St → TC (List Term × St)
  processRules cands []       st = return ([] , st)
  processRules cands (n ∷ ns) st = do
    (rs₁ , st₁) ← processRule cands st n
    (rs₂ , st₂) ← processRules cands ns st₁
    return (rs₁ ++ rs₂ , st₂)

  -- A local hypothesis `h` (already shifted into the goal-leaf
  -- context) becomes a rule with head `hTerm h`.  Unlike named rules
  -- there is no Name to instantiate, so polymorphic-parameter binders
  -- are rejected for now; ground and ∀-carrier-quantified hypotheses
  -- (whose binders are all pattern binders) work via the same
  -- telescope machinery as named rules.
  processHyp : St → Term → TC (List Term × St)
  processHyp st h = do
    ty ← inferType h
    (body , tel) ← stripAndReduce 100 ty
    let flags = classify tel
        p     = countLeading flags
    case anyB id flags of λ where
      true  → error1 ("simp!: polymorphic hypotheses are unsupported (use a monomorphic copy): " <+> show h)
      false → do
        (r , st₁) ← processRuleMono [] (hTerm h) [] tel body st
        return (r ∷ [] , st₁)

  processHyps : St → List Term → TC (List Term × St)
  processHyps st []       = return ([] , st)
  processHyps st (h ∷ hs) = do
    (rs₁ , st₁) ← processHyp st h
    (rs₂ , st₂) ← processHyps st₁ hs
    return (rs₁ ++ rs₂ , st₂)

  ----------------------------------------------------------------
  -- Extensible dictionaries: read rule names off `Simp D` instances.
  ----------------------------------------------------------------

  extractDictName : Term → TC Name
  extractDictName inst = do
    t ← normalise (def (quote Simp.ruleName) (hArg unknown ∷ vArg inst ∷ []))
    unquoteTC t

  getDictNames : Term → TC (List Name)
  getDictNames dictTy = do
    insts ← findInstances (def (quote Simp) (vArg dictTy ∷ []))
    sequence (map extractDictName insts)

  ----------------------------------------------------------------
  -- Deconstruct the QUOTED list literal a `simpH!` caller writes as
  -- the (Term-typed) second argument, e.g. `h₁ ∷ h₂ ∷ []`.  The cons
  -- constructor may carry hidden level/type args before the two
  -- visible ones; we match on visibility and take the visible args.
  ----------------------------------------------------------------

  -- Fueled (the recursion descends `filterVisible` output, which Agda
  -- does not see as structural).
  unquoteHypList : ℕ → Term → TC (List Term)
  unquoteHypList 0        _ = error1 "simpH!: hypothesis list too long"
  unquoteHypList (suc fl) (con c args) =
    if c == quote List._∷_
      then (case filterVisible args of λ where
        (h ∷ tl ∷ []) → do
          rest ← unquoteHypList fl tl
          return (h ∷ rest)
        _ → error1 "simpH!: malformed hypothesis list (cons)")
      else if c == quote List.[]
        then return []
        else error1 "simpH!: hypothesis argument is not a list literal"
  unquoteHypList (suc fl) _ =
    error1 "simpH!: hypothesis argument is not a list literal"

  -- The hypothesis argument of `simpH!` may be a single term, a
  -- right-nested pair (h₁ , h₂ , …), or a list literal.  Macro
  -- Term-arguments are elaborated like `quoteTerm`, so a LIST literal
  -- forces one common element type — hypotheses with different
  -- statements (the common case) must come as a pair, whose components
  -- elaborate independently.
  unquoteHyps : ℕ → Term → TC (List Term)
  unquoteHyps 0 _ = error1 "simpH!: hypothesis tuple too deep"
  unquoteHyps (suc fl) t@(con c args) =
    if c == quote _,_
      then (case filterVisible args of λ where
        (a ∷ b ∷ []) → do
          rest ← unquoteHyps fl b
          return (a ∷ rest)
        _ → error1 "simpH!: malformed hypothesis tuple")
      else if (c == quote List._∷_) ∨ (c == quote List.[])
        then unquoteHypList (suc fl) t
        else return (t ∷ [])
  unquoteHyps (suc fl) t = return (t ∷ [])

  ----------------------------------------------------------------
  -- Mixed universe levels (item 8).  The engine is level-uniform per
  -- goal (`Pointed ℓ`), so when a goal mixes sorts at different levels
  -- (e.g. `List A : Set a` and `ℕ : Set₀`) we `Lift` every lower sort
  -- to the join `ℓmax` and wrap that sort's op positions with
  -- `lift`/`lower`.  Definitional collapse survives because
  -- `lower (lift x)` reduces, so `evalAt` still reduces to the goal.
  ----------------------------------------------------------------

  -- The level term of a sort type `ty` (a goal-context Term).  `Set₀`
  -- normalises to `agda-sort (lit 0)`; `Set a` to `agda-sort (set a)`.
  levelOf : Term → TC Term
  levelOf ty = do
    s ← inferType ty >>= normalise
    case s of λ where
      (sort (set l)) → return l
      (sort (lit n)) → return (levelLit n)
      _              → return (def (quote zeroˡ) [])
    where
      -- `lit n` means Setₙ, whose level is `suc^n zero`.
      levelLit : ℕ → Term
      levelLit zero    = def (quote zeroˡ) []
      levelLit (suc n) = def (quote sucˡ) (vArg (levelLit n) ∷ [])

  -- α-dedup a list of level terms.
  dedupα : List Term → List Term
  dedupα []       = []
  dedupα (t ∷ ts) = go t (dedupα ts)
    where
      go : Term → List Term → List Term
      go x []       = x ∷ []
      go x (y ∷ ys) = if x =α= y then y ∷ ys else y ∷ go x ys

  -- ℓ₁ ⊔ ℓ₂ ⊔ … (right fold) over a non-empty distinct level list.
  quoteLevelMax : List Term → Term
  quoteLevelMax []       = def (quote zeroˡ) []
  quoteLevelMax (l ∷ []) = l
  quoteLevelMax (l ∷ ls) =
    def (quote _⊔ˡ_) (vArg l ∷ vArg (quoteLevelMax ls) ∷ [])

  -- `Lift ℓmax T`, witness `lift w`, value `lower v`, result `lift v`.
  liftTy : Term → Term → Term
  liftTy ℓmax T = def (quote Lift) (vArg ℓmax ∷ vArg T ∷ [])

  liftTm : Term → Term
  liftTm w = con (quote lift) (vArg w ∷ [])

  lowerTm : Term → Term
  lowerTm v = def (quote lower) (vArg v ∷ [])

  ----------------------------------------------------------------
  -- Emission.
  ----------------------------------------------------------------

  quoteSorts : List (Term × Maybe Term) → TC Term
  quoteSorts [] = return (con (quote List.[]) [])
  quoteSorts ((ty , just w) ∷ rest) = do
    r ← quoteSorts rest
    return (con (quote List._∷_) (vArg (quotePair ty w) ∷ vArg r ∷ []))
  quoteSorts ((ty , nothing) ∷ _) =
    error1 ("simp!: no witness available for sort" <+> show ty
            <+> "(a rule mentions a type that never occurs in the goal)")

  -- Indexed (sort i, isLifted flag) — does sort index s need lifting?
  liftedAt : List Bool → ℕ → Bool
  liftedAt []       _       = false
  liftedAt (b ∷ _)  zero    = b
  liftedAt (_ ∷ bs) (suc i) = liftedAt bs i

  -- Build the `List (Pointed ℓmax)` with lifted lower sorts.
  quoteSortsLifted : Term → List Bool → List (Term × Maybe Term) → TC Term
  quoteSortsLifted _    _        [] = return (con (quote List.[]) [])
  quoteSortsLifted ℓmax (b ∷ bs) ((ty , just w) ∷ rest) = do
    r ← quoteSortsLifted ℓmax bs rest
    let ty′ = if b then liftTy ℓmax ty else ty
        w′  = if b then liftTm w        else w
    return (con (quote List._∷_) (vArg (quotePair ty′ w′) ∷ vArg r ∷ []))
  quoteSortsLifted _ _ ((ty , nothing) ∷ _) =
    error1 ("simp!: no witness available for sort" <+> show ty
            <+> "(a rule mentions a type that never occurs in the goal)")
  quoteSortsLifted _ [] (_ ∷ _) =
    error1 "simp!: internal error: level table shorter than sort table"

  -- Membership test on a list of de Bruijn indices.
  memℕ : ℕ → List ℕ → Bool
  memℕ x []       = false
  memℕ x (y ∷ ys) = Data.Nat._≡ᵇ_ x y ∨ memℕ x ys

  -- Replace every value reference `var v []` (with v ∈ `vs`, adjusted for
  -- binder depth) by `lower (var v [])`.  Used to insert `lower` at the
  -- uses of lifted-sort argument variables inside an op implementation.
  mutual
    lowerVars : List ℕ → Term → Term
    lowerVars vs (var v []) =
      if memℕ v vs then lowerTm (var v []) else var v []
    lowerVars vs (var v as)  = var v (lowerVarsArgs vs as)
    lowerVars vs (def f as)  = def f (lowerVarsArgs vs as)
    lowerVars vs (con c as)  = con c (lowerVarsArgs vs as)
    lowerVars vs (lam vis (abs x b)) = lam vis (abs x (lowerVars (map suc vs) b))
    lowerVars vs t           = t

    lowerVarsArgs : List ℕ → Args Term → Args Term
    lowerVarsArgs vs []             = []
    lowerVarsArgs vs (arg i t ∷ as) = arg i (lowerVars vs t) ∷ lowerVarsArgs vs as

  -- Wrap an op implementation `λ x₁ … xₙ → body` (the shape `mkImpl`
  -- guarantees) so arguments of a lifted sort are `lower`ed at their use
  -- sites and a lifted-result body is `lift`ed.  Argument k (sort as[k])
  -- is referenced as `var (n∸1∸k)` directly under the n lambdas.
  wrapImpl : List Bool → List ℕ → ℕ → Term → Term
  wrapImpl flags as r impl = peel n impl
    where
      n : ℕ
      n = length as
      -- the de Bruijn indices (under the n lambdas) of lifted args
      liftedVars : List ℕ
      liftedVars = go 0 as
        where
          go : ℕ → List ℕ → List ℕ
          go _ []        = []
          go k (s ∷ ss)  =
            if liftedAt flags s then (n ∸ 1 ∸ k) ∷ go (suc k) ss
                                else go (suc k) ss
      peel : ℕ → Term → Term
      peel zero    body =
        let body′ = lowerVars liftedVars body
        in if liftedAt flags r then liftTm body′ else body′
      peel (suc m) (lam vis (abs x b)) = lam vis (abs x (peel m b))
      peel (suc m) t                   = t   -- shouldn't happen

  quoteOps : List (Term × List ℕ × ℕ) → Term
  quoteOps ops = quoteList (map
    (λ p → quotePair
             (quotePair (quoteList (map `ℕ (proj₁ (proj₂ p))))
                        (`ℕ (proj₂ (proj₂ p))))
             (proj₁ p))
    ops)

  -- Rule soundness witnesses are `λ τ → lemma … (τ s i) …`; a lifted
  -- sort makes `τ s i : Lift ℓmax T`, but the lemma expects `T`, so wrap
  -- those applications with `lower`.  Traverse the sound lambda tracking
  -- τ's de Bruijn depth `d`; rewrite `var d (lit s ∷ lit i ∷ [])` whose
  -- sort s is lifted into `lower (var d …)`.
  mutual
    wrapSound : List Bool → ℕ → Term → Term
    wrapSound flags d t@(var k (arg _ (lit (nat s)) ∷ arg _ (lit (nat i)) ∷ [])) =
      if (Data.Nat._≡ᵇ_ k d) ∧ liftedAt flags s
        then lowerTm t
        else t
    wrapSound flags d (var k as)           = var k (wrapSoundArgs flags d as)
    wrapSound flags d (def f as)           = def f (wrapSoundArgs flags d as)
    wrapSound flags d (con c as)           = con c (wrapSoundArgs flags d as)
    wrapSound flags d (lam v (abs x b))    = lam v (abs x (wrapSound flags (suc d) b))
    wrapSound flags d t                    = t

    wrapSoundArgs : List Bool → ℕ → Args Term → Args Term
    wrapSoundArgs flags d []             = []
    wrapSoundArgs flags d (arg i t ∷ as) = arg i (wrapSound flags d t) ∷ wrapSoundArgs flags d as

  -- Read the sort index off a quoted `RC.Expr` term (`op o s …` / `var i s`).
  exprSortOf : Term → Maybe ℕ
  exprSortOf (con c (_ ∷ arg _ (lit (nat s)) ∷ _)) =
    if (c == quote RC.Expr.op) ∨ (c == quote RC.Expr.var) then just s else nothing
  exprSortOf _ = nothing

  -- `λ τ → e`  ↦  `λ τ → cong lift e`
  congLiftLam : Term → Term
  congLiftLam (lam v (abs x e)) =
    lam v (abs x (def (quote cong) (vArg (con (quote lift) []) ∷ vArg e ∷ [])))
  congLiftLam e = e

  -- Rewrite the soundness lambda of a quoted `mkRule` term (it is the
  -- last visible arg; the lhs Expr is the first visible `con`-Expr arg,
  -- whose sort decides the `cong lift` on the result).  Robust to any
  -- leading (reconstructed) module-parameter args.
  wrapRule : List Bool → Term → Term
  wrapRule flags (con c as) = con c (go true as)
    where
      -- whether the rule sort is lifted (read from the first Expr arg)
      ruleLifted : Bool
      ruleLifted = goFind as
        where
          goFind : Args Term → Bool
          goFind []             = false
          goFind (arg _ t ∷ rest) = case exprSortOf t of λ where
            (just s) → liftedAt flags s
            nothing  → goFind rest
      -- rewrite each visible λ-arg (the sound lambda); `fstExpr` guards
      -- so only the trailing lambda is treated as the witness.
      go : Bool → Args Term → Args Term
      go _ []                                = []
      go first (arg i@(arg-info visible _) t ∷ rest) =
        case t of λ where
          (lam v (abs x b)) →
            -- inside the body of `λ τ`, τ is `var 0`; start matching at d=0
            let lowered = lam v (abs x (wrapSound flags 0 b))
                body    = if ruleLifted then congLiftLam lowered else lowered
            in arg i body ∷ go false rest
          _ → arg i t ∷ go false rest
      go first (a ∷ rest) = a ∷ go first rest
  wrapRule _ t = t

  -- Like `quoteOps`, but `lift`/`lower`-wraps each impl per `flags`
  -- (sort index → isLifted).
  quoteOpsLifted : List Bool → List (Term × List ℕ × ℕ) → Term
  quoteOpsLifted flags ops = quoteList (map
    (λ p → let as = proj₁ (proj₂ p)
               r  = proj₂ (proj₂ p)
           in quotePair
                (quotePair (quoteList (map `ℕ as)) (`ℕ r))
                (wrapImpl flags as r (proj₁ p)))
    ops)

  ----------------------------------------------------------------
  -- The tactic: recurse under binders, then reify and emit.
  ----------------------------------------------------------------

  -- On the failure path only: build the meta-level term that evaluates
  -- one stuck side to its normal form (same argument spelling as the
  -- happy-path `solveApp`: module params Ts and ops first), normalise
  -- it (bounded — the result is goal-sized), and `show` it.  The happy
  -- path never reaches here, so it pays nothing.
  showStuck : Term → Term → ℕ → Term → Term → TC String
  showStuck TsT opsT g rulesT eE = do
    let nfApp = def (quote RC.Eval.normalForm)
                  ( vArg TsT ∷ vArg opsT
                  ∷ vArg (`ℕ 100) ∷ vArg rulesT ∷ vArg eE ∷ [] )
    -- Read back the normal-form Expr first and refuse to evaluate huge
    -- ones: rendering a deep normal form through the (non-sharing)
    -- evaluator can take minutes, and a large form almost always means
    -- a diverging (e.g. expanding) rule set anyway.
    nfT ← normalise nfApp
    nfE ← unquoteTC {A = RC.Expr} nfT
    if 40 <ᵇ RC.sizeExpr nfE
      then return ("(normal form with" <+> show (RC.sizeExpr nfE)
                   <+> "nodes omitted — diverging rule set?)")
      else (do
        let valApp = def (quote RC.Eval.evalAt)
                  ( vArg TsT ∷ vArg opsT
                  ∷ vArg (`ℕ g)
                  ∷ vArg (def (quote RC.Eval.ρ₀) (vArg TsT ∷ vArg opsT ∷ []))
                  ∷ vArg nfApp ∷ [] )
        t ← normalise valApp
        return (show t))

  ----------------------------------------------------------------
  -- Relation goals (`simpRel!`).
  ----------------------------------------------------------------

  -- (relN, prefix-args, lhs, rhs): the last two VISIBLE args of a
  -- def-headed relation goal are lhs/rhs, the rest is the prefix.
  getRelSides : Term → Maybe (Name × Args Term × Term × Term)
  getRelSides (def relN args) =
    case reverse args of λ where
      (arg (arg-info visible _) rhs ∷ arg (arg-info visible _) lhs ∷ rest) →
        just (relN , reverse rest , lhs , rhs)
      _ → nothing
  getRelSides _ = nothing

  -- Build the meta-level `normalForm` application for an Expr term and
  -- normalise it (plain Expr data — bounded).  Returns the normalised
  -- Expr-as-Term, the engine's normal form for `eE`.  Same module-
  -- argument spelling as solveApp (Ts, ops first).
  computeNF : Term → Term → Term → Term → TC Term
  computeNF TsT opsT rulesT eE =
    normalise (def (quote RC.Eval.normalForm)
                  ( vArg TsT ∷ vArg opsT
                  ∷ vArg (`ℕ 100) ∷ vArg rulesT ∷ vArg eE ∷ [] ))

  -- p_i : evalAt g ρ₀ e ≡ evalAt g ρ₀ (normalForm 100 rs e), whose type
  -- reduces (definitional collapse) to the actual goal-side term ≡ nf.
  mkSimplifyEq : Term → Term → ℕ → Term → Term → Term
  mkSimplifyEq TsT opsT g rulesT eE =
    def (quote RC.Eval.simplifyEq)
      ( vArg TsT ∷ vArg opsT
      ∷ vArg (`ℕ g) ∷ vArg (`ℕ 100) ∷ vArg rulesT ∷ vArg eE ∷ [] )

  -- subst-based relation proof (mirrors old buildRelProof).  prefix/rhs
  -- are goal-context terms; shift them under the predicate λ.  `changedL`
  -- / `changedR` say whether each side actually simplified (skip the
  -- subst if not).  core : lhsNF ~ rhsNF (a goal-context term).
  buildRelProof : Name → Args Term → Term → Term → Term → Term → Term
                → Bool → Bool → Term
  buildRelProof relN prefix p1 p2 core lhsNFt rhs changedL changedR =
    let prefixS = map-Args (mapVars suc) prefix
        predL   = lam visible (abs "◆"
                    (def relN (prefixS ++ vArg (var 0 []) ∷ vArg (mapVars suc rhs) ∷ [])))
        predR   = lam visible (abs "◆"
                    (def relN (prefixS ++ vArg (mapVars suc lhsNFt) ∷ vArg (var 0 []) ∷ [])))
        sym' p  = def (quote sym) (vArg p ∷ [])
        subst' P eq t = def (quote subst) (vArg P ∷ vArg eq ∷ vArg t ∷ [])
    in
    if not changedL
    then (if not changedR then core else subst' predR (sym' p2) core)
    else (if not changedR then subst' predL (sym' p1) core
                          else subst' predL (sym' p1) (subst' predR (sym' p2) core))

  -- Read bindings for all d binders, outermost-first, into args with the
  -- given ArgInfos.  Binder k ↦ rule index d∸1∸k.
  collectAllArgs : ℕ → List ArgInfo → List (ℕ × Term) → Maybe (Args Term)
  collectAllArgs d infos σ = go 0 infos
    where
      go : ℕ → List ArgInfo → Maybe (Args Term)
      go k []         = just []
      go k (i ∷ is) = case lookupB σ (d ∸ 1 ∸ k) of λ where
        (just t) → (case go (suc k) is of λ where
          (just as) → just (arg i t ∷ as)
          nothing   → nothing)
        nothing  → nothing

  -- One ~-rule, all telescope binders treated as wildcards.  Returns
  -- (instantiated-proof : cur ~ rhsInst , rhsInst) on a full match.
  data RelRule : Set where
    mkRelRule : (relN : Name) (ruleN : Name) (d : ℕ)
              → (infos : List ArgInfo) (lhsB rhsB : Term) → RelRule

  -- getType + stripAndReduce + parse a ~-rule into a RelRule.
  loadRelRule : Name → TC RelRule
  loadRelRule n = do
    ty ← getType n
    (body , tel) ← stripAndReduce 100 ty
    (just (relN , _ , lhsB , rhsB)) ← return (getRelSides body)
      where nothing → error1 ("simpRel!: ~-rule is not a binary relation: " <+> show n)
    return (mkRelRule relN n (length tel) (map proj₁ tel) lhsB rhsB)

  -- Try each ~-rule at the root of `cur`; on the first match return the
  -- instantiated rhs term and the proof `def ruleN args : cur ~ rhsInst`.
  tryRelStep : List RelRule → Term → Maybe (Term × Term)
  tryRelStep []                                       cur = nothing
  tryRelStep (mkRelRule relN ruleN d infos lhsB rhsB ∷ rs) cur =
    case matchT d lhsB cur [] of λ where
      (just σ) → case collectAllArgs d infos σ of λ where
        (just args) → just (substRuleVars d σ rhsB , def ruleN args)
        nothing     → tryRelStep rs cur
      nothing  → tryRelStep rs cur

  -- Compute each sort's level term, then decide: if all sorts share one
  -- level → `nothing` (fast path).  Otherwise `just (ℓmax , flags)` where
  -- `flags i` says sort i must be `Lift`ed to the join `ℓmax`.
  buildLiftFlags : List (Term × Maybe Term) → TC (Maybe (Term × List Bool))
  buildLiftFlags sorts = do
    levels ← traverse (λ p → levelOf (proj₁ p)) sorts
    let distinct = dedupα levels
    case distinct of λ where
      []       → return nothing
      (_ ∷ []) → return nothing
      _        → do
        -- Normalise the join: `0 ⊔ a` collapses to `a`, so a sort whose
        -- level already equals ℓmax is NOT lifted (avoids lifting the
        -- top-level sort to a syntactically-different-but-equal level).
        ℓmax ← normalise (quoteLevelMax distinct)
        levels′ ← traverse normalise levels
        let flags = map (λ l → not (l =α= ℓmax)) levels′
        return (just (ℓmax , flags))

  simpRGoal : ℕ → ℕ → List Name → List Term → ITactic
  simpRGoal 0          _     _     _    = error1 "simp!: goal has too many binders"
  simpRGoal (suc fuel) depth names hyps = do
    hole ← goalHole
    ty   ← inferType hole >>= reduce
    case ty of λ where
      (pi argTy@(arg (arg-info v _) _) (abs x bodyTy)) → do
        hole′ ← extendContext (x , argTy) (newMeta bodyTy)
        unifyStrict (hole , ty) (lam v (abs x hole′))
        extendContext (x , argTy)
          (runWithHole hole′ (simpRGoal fuel (suc depth) names hyps))
      (def (quote _≡_) (hArg _ ∷ hArg _ ∷ vArg lhs₀ ∷ vArg rhs₀ ∷ [])) → do
        -- Shift the call-site hypothesis terms past the binders we
        -- entered (their indices are relative to the call site, which
        -- excludes the stripped ∀-binders).
        let hyps′ = map (mapVars (_+ depth)) hyps
            lhs   = canonNums lhs₀
            rhs   = canonNums rhs₀
        cands ← enrichCandidates names (subApps lhs ++ subApps rhs)
        (ruleTs , st₀) ← processRules cands names (mkSt [] [] nothing)
        (hypTs  , st₀′) ← processHyps st₀ hyps′
        let allRuleTs = ruleTs ++ hypTs
        (lhsE , st₁) ← conv 0 [] st₀′ lhs
        (rhsE , st₂) ← conv 0 [] st₁ rhs
        lT  ← quoteNorm lhsE
        rT  ← quoteNorm rhsE
        -- Mixed-level handling: build the (possibly Lift-ed) sort table
        -- and matching impls.  `gLifted` says whether the goal sort g was
        -- lifted (then the engine proves `lift lhs ≡ lift rhs` and we
        -- close the real goal with `cong lower`).
        liftInfo ← buildLiftFlags (St.sorts st₂)
        let g = RC.sortOf lhsE
        TsT ← case liftInfo of λ where
          nothing               → quoteSorts (St.sorts st₂)
          (just (ℓmax , flags)) → quoteSortsLifted ℓmax flags (St.sorts st₂)
        let opsT = case liftInfo of λ where
              nothing               → quoteOps (St.ops st₂)
              (just (_ , flags))    → quoteOpsLifted flags (St.ops st₂)
            gLifted = case liftInfo of λ where
              nothing            → false
              (just (_ , flags)) → liftedAt flags g
            rulesT   = case liftInfo of λ where
              nothing            → quoteList allRuleTs
              (just (_ , flags)) → quoteList (map (wrapRule flags) allRuleTs)
            solveApp = def (quote RC.Eval.solveAt)
              ( vArg TsT ∷ vArg opsT
              ∷ vArg (`ℕ g) ∷ vArg (`ℕ 100)
              ∷ vArg rulesT ∷ vArg lT ∷ vArg rT ∷ [] )
            mkProof : Term → Term
            mkProof p = if gLifted
                        then def (quote cong) (vArg (def (quote lower) []) ∷ vArg p ∷ [])
                        else p
        -- Pre-run the solver to WHNF at the meta level for a decent
        -- error (via is-just, so the proof term is never normalised).
        nf ← normalise (def (quote Data.Maybe.is-just) (vArg solveApp ∷ []))
        case nf of λ where
          (con c _) → if c == quote Data.Bool.false
            -- Last resort: rewrite each side to its engine normal form
            -- and close the remaining gap definitionally (refl in the
            -- middle).  Handles goals that need rewriting AND a
            -- definitional step (e.g. `(x + 0) + (2 + 3) ≡ x + 5`) and
            -- purely definitional goals (`2 + 3 ≡ 5`).  Costs nothing
            -- on the happy path.
            then (let eqSide : Term → Term
                      eqSide eT = def (quote RC.Eval.simplifyEq)
                        ( vArg TsT ∷ vArg opsT ∷ vArg (`ℕ g) ∷ vArg (`ℕ 100)
                        ∷ vArg rulesT ∷ vArg eT ∷ [] )
                      composed = def (quote trans)
                        ( vArg (eqSide lT)
                        ∷ vArg (def (quote trans)
                            ( vArg (con (quote refl) [])
                            ∷ vArg (def (quote sym) (vArg (eqSide rT) ∷ [])) ∷ []))
                        ∷ [] )
                  in catch (unifyWithGoal (mkProof composed)) λ _ → do
              lNF ← showStuck TsT opsT g rulesT lT
              rNF ← showStuck TsT opsT g rulesT rT
              error1 ("simp!: simplification failed to close the goal;\n  the two sides reached the normal forms\n    "
                      <+> lNF <+> "\n  and\n    " <+> rNF))
            else unifyWithGoal (mkProof (def (quote RC.from-just!) (vArg solveApp ∷ [])))
          _ → unifyWithGoal (mkProof (def (quote RC.from-just!) (vArg solveApp ∷ [])))
      _ → error1 "simp!: goal is not a propositional equality"

  ----------------------------------------------------------------
  -- The relation tactic: recurse under binders, then (a) ≡-normalise
  -- both sides with the verified engine and (b) chain top-level
  -- ~-rules, closing with the relation's reflexivity.
  ----------------------------------------------------------------

  -- Option B: chain ~-rules from `cur` towards `target` (both already
  -- ≡-normalised goal-context Terms).  Returns the trans-chain proof
  -- `cur ~ final` and `final` (= `target` on success).  Minimal-args
  -- emission: relTrans/relRefl applied with no prefix/endpoints, letting
  -- final goal-unification solve the implicits.  After each ~-step the
  -- new current term is `normalise`d (the rule's rhs is unreduced — e.g.
  -- `1 + n` — but `target` is the engine's normal form, so they must be
  -- brought to a common form before the α-equality test).
  relChain : RelInfo → List RelRule → ℕ → Term → Term → TC (Maybe (Term × Term))
  relChain ri rrs n cur target =
    if cur =α= target
      then return (just (def (RelInfo.relRefl ri) [] , cur))
      else (case n of λ where
        0       → return nothing
        (suc m) → case tryRelStep rrs cur of λ where
          (just (next , step)) → do
            next′ ← normalise next
            r ← relChain ri rrs m next′ target
            case r of λ where
              (just (rest , final)) →
                return (just (def (RelInfo.relTrans ri) (vArg step ∷ vArg rest ∷ []) , final))
              nothing → return nothing
          nothing → return nothing)

  simpRelGoal : ℕ → ℕ → RelInfo → List Name → List Name → ITactic
  simpRelGoal 0          _     _  _       _        = error1 "simpRel!: goal has too many binders"
  simpRelGoal (suc fuel) depth ri eqNames relNames = do
    hole ← goalHole
    ty   ← inferType hole >>= reduce
    case ty of λ where
      (pi argTy@(arg (arg-info v _) _) (abs x bodyTy)) → do
        hole′ ← extendContext (x , argTy) (newMeta bodyTy)
        unifyStrict (hole , ty) (lam v (abs x hole′))
        extendContext (x , argTy)
          (runWithHole hole′ (simpRelGoal fuel (suc depth) ri eqNames relNames))
      _ → do
        (just (relN , prefix , lhs₀ , rhs₀)) ← return (getRelSides ty)
          where nothing → error1 "simpRel!: goal is not a binary relation"
        let lhs = canonNums lhs₀
            rhs = canonNums rhs₀
            -- Bundle parameter (e.g. an abstract Monoid): the relation's
            -- last visible prefix arg.  Bundle operations are dropped
            -- during reification so the bundle never becomes a sort.
            bM  = lastVisibleArg prefix
        -- (a) Build the engine tables + ≡-rules over BOTH sides.
        cands ← enrichCandidates eqNames (subApps lhs ++ subApps rhs)
        (ruleTs , st₁) ← processRules cands eqNames (mkSt [] [] bM)
        (lhsE , st₂) ← conv 0 [] st₁ lhs
        (rhsE , st₃) ← conv 0 [] st₂ rhs
        -- Mixed universe levels are not supported for relation goals
        -- (the `Lift`/`cong lower` interaction with the subst predicates
        -- is unimplemented); fail cleanly rather than emit a bad term.
        (nothing) ← buildLiftFlags (St.sorts st₃)
          where (just _) → error1 "simpRel!: mixed universe levels are unsupported for relation goals (use monomorphic carrier types)"
        let rulesT = quoteList ruleTs
            g      = RC.sortOf lhsE
        lT  ← quoteNorm lhsE
        rT  ← quoteNorm rhsE
        TsT ← quoteSorts (St.sorts st₃)
        let opsT = quoteOps (St.ops st₃)
        -- Meta-level normal forms (Expr data — bounded normalise).
        lNFt ← computeNF TsT opsT rulesT lT
        rNFt ← computeNF TsT opsT rulesT rT
        -- The actual goal-context normal-form Terms (definitional
        -- collapse: evalAt g ρ₀ nf reduces to the goal side's nf).
        lhsNFterm ← normalise (def (quote RC.Eval.evalAt)
                      ( vArg TsT ∷ vArg opsT ∷ vArg (`ℕ g)
                      ∷ vArg (def (quote RC.Eval.ρ₀) (vArg TsT ∷ vArg opsT ∷ []))
                      ∷ vArg lNFt ∷ [] ))
        rhsNFterm ← normalise (def (quote RC.Eval.evalAt)
                      ( vArg TsT ∷ vArg opsT ∷ vArg (`ℕ g)
                      ∷ vArg (def (quote RC.Eval.ρ₀) (vArg TsT ∷ vArg opsT ∷ []))
                      ∷ vArg rNFt ∷ [] ))
        let changedL = not (lT =α= lNFt)
            changedR = not (rT =α= rNFt)
            p1 = mkSimplifyEq TsT opsT g rulesT lT
            p2 = mkSimplifyEq TsT opsT g rulesT rT
        -- (b) Chain ~-rules from lhsNFterm towards rhsNFterm.
        relRules ← traverse loadRelRule relNames
        (just (core , _)) ← relChain ri relRules 100 lhsNFterm rhsNFterm
          where nothing → error1
                  ("simpRel!: could not connect the normal forms;\n  lhs-nf = "
                   <+> show lhsNFterm <+> "\n  rhs-nf = " <+> show rhsNFterm)
        unifyWithGoal
          (buildRelProof relN prefix p1 p2 core lhsNFterm rhs changedL changedR)

simpRTactic : List Name → ITactic
simpRTactic names =
  -- Reconstructed syntax: without this, constructor parameters (e.g.
  -- the level/type arguments of List.[]) appear as `unknown` in
  -- reflected terms, breaking sort inference and table keys.
  local (λ env → record env { reconstruction = true }) (simpRGoal 100 0 names [])

-- Like `simpRTactic` but also takes local-hypothesis terms (in the
-- call-site context) to use as ground/∀-carrier rules.
simpHTactic : List Name → List Term → ITactic
simpHTactic names hyps =
  local (λ env → record env { reconstruction = true }) (simpRGoal 100 0 names hyps)

-- Relation goals: ≡-rules, ~-rules, the relation's trans/refl.
simpRelTactic : List Name → List Name → RelInfo → ITactic
simpRelTactic eqNames relNames ri =
  local (λ env → record env { reconstruction = true })
        (simpRelGoal 100 0 ri eqNames relNames)

macro
  simp! : List Name → Tactic
  simp! names = initTacOpts (simpRTactic names) defaultTCOptions

  -- Resolve the rule names from the `Simp D` instances, then run the
  -- ordinary machinery.
  simpD! : (D : Set) → Tactic
  simpD! D = initTacOpts (do
    dictTy ← quoteTC D
    names  ← getDictNames dictTy
    simpRTactic names) defaultTCOptions

  -- Like `simp!` but also takes local hypotheses.  The first argument
  -- is an ordinary (elaborated) `List Name`; the second is written as
  -- a list literal of hypotheses but, being `Term`-typed, arrives as
  -- the QUOTED call-site expression, which we deconstruct here.
  simpH! : List Name → Term → Tactic
  simpH! names hypsExpr = initTacOpts (do
    hyps ← unquoteHyps 100 hypsExpr
    simpHTactic names hyps) defaultTCOptions

  -- Prove `lhs ~ rhs` for a binary relation `~` by (a) ≡-normalising
  -- both sides with the verified engine and transporting along ~ with
  -- subst, then (b) chaining top-level ~-rules with the relation's
  -- transitivity, closing with reflexivity.  Args: ≡-rules, ~-rules,
  -- and the relation's trans/refl info.
  simpRel! : List Name → List Name → RelInfo → Tactic
  simpRel! eqNames relNames ri =
    initTacOpts (simpRelTactic eqNames relNames ri) defaultTCOptions

  -- Like `simpRel!`, but the ≡-rule and ~-rule name lists are resolved
  -- from `Simp` instance dictionaries `EqD` / `RelD`.
  simpRelD! : (EqD RelD : Set) → RelInfo → Tactic
  simpRelD! EqD RelD ri = initTacOpts (do
    eqTy     ← quoteTC EqD
    relTy    ← quoteTC RelD
    eqNames  ← getDictNames eqTy
    relNames ← getDictNames relTy
    simpRelTactic eqNames relNames ri) defaultTCOptions

-- ** Tests

private
  open import Tactic.Defaults
  open import Data.List.Properties using (++-identityʳ; ++-identityˡ; length-map)

  -- *** ℕ tests (mirroring Tactic.Simp)

  t₁ : ∀ {x y : ℕ} → (x + 0) + y ≡ x + (0 + y)
  t₁ = simp! (quote +-assoc ∷ quote +-identityˡ ∷ quote +-identityʳ ∷ [])

  t₂ : ∀ {x : ℕ} → x + 0 ≡ x
  t₂ = simp! (quote +-identityʳ ∷ [])

  t₃ : ∀ {x y : ℕ} → (x + 0) + (0 + y) ≡ x + y
  t₃ = simp! (quote +-identityˡ ∷ quote +-identityʳ ∷ [])

  -- Multiple applications of the same rule
  t₄ : ∀ {x : ℕ} → x + 0 + 0 ≡ x
  t₄ = simp! (quote +-identityʳ ∷ [])

  -- Simplification in a non-leftmost argument
  t₅ : ∀ {x y : ℕ} → x + (y + 0) ≡ x + y
  t₅ = simp! (quote +-identityʳ ∷ [])

  -- Only the RHS needs simplification
  t₆ : ∀ {x : ℕ} → x ≡ x + 0
  t₆ = simp! (quote +-identityʳ ∷ [])

  -- Different operator
  t₇ : ∀ {x : ℕ} → x * 1 ≡ x
  t₇ = simp! (quote *-identityʳ ∷ [])

  -- Each argument simplified by a different rule
  t₈ : ∀ {x y : ℕ} → (x * 1) + (0 + y) ≡ x + y
  t₈ = simp! (quote *-identityʳ ∷ quote +-identityˡ ∷ [])

  -- Top-level rule exposes a new redex in the result
  t₉ : ∀ {x : ℕ} → (x + 0) * 1 ≡ x
  t₉ = simp! (quote *-identityʳ ∷ quote +-identityʳ ∷ [])

  -- Three-rule chain
  t₁₀ : ∀ {x y : ℕ} → (x + y) * 0 + x * 1 ≡ x
  t₁₀ = simp! (quote *-zeroʳ ∷ quote *-identityʳ ∷ quote +-identityˡ ∷ [])

  -- Trivial goal, empty rule set
  t₁₁ : ∀ {x : ℕ} → x ≡ x
  t₁₁ = simp! []

  -- Two levels deep inside an argument
  t₁₂ : ∀ {x y z : ℕ} → (x + 0) + ((y + 0) + z) ≡ x + (y + z)
  t₁₂ = simp! (quote +-identityʳ ∷ [])

  -- Left-associativity flattening in two top-level steps
  t₁₃ : ∀ {a b c d : ℕ} → ((a + b) + c) + d ≡ a + (b + (c + d))
  t₁₃ = simp! (quote +-assoc ∷ [])

  -- Rewriting under an explicit ∀ binder
  tb₁ : ∀ (n : ℕ) → n + 0 ≡ n
  tb₁ = simp! (quote +-identityʳ ∷ [])

  -- Rewriting under an implicit ∀ binder
  tb₂ : ∀ {n : ℕ} → n + 0 ≡ n
  tb₂ = simp! (quote +-identityʳ ∷ [])

  -- Mixed binders
  tb₃ : ∀ (m : ℕ) {n : ℕ} → (m + 0) + (0 + n) ≡ m + n
  tb₃ = simp! (quote +-identityˡ ∷ quote +-identityʳ ∷ [])

  -- *** Multi-sorted tests

  -- Monomorphic wrappers (also exercised: Phase C handles the raw
  -- polymorphic lemmas directly, see below).
  catIdʳ : (xs : List ℕ) → xs ++ [] ≡ xs
  catIdʳ = ++-identityʳ

  lenMapSuc : (l : List ℕ) → length (map suc l) ≡ length l
  lenMapSuc = length-map suc

  -- Lists: ops with hidden (level/type) arguments, atom `[]`
  tl₁ : ∀ (xs ys : List ℕ) → (xs ++ []) ++ ys ≡ xs ++ ys
  tl₁ = simp! (quote catIdʳ ∷ [])

  -- Two sorts (List ℕ, ℕ) plus a function-typed atom (`suc`)
  tm₁ : ∀ (l : List ℕ) → length (map suc l) ≡ length l
  tm₁ = simp! (quote lenMapSuc ∷ [])

  -- Chaining across sorts: rewrite inside List ℕ, then ℕ
  tm₂ : ∀ (l : List ℕ) → length (map suc (l ++ [])) ≡ length l
  tm₂ = simp! (quote lenMapSuc ∷ quote catIdʳ ∷ [])

  -- Rules at two different sorts in one call
  tm₃ : ∀ (l : List ℕ) → length (map suc l) + 0 ≡ length l
  tm₃ = simp! (quote lenMapSuc ∷ quote +-identityʳ ∷ [])

  -- *** Phase C: polymorphic rules, no wrappers

  -- {a} {A : Set a} instantiated from the goal
  tp₁ : ∀ (xs ys : List ℕ) → (xs ++ []) ++ ys ≡ xs ++ ys
  tp₁ = simp! (quote ++-identityʳ ∷ [])

  -- two polymorphic rules; length-map keeps f as a pattern variable
  -- of function sort after specialisation
  tp₂ : ∀ (l : List ℕ) → length (map suc (l ++ [])) ≡ length l
  tp₂ = simp! (quote length-map ∷ quote ++-identityʳ ∷ [])

  -- module-local rule: the module parameter lifts into the rule type
  -- and is instantiated from the goal (with a context variable)
  module _ {A : Set} where
    localIdʳ : (xs : List A) → xs ++ [] ≡ xs
    localIdʳ = ++-identityʳ

    tp₃ : (xs : List A) → (xs ++ []) ++ xs ≡ xs ++ xs
    tp₃ = simp! (quote localIdʳ ∷ [])

  -- one polymorphic rule instantiated at two element types in one goal
  tp₄ : ∀ (xs : List ℕ) (bs : List Bool) →
        length (xs ++ []) + length (bs ++ []) ≡ length xs + length bs
  tp₄ = simp! (quote ++-identityʳ ∷ [])

  -- *** Task A: extensible dictionaries (simpD!)

  data ArithRules : Set where

  instance
    arith-assoc  : Simp ArithRules
    arith-identᵣ : Simp ArithRules
    arith-identˡ : Simp ArithRules
    arith-assoc  = mkSimp (quote +-assoc)
    arith-identᵣ = mkSimp (quote +-identityʳ)
    arith-identˡ = mkSimp (quote +-identityˡ)

  -- Basic rule from dictionary
  testDict₁ : ∀ {x : ℕ} → x + 0 ≡ x
  testDict₁ = simpD! ArithRules

  -- Multiple rules from dictionary
  testDict₂ : ∀ {x y : ℕ} → (x + 0) + (0 + y) ≡ x + y
  testDict₂ = simpD! ArithRules

  -- Associativity from dictionary
  testDict₃ : ∀ {a b c d : ℕ} → ((a + b) + c) + d ≡ a + (b + (c + d))
  testDict₃ = simpD! ArithRules

  -- *** Task B: local hypotheses as rules (simpH!)

  -- Ground hypothesis: rewrite both x's to 0, then +-identityʳ on the
  -- RHS.  Hypothesis bound in the body, no ∀ stripped after — shift 0.
  th₁ : ∀ {x : ℕ} → (h : x ≡ 0) → x + x ≡ 0 + 0
  th₁ {x} h = simpH! [] (h ∷ [])

  -- Ground hypothesis combined with a named rule.
  th₂ : ∀ {x : ℕ} → (h : x ≡ 0) → x + 0 ≡ 0
  th₂ {x} h = simpH! (quote +-identityʳ ∷ []) (h ∷ [])

  -- ∀-carrier-quantified hypothesis used like a named rule (shift 0).
  th₃ : ∀ {m : ℕ} → (h : ∀ (n : ℕ) → n + 0 ≡ n) → m + 0 ≡ m
  th₃ {m} h = simpH! [] (h ∷ [])

  -- Shift test: a ∀-binder (m) is stripped AFTER the hypothesis h is
  -- bound, so h's de Bruijn index must be shifted by the depth entered.
  th₄ : (h : ∀ (n : ℕ) → n + 0 ≡ n) → ∀ (m : ℕ) → m + 0 ≡ m
  th₄ h = simpH! [] (h ∷ [])

  -- *** Task 1: relation goals (simpRel!)

  -- **** Option C: ≡-normalisation, closed by relRefl (no ~-rules) ****

  -- LHS only: n + 0 → n, then ≤-refl closes n ≤ n
  testRel₁ : ∀ {n : ℕ} → n + 0 ≤ n
  testRel₁ = simpRel! (quote +-identityʳ ∷ []) []
                      (mkRelInfo (quote ≤-trans) (quote ≤-refl))

  -- RHS only normalises (exercises the predR/sym-subst path)
  testRel₂ : ∀ {n : ℕ} → n ≤ n + 0
  testRel₂ = simpRel! (quote +-identityʳ ∷ []) []
                      (mkRelInfo (quote ≤-trans) (quote ≤-refl))

  -- Both sides + two rules
  testRel₃ : ∀ {n m : ℕ} → (n + 0) + (0 + m) ≤ n + m
  testRel₃ = simpRel! (quote +-identityˡ ∷ quote +-identityʳ ∷ []) []
                      (mkRelInfo (quote ≤-trans) (quote ≤-refl))

  -- Under an explicit ∀ binder
  testRel₄ : ∀ (n : ℕ) → n + 0 ≤ n
  testRel₄ = simpRel! (quote +-identityʳ ∷ []) []
                      (mkRelInfo (quote ≤-trans) (quote ≤-refl))

  -- Mixed binders
  testRel₅ : ∀ (m : ℕ) {n : ℕ} → (m + 0) + (0 + n) ≤ m + n
  testRel₅ = simpRel! (quote +-identityˡ ∷ quote +-identityʳ ∷ []) []
                      (mkRelInfo (quote ≤-trans) (quote ≤-refl))

  -- Deep subterm normalisation
  testRel₆ : ∀ {a b c : ℕ} → (a + 0) + ((b + 0) + c) ≤ a + (b + c)
  testRel₆ = simpRel! (quote +-identityʳ ∷ []) []
                      (mkRelInfo (quote ≤-trans) (quote ≤-refl))

  -- **** Option B: top-level ~-rule chaining (n≤1+n) ****

  -- n≤1+n : ∀ n → n ≤ 1 + n  (from Data.Nat.Properties)

  -- ≡-normalise LHS (n + 0 → n), then one ~-step n ≤ 1 + n
  testRelB₁ : ∀ {n : ℕ} → n + 0 ≤ 1 + n
  testRelB₁ = simpRel! (quote +-identityʳ ∷ [])
                       (quote n≤1+n ∷ [])
                       (mkRelInfo (quote ≤-trans) (quote ≤-refl))

  -- Two chained ~-steps: n ≤ 1 + n ≤ 2 + n
  testRelB₃ : ∀ {n : ℕ} → n + 0 ≤ 2 + n
  testRelB₃ = simpRel! (quote +-identityʳ ∷ [])
                       (quote n≤1+n ∷ [])
                       (mkRelInfo (quote ≤-trans) (quote ≤-refl))

  -- Migration (item 13): old testRelB₂-style — the ~-target rhs `1 + (n + 0)`
  -- is itself ≡-normalised by the engine (the rhs side is normalised too),
  -- so the chain connects.  (This was a suspected gap; it works.)
  testRelB₂ : ∀ {n : ℕ} → n + 0 ≤ 1 + (n + 0)
  testRelB₂ = simpRel! (quote +-identityʳ ∷ [])
                       (quote n≤1+n ∷ [])
                       (mkRelInfo (quote ≤-trans) (quote ≤-refl))

  -- Migration (item 13): old testRelB₄-style — three chained ~-steps.
  testRelB₄ : ∀ {n : ℕ} → n + 0 ≤ 3 + n
  testRelB₄ = simpRel! (quote +-identityʳ ∷ [])
                       (quote n≤1+n ∷ [])
                       (mkRelInfo (quote ≤-trans) (quote ≤-refl))

  -- Migration (item 13): old testRelB₅-style — both sides exercised, two
  -- ≡-rewrites on the LHS (n+0+0 → n) then two ~-steps to 2 + n.
  testRelB₅ : ∀ {n : ℕ} → n + 0 + 0 ≤ 2 + n
  testRelB₅ = simpRel! (quote +-identityʳ ∷ [])
                       (quote n≤1+n ∷ [])
                       (mkRelInfo (quote ≤-trans) (quote ≤-refl))

  -- Migration (item 13): old testRelB₆-style — LHS double-normalises and the
  -- ~-target rhs `2 + (n + 0)` also normalises.
  testRelB₆ : ∀ {n : ℕ} → n + 0 + 0 ≤ 2 + (n + 0)
  testRelB₆ = simpRel! (quote +-identityʳ ∷ [])
                       (quote n≤1+n ∷ [])
                       (mkRelInfo (quote ≤-trans) (quote ≤-refl))

  -- **** List permutation: simpRel! over _↭_ ****

  open import Data.List.Relation.Binary.Permutation.Propositional
    using (_↭_; ↭-refl; ↭-trans)
  import Data.List.Relation.Binary.Permutation.Propositional.Properties as ↭Prop

  -- Option C for ↭: ≡-normalise (xs ++ []) → xs in the LHS, ↭-refl closes.
  -- The new engine handles the raw polymorphic ++-identityʳ directly.
  testBag₁ : ∀ (xs ys : List ℕ) → (xs ++ []) ++ ys ↭ xs ++ ys
  testBag₁ = simpRel! (quote ++-identityʳ ∷ []) []
                      (mkRelInfo (quote ↭-trans) (quote ↭-refl))

  -- Option B for ↭: no ≡-rules, a single ++-comm ~-step.  Option B's
  -- match-all-binders instantiates the polymorphic ++-comm uniformly.
  testBag₄ : ∀ (xs ys : List ℕ) → xs ++ ys ↭ ys ++ xs
  testBag₄ = simpRel! [] (quote ↭Prop.++-comm ∷ [])
                      (mkRelInfo (quote ↭-trans) (quote ↭-refl))

  -- Migration (item 13): old testBag₂-style — BOTH sides ≡-normalise to
  -- the same form ([] ++ xs → xs and xs ++ [] → xs), ↭-refl closes.
  -- Exercises the both-sides-changed path in buildRelProof.
  testBag₂ : ∀ (xs : List ℕ) → [] ++ xs ↭ xs ++ []
  testBag₂ = simpRel! (quote ++-identityˡ ∷ quote ++-identityʳ ∷ []) []
                      (mkRelInfo (quote ↭-trans) (quote ↭-refl))

  -- Migration (item 13): old testBag₃-style — mixed ≡+~ chain.  The LHS
  -- ≡-normalises ([] ++ ys → ys) leaving xs ++ ys, then one ++-comm ~-step
  -- reaches ys ++ xs.
  testBag₃ : ∀ (xs ys : List ℕ) → xs ++ ([] ++ ys) ↭ ys ++ xs
  testBag₃ = simpRel! (quote ++-identityˡ ∷ []) (quote ↭Prop.++-comm ∷ [])
                      (mkRelInfo (quote ↭-trans) (quote ↭-refl))

  -- Migration (item 13): old testBag₅-style — double ≡-normalisation
  -- (two [] eliminations) on the LHS then one ↭ step.
  testBag₅ : ∀ (xs ys : List ℕ) → xs ++ ([] ++ (ys ++ [])) ↭ ys ++ xs
  testBag₅ = simpRel! (quote ++-identityˡ ∷ quote ++-identityʳ ∷ [])
                      (quote ↭Prop.++-comm ∷ [])
                      (mkRelInfo (quote ↭-trans) (quote ↭-refl))

  -- *** Task 2: mixed universe levels

  -- Same-level but generic: a single sort at level a (already worked
  -- before Task 2; confirms the fast path is unaffected).
  tlvl₁ : ∀ {a} {A : Set a} (xs ys : List A) → (xs ++ []) ++ ys ≡ xs ++ ys
  tlvl₁ = simp! (quote ++-identityʳ ∷ [])

  -- Mixed levels: `List A : Set a` and `ℕ : Set₀`.  The ℕ sort is lifted
  -- to `a`; the goal sort (ℕ) is lifted, so the proof is `cong lower …`.
  tlvl₂ : ∀ {a} {A : Set a} (xs : List A) → length (xs ++ []) ≡ length xs
  tlvl₂ = simp! (quote ++-identityʳ ∷ [])

  -- Mixed levels with a ℕ-side rule combined in the same goal.
  tlvl₃ : ∀ {a} {A : Set a} (xs : List A) → length (xs ++ []) + 0 ≡ length xs
  tlvl₃ = simp! (quote ++-identityʳ ∷ quote +-identityʳ ∷ [])

  -- *** Task 3 (item 9): ordered rewriting for permutative rules

  open import Data.Nat.Properties using (+-comm; +-assoc)

  -- +-comm alone: without the permutative gate this ping-pongs until
  -- fuel exhausts.  The gate orients it towards a single canonical form,
  -- and both sides share the operation table so they converge there.
  torder₁ : ∀ {x y : ℕ} → x + y ≡ y + x
  torder₁ = simp! (quote +-comm ∷ [])

  -- A left-commutativity wrapper is permutative (x + (y + z) ≡ y + (x + z),
  -- same tree shape, bijective var renaming) — the classic AC-completion
  -- partner of assoc + comm.
  +-lcomm : ∀ x y z → x + (y + z) ≡ y + (x + z)
  +-lcomm x y z =
    trans (sym (+-assoc x y z)) (trans (cong (_+ z) (+-comm x y)) (+-assoc y x z))

  -- AC normalisation with the assoc/comm/lcomm trio.  `ltExpr`'s
  -- size-first key keeps comm from breaking the right-spine, so assoc
  -- (right-association) + comm/lcomm (sorting) converge to one canonical
  -- form on both sides regardless of the input association.
  torder₂ : ∀ {a b c : ℕ} → (c + b) + a ≡ a + (b + c)
  torder₂ = simp! (quote +-assoc ∷ quote +-comm ∷ quote +-lcomm ∷ [])

  -- Four atoms, fully left-nested on the left, fully right-nested on the
  -- right — the AC trio normalises both to the same canonical sum.
  torder₄ : ∀ {a b c d : ℕ} → ((d + c) + b) + a ≡ a + (b + (c + d))
  torder₄ = simp! (quote +-assoc ∷ quote +-comm ∷ quote +-lcomm ∷ [])

  -- *** Task 2 (item 10): instantiation candidates beyond the goal

  -- `++-identityʳ`'s `{A := ℕ}` instantiation needs the candidate
  -- `dup n ++ []`, which appears NOWHERE in the goal — only in `f-eq`'s
  -- instantiated rhs.  Without enrichment this fails with
  -- "could not instantiate polymorphic rule"; the enrichment pass adds
  -- `f-eq`'s rhs subterms to the candidate pool, exposing it.
  dup : ℕ → List ℕ
  dup n = n ∷ n ∷ []

  f : ℕ → List ℕ
  f n = dup n ++ []

  f-eq : ∀ n → f n ≡ dup n ++ []
  f-eq n = refl

  tenrich₁ : ∀ n → f n ≡ dup n
  tenrich₁ = simp! (quote f-eq ∷ quote ++-identityʳ ∷ [])

  -- Non-regression: +-assoc alone is NOT permutative (different tree
  -- shape) and must keep behaving as an ordinary rule (cf. t₁₃).
  torder₃ : ∀ {a b c d : ℕ} → ((a + b) + c) + d ≡ a + (b + (c + d))
  torder₃ = simp! (quote +-assoc ∷ [])
