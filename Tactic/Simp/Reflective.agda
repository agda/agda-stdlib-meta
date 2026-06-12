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
open import Reflection.Utils hiding (args)
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

private

  ----------------------------------------------------------------
  -- Reification state: sort table + operation table.
  ----------------------------------------------------------------

  -- sorts: (normalised type , witness term valid in the goal context)
  -- ops:   (canonical impl term , argument sorts , result sort)
  record St : Set where
    constructor mkSt
    field sorts : List (Term × Maybe Term)
          ops   : List (Term × List ℕ × ℕ)

  keepW : Maybe Term → Maybe Term → Maybe Term
  keepW (just w) _ = just w
  keepW nothing  w = w

  addSort : Term → Maybe Term → St → ℕ × St
  addSort ty w (mkSt sorts ops) =
    let (i , sorts′) = go sorts in (i , mkSt sorts′ ops)
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
  addOp im as r (mkSt sorts ops) =
    let (i , ops′) = go ops in (i , mkSt sorts ops′)
    where
      go : List (Term × List ℕ × ℕ) → ℕ × List (Term × List ℕ × ℕ)
      go [] = 0 , (im , as , r) ∷ []
      go (e@(im′ , as′ , r′) ∷ rest) =
        if (im =α= im′) ∧ eqSorts as as′ ∧ (Data.Nat._≡ᵇ_ r r′)
          then (0 , e ∷ rest)
          else (let (i , rest′) = go rest in suc i , e ∷ rest′)

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

  -- λ x₁ … xₙ → head {hidden…} x₁ … xₙ  with the closed non-visible
  -- arguments strengthened out of the rule telescope and shifted
  -- under the new lambdas.
  mkImpl : ℕ → Term → Args Term → Term
  mkImpl depth hd as = wrapLams n (rebuild hd (go 0 as))
    where
      n : ℕ
      n = countVisible as

      go : ℕ → Args Term → Args Term
      go k []                                   = []
      go k (arg i@(arg-info visible _) _ ∷ rest) =
        arg i (var (n ∸ 1 ∸ k) []) ∷ go (suc k) rest
      go k (arg i t ∷ rest)                      =
        arg i (mapVars (λ v → v ∸ depth + n) t) ∷ go k rest

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
            (es , st₁) ← convArgs depth pats st as
            (r  , st₂) ← inferSort depth st₁ orig (witnessOf depth orig)
            let im        = mkImpl depth hd as
                (o , st₃) = addOp im (map RC.sortOf es) r st₂
            return (RC.Expr.op o r es , st₃))

    -- Converts the visible arguments only (structural recursion).
    convArgs : ℕ → List ℕ → St → Args Term → TC (List RC.Expr × St)
    convArgs depth pats st [] = return ([] , st)
    convArgs depth pats st (arg (arg-info visible _) t ∷ as) = do
      (e  , st₁) ← conv depth pats st t
      (es , st₂) ← convArgs depth pats st₁ as
      return (e ∷ es , st₂)
    convArgs depth pats st (_ ∷ as) = convArgs depth pats st as

    convAtom : ℕ → St → Term → TC (RC.Expr × St)
    convAtom depth st t =
      case usesVarBelow depth t of λ where
        true  → error1 ("simp!: opaque subterm mentions rule variables (unsupported): " <+> show t)
        false → do
          let t′ = strengthenBy depth t
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
        return (body , (i , dom) ∷ tel)
      _ → return (ty′ , [])

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

  -- Append extra args to a head term (no de Bruijn shift here).
  applyTerm : Term → Args Term → Term
  applyTerm (var k as) extra = var k (as ++ extra)
  applyTerm (def f as) extra = def f (as ++ extra)
  applyTerm (con c as) extra = con c (as ++ extra)
  applyTerm t          _     = t

  applyHead : Head → Args Term → Term
  applyHead (hName n) extra = def n extra
  applyHead (hTerm t) extra = applyTerm (mapVars suc t) extra

  -- λ τ → head pre… (τ s₁ i₁) … (τ sₖ iₖ): binder k (outermost-first,
  -- of d binders, with sort sₖ) is pattern variable d∸1∸k.  `pre` is
  -- the parameter instantiation (goal-context terms, hence shifted
  -- under the λ).  A hypothesis head carries no `pre` (`[]`) and is
  -- itself shifted under the λ by `applyHead`.  Typechecks by
  -- computation of `evalAt`.
  mkSoundTerm : Head → Args Term → List (ArgInfo × ℕ) → Term
  mkSoundTerm hd pre is =
    let d = length is
    in `λ "τ" ⇒ applyHead hd (map-Args (mapVars suc) pre ++ zipWithIndex
         (λ k p → arg (proj₁ p)
            (var 0 (vArg (`ℕ (proj₂ p)) ∷ vArg (`ℕ (d ∸ 1 ∸ k)) ∷ [])))
         is)

  processRuleMono : Head → Args Term → List (ArgInfo × Term) → Term → St
                  → TC (Term × St)
  processRuleMono hd pre tel body st = do
    (def (quote _≡_) (hArg _ ∷ hArg _ ∷ vArg lhs ∷ vArg rhs ∷ [])) ← return body
      where _ → error1 ("simp!: not an equation: " <+> show body)
    let depth = length tel
    (bs , st₁) ← goBinders 0 st tel
    let pats = reverse bs
    (lhsE , rhsE , st₂) ← extendCtxTel tel (do
      (lhsE , sta) ← conv depth pats st₁ lhs
      (rhsE , stb) ← conv depth pats sta rhs
      return (lhsE , rhsE , stb))
    lhsT ← quoteNorm lhsE
    rhsT ← quoteNorm rhsE
    return ( con (quote RC.Eval.mkRule)
               ( vArg lhsT ∷ vArg rhsT ∷ vArg (con (quote refl) [])
               ∷ vArg (mkSoundTerm hd pre (zip (map proj₁ tel) bs)) ∷ [] )
           , st₂ )

  -- Specialise the rule at one parameter assignment: apply the lemma
  -- to the instantiation and let Agda compute the remaining type.
  processAssign : Name → List ArgInfo → St → List Term → TC (Term × St)
  processAssign n infos st vals = do
    let pre = Data.List.zipWith arg infos vals
    specTy ← inferType (def n pre)
    (body , tel) ← stripAndReduce 100 specTy
    processRuleMono (hName n) pre tel body st

  processAssigns : Name → List ArgInfo → St → List (List Term)
                 → TC (List Term × St)
  processAssigns n infos st []       = return ([] , st)
  processAssigns n infos st (v ∷ vs) = do
    (r  , st₁) ← processAssign n infos st v
    (rs , st₂) ← processAssigns n infos st₁ vs
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
          (r , st₁) ← processRuleMono (hName n) [] tel body st
          return (r ∷ [] , st₁)
        _ → do
          (def (quote _≡_) (hArg _ ∷ hArg _ ∷ vArg lhs ∷ vArg _ ∷ [])) ← return body
            where _ → error1 ("simp!: not an equation: " <+> show body)
          (just hd) ← return (headName lhs)
            where nothing → error1 ("simp!: cannot instantiate a rule whose lhs is not an application: " <+> show n)
          case findAssignments (length tel) p hd lhs cands of λ where
            []    → error1 ("simp!: could not instantiate polymorphic rule from the goal: " <+> show n)
            asgns → processAssigns n (map proj₁ (take p tel)) st asgns)

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
        (r , st₁) ← processRuleMono (hTerm h) [] tel body st
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

  quoteOps : List (Term × List ℕ × ℕ) → Term
  quoteOps ops = quoteList (map
    (λ p → quotePair
             (quotePair (quoteList (map `ℕ (proj₁ (proj₂ p))))
                        (`ℕ (proj₂ (proj₂ p))))
             (proj₁ p))
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
        valApp = def (quote RC.Eval.evalAt)
                  ( vArg TsT ∷ vArg opsT
                  ∷ vArg (`ℕ g)
                  ∷ vArg (def (quote RC.Eval.ρ₀) (vArg TsT ∷ vArg opsT ∷ []))
                  ∷ vArg nfApp ∷ [] )
    t ← normalise valApp
    return (show t)

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
      (def (quote _≡_) (hArg _ ∷ hArg _ ∷ vArg lhs ∷ vArg rhs ∷ [])) → do
        -- Shift the call-site hypothesis terms past the binders we
        -- entered (their indices are relative to the call site, which
        -- excludes the stripped ∀-binders).
        let hyps′ = map (mapVars (_+ depth)) hyps
        (ruleTs , st₀) ← processRules (subApps lhs ++ subApps rhs) names (mkSt [] [])
        (hypTs  , st₀′) ← processHyps st₀ hyps′
        let allRuleTs = ruleTs ++ hypTs
        (lhsE , st₁) ← conv 0 [] st₀′ lhs
        (rhsE , st₂) ← conv 0 [] st₁ rhs
        lT  ← quoteNorm lhsE
        rT  ← quoteNorm rhsE
        TsT ← quoteSorts (St.sorts st₂)
        let opsT     = quoteOps (St.ops st₂)
            rulesT   = quoteList allRuleTs
            g        = RC.sortOf lhsE
            solveApp = def (quote RC.Eval.solveAt)
              ( vArg TsT ∷ vArg opsT
              ∷ vArg (`ℕ g) ∷ vArg (`ℕ 100)
              ∷ vArg rulesT ∷ vArg lT ∷ vArg rT ∷ [] )
        -- Pre-run the solver to WHNF at the meta level for a decent
        -- error (via is-just, so the proof term is never normalised).
        nf ← normalise (def (quote Data.Maybe.is-just) (vArg solveApp ∷ []))
        case nf of λ where
          (con c _) → if c == quote Data.Bool.false
            then (do
              lNF ← showStuck TsT opsT g rulesT lT
              rNF ← showStuck TsT opsT g rulesT rT
              error1 ("simp!: simplification failed to close the goal;\n  the two sides reached the normal forms\n    "
                      <+> lNF <+> "\n  and\n    " <+> rNF))
            else unifyWithGoal (def (quote RC.from-just!) (vArg solveApp ∷ []))
          _ → unifyWithGoal (def (quote RC.from-just!) (vArg solveApp ∷ []))
      _ → error1 "simp!: goal is not a propositional equality"

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
    hyps ← unquoteHypList 100 hypsExpr
    simpHTactic names hyps) defaultTCOptions

-- ** Tests

private
  open import Tactic.Defaults
  open import Data.List.Properties using (++-identityʳ; length-map)

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
