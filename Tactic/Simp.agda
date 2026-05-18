-- TODO: support goals other than equalities (e.g., boolean goals via decide)

-- Currently requires `--lossy-unification`. To drop that requirement we'd need
-- to implement our own unification (or ask Agda for a lossy `unify` primitive).

{-# OPTIONS --safe #-}
{-# OPTIONS --lossy-unification #-}

module Tactic.Simp where

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
open import Data.String hiding (show; map; head; replicate; _==_; length; _≤_; _≈_; _<_)
  renaming (_++_ to _++S_)

open import Function

open import Relation.Binary.PropositionalEquality

open import Meta.Init
open import Meta.Prelude
open import Reflection.AlphaEquality
open import Reflection.QuotedDefinitions
open import Reflection.Tactic
open import Reflection.Utils hiding (args)
open import Reflection.Utils.TCI using (applyWithVisibility; unifyStrict)

open import Class.Monoid
open import Class.Monad
open import Class.MonadError

open MonadError ⦃...⦄

-- ** Private helpers

private
  -- stdlib 2.3 has updateAt : List A → Fin (length xs) → (A → A) → List A
  -- which differs from the ℕ-indexed version we need here.
  updateAtℕ : ℕ → (A → A) → List A → List A
  updateAtℕ _       _ []       = []
  updateAtℕ zero    f (x ∷ xs) = f x ∷ xs
  updateAtℕ (suc i) f (x ∷ xs) = x ∷ updateAtℕ i f xs

  -- Replace the value inside an Arg, preserving its ArgInfo.
  setArgValue : Term → Arg Term → Arg Term
  setArgValue t (arg i _) = arg i t

  replicateM : {A : Set} → ℕ → TC A → TC (List A)
  replicateM n x = sequence (replicate n x)

  -- Substitution that replaces var x with s, leaving all other vars unchanged
  -- (no de Bruijn shifting).  Treating metas as atomic avoids corrupting the
  -- context args that newMeta injects into meta terms.
  -- Sequential applications of substTermAtExact for distinct indices is equivalent
  -- to simultaneous substitution, because no index is shifted between steps.
  -- This is required for open templates (rules defined inside parameterised modules)
  -- where vars ≥ fv are outer-context references that must not be shifted.
  mutual
    substTermAtExact : ℕ → Term → Term → Term
    substTermAtExact x s (var y as) = case compare x y of λ where
      (equal _) → s
      _         → var y (substArgsAtExact x s as)
    substTermAtExact x s (con c as)               = con c (substArgsAtExact x s as)
    substTermAtExact x s (def f as)               = def f (substArgsAtExact x s as)
    substTermAtExact x s (lam v (abs z t))        = lam v (abs z (substTermAtExact (suc x) s t))
    substTermAtExact _ _ (pat-lam _ _)            = unknown
    substTermAtExact x s (pi (arg i a) (abs z b)) =
      pi (arg i (substTermAtExact x s a)) (abs z (substTermAtExact (suc x) s b))
    substTermAtExact _ _ (meta m as)              = meta m as
    substTermAtExact _ _ t                        = t

    substArgsAtExact : ℕ → Term → List (Arg Term) → List (Arg Term)
    substArgsAtExact _ _ []              = []
    substArgsAtExact x s (arg i t ∷ ts)  = arg i (substTermAtExact x s t) ∷ substArgsAtExact x s ts

  isRefl : Term → Bool
  isRefl (con n _) = n == quote refl
  isRefl _         = false

  -- Strip leading ∀/pi binders and count them.
  removePis : Term → Term × ℕ
  removePis (pi _ (abs _ b)) = map₂ suc (removePis b)
  removePis t                = (t , 0)

  -- Extract (relN, prefix-args, lhs, rhs) from a binary-relation goal by
  -- treating the last two visible args of a def-headed term as lhs and rhs.
  getRelSides : Term → Maybe (Name × Args Term × Term × Term)
  getRelSides (def relN args) =
    case reverse args of λ where
      (vArg rhs ∷ vArg lhs ∷ rest) → just (relN , reverse rest , lhs , rhs)
      _ → nothing
  getRelSides _ = nothing

-- ** Matching

-- Try to unify term t with the template (which has freeVars free variables).
-- Returns the instantiated free variables on success.
matchTerms : (freeVars : ℕ) → Term → Term → TC (Maybe (List Term))
matchTerms fv t templ = runSpeculative do
  metas ← replicateM fv (newMeta unknown)
  -- Substitute var i → m_{fv-1-i} via substTermAtExact (no shifting).
  -- downFrom fv = [fv-1, …, 0], so zip pairs each meta with its target index,
  -- preserving the var→meta mapping that applyWithVisibility expects.
  let substd = foldl (λ acc p → substTermAtExact (proj₁ p) (proj₂ p) acc)
                     templ
                     (zip (downFrom fv) metas)
  catch
    (unify t substd >> return (just metas , true))
    (λ _ → return (nothing , false))

-- ** Equation dictionary

data Instantiated : Set where
  isInst notInst : Instantiated

Instantiation : Instantiated → Set
Instantiation isInst  = List Term
Instantiation notInst = ℕ

record Equation (i : Instantiated) : Set where
  field lhs rhs : Term
        name    : Name
        args    : Instantiation i

EqDict = List (Equation notInst)

preprocessDict : List Name → TC EqDict
preprocessDict = traverse genEq
  where
    genEq : Name → TC (Equation notInst)
    genEq n = do
      ty ← getType n >>= reduce
      case removePis ty of λ where
        (def (quote _≡_) (hArg _ ∷ hArg _ ∷ vArg lhs ∷ vArg rhs ∷ []) , numArgs) →
          return record { lhs = lhs ; rhs = rhs ; name = n ; args = numArgs }
        (ty' , _) →
          error1 ("Error while preprocessing simp dict: Not an equation: " <+> show ty')

-- Apply an instantiated equation to produce the proof term
extractRewrite : Equation isInst → TC Term
extractRewrite record { name = n ; args = xs } = applyWithVisibility n xs

-- Like preprocessDict but accepts rules of any binary relation (lhs ~ rhs).
preprocessDictRel : List Name → TC EqDict
preprocessDictRel = traverse genRelEq
  where
    genRelEq : Name → TC (Equation notInst)
    genRelEq n = do
      ty ← getType n >>= normalise
      let (relTy , numArgs) = removePis ty
      just (_ , _ , lhs , rhs) ← return (getRelSides relTy)
        where nothing → error1 ("Error in rel dict: not a binary relation: " <+> show relTy)
      return record { lhs = lhs ; rhs = rhs ; name = n ; args = numArgs }

-- ** Extensible dictionaries

-- To build an extensible simp dictionary, declare a dummy type:
--   data MyDict : Set where
-- then register rules via instance declarations:
--   instance myRule : Simp MyDict; myRule = mkSimp (quote myLemma)
record Simp (D : Set) : Set where
  constructor mkSimp
  field ruleName : Name

private
  extractDictName : Term → TC Name
  extractDictName inst = do
    t ← normalise (def (quote Simp.ruleName) (hArg unknown ∷ vArg inst ∷ []))
    unquoteTC t

  getDictNames : Term → TC (List Name)
  getDictNames dictTy = do
    insts ← findInstances (def (quote Simp) (vArg dictTy ∷ []))
    sequence (map extractDictName insts)

-- ** Simplification

-- Build the congruence lambda: λ ◆ → (def/con f args)[args[i] ↦ ◆]
-- Free variables in all args are shifted by 1 under the lambda.
buildCongLambda : Bool → Name → Args Term → ℕ → Term
buildCongLambda isDef f args i =
  let shiftedArgs = map-Args (mapVars suc) args
      newArgs     = updateAtℕ i (setArgValue (var 0 [])) shiftedArgs
      body        = if isDef then def f newArgs else con f newArgs
  in `λ "◆" ⇒ body

private
  -- Try one rule; wraps in runSpeculative so that any committed constraints
  -- from matchTerms's unify are rolled back if the alpha-equality guard fails.
  tryOneRule : Term → Term → Equation notInst → TC (Maybe (Term × Term) × Bool)
  tryOneRule orig t' eq = do
    just metas ← matchTerms (Equation.args eq) t' (Equation.lhs eq)
      where nothing → return (nothing , false)
    proof ← extractRewrite (record { Equation eq ; args = metas })
    ty    ← inferType proof
    (lhs' ``≡ rhs') ← return ty
      where _ → return (nothing , false)
    if lhs' =α= orig
      then return (just (rhs' , proof) , true)
      else return (nothing , false)

  -- Iterate through the dict; try each rule with full rollback on failure.
  tryRuleStep : Term → Term → EqDict → TC (Maybe (Term × Term))
  tryRuleStep _    _  []           = return nothing
  tryRuleStep orig t' (eq ∷ eqs)   = do
    just r ← runSpeculative (tryOneRule orig t' eq)
      where nothing → tryRuleStep orig t' eqs
    return (just r)

-- Try a top-level rule match on t.
-- Iterates through all rules; validates each candidate via alpha-equality
-- to filter spurious matches produced by --lossy-unification.
tryRule : EqDict → Term → TC (Maybe (Term × Term))
tryRule d t = do
  t' ← reduce t
  tryRuleStep t t' d

mutual
  -- Try to simplify t at the top level or in a direct argument of a def/con.
  -- Returns (t', proof : t ≡ t') if t simplifies, nothing otherwise.
  simpAll : EqDict → Term → TC (Maybe (Term × Term))
  simpAll d t = do
    result ← tryRule d t
    case result of λ where
      (just r) → return (just r)
      nothing  → case t of λ where
        (def f as) → simpInArgs true  f as d
        (con c as) → simpInArgs false c as d
        _          → return nothing

  -- Try to simplify an argument of (def/con f args).
  -- Returns (newTerm, proof : (def/con f args) ≡ newTerm) if any arg simplifies.
  simpInArgs : Bool → Name → Args Term → EqDict → TC (Maybe (Term × Term))
  simpInArgs isDef f args d = do
    result ← tryArgs d args
    case result of λ where
      nothing → return nothing
      (just (i , a' , proof)) →
        let newArgs = updateAtℕ i (setArgValue a') args
            newTerm = if isDef then def f newArgs else con f newArgs
            lambda  = buildCongLambda isDef f args i
        in return (just (newTerm , quote cong ∙⟦ lambda ∣ proof ⟧))

  -- Find and simplify the first simplifiable argument in a list.
  -- Returns (index, newValue, proof) on success.
  tryArgs : EqDict → Args Term → TC (Maybe (ℕ × Term × Term))
  tryArgs _ [] = return nothing
  tryArgs d (arg _ a ∷ rest) = do
    result ← simpAll d a
    case result of λ where
      (just (a' , proof)) → return (just (0 , a' , proof))
      nothing → do
        r ← tryArgs d rest
        case r of λ where
          nothing              → return nothing
          (just (i , a' , p)) → return (just (suc i , a' , p))

-- Repeatedly simplify t (up to n steps), chaining proofs with trans.
-- Returns (normalForm, proof : t ≡ normalForm).
simpIter : ℕ → EqDict → Term → TC (Term × Term)
simpIter 0       _ t = return (t , `refl)
simpIter (suc n) d t = do
  result ← simpAll d t
  case result of λ where
    nothing → return (t , `refl)
    (just (t' , step)) → do
      (t'' , rest) ← simpIter n d t'
      -- Avoid trans _ refl
      return (t'' , (if isRefl rest then step else quote trans ∙⟦ step ∣ rest ⟧))

-- ** Setoid / preorder rewriting

-- Carry the relation's transitivity and reflexivity witnesses.
record RelInfo : Set where
  constructor mkRelInfo
  field
    relTrans : Name   -- trans : a ~ b → b ~ c → a ~ c
    relRefl  : Name   -- a ~ a

private
  -- Like tryOneRule / tryRuleStep / tryRule but for ~ rules (not ≡).
  -- Checks that the proof has the expected relation head relN.
  -- g = number of goal binders simpGoalRel has stripped so far (unused here;
  -- de Bruijn correctness comes for free because inferType runs in the current
  -- extended context, so lhs' already has the right indices).
  tryOneRuleRel : Name → Term → Term → Equation notInst → ℕ → TC (Maybe (Term × Term) × Bool)
  tryOneRuleRel relN orig t' eq g =
    catch go (λ _ → return (nothing , false))
    where
    go : TC (Maybe (Term × Term) × Bool)
    go = do
      metas ← replicateM (Equation.args eq) (newMeta unknown)
      proof ← extractRewrite (record { Equation eq ; args = metas })
      pty   ← inferType proof >>= normalise
      just (relN' , _ , lhs' , rhs') ← return (getRelSides pty)
        where nothing → return (nothing , false)
      case (relN' == relN) of λ where
        false → return (nothing , false)
        true  → do
          unify t' lhs'
          rhs'' ← normalise rhs'
          proof' ← normalise proof
          return (just (rhs'' , proof') , true)

  tryRuleStepRel : Name → Term → Term → EqDict → ℕ → TC (Maybe (Term × Term))
  tryRuleStepRel _    _    _  []         _ = return nothing
  tryRuleStepRel relN orig t' (eq ∷ eqs) g = do
    just r ← runSpeculative (tryOneRuleRel relN orig t' eq g)
      where nothing → tryRuleStepRel relN orig t' eqs g
    return (just r)

tryRuleRel : Name → EqDict → Term → ℕ → TC (Maybe (Term × Term))
tryRuleRel relN relD t g = do
  t' ← reduce t
  tryRuleStepRel relN t t' relD g

private
  -- Count the leading non-visible (hidden / instance) Pi-binders of a type.
  -- Used to decide whether relRefl/relTrans are "global" (quantify over the
  -- relation's universe/type params themselves) or "module-local" (those params
  -- are already free variables in the local context).
  countLeadingHiddenPis : Term → ℕ
  countLeadingHiddenPis (pi (arg (arg-info visible _) _) _)        = 0
  countLeadingHiddenPis (pi (arg _ _) (abs _ body))                = suc (countLeadingHiddenPis body)
  countLeadingHiddenPis _                                           = 0

  -- Chain ~ rules from lhs towards rhs (both fully normalised before calling).
  -- Stops when lhs =α= rhs or no rules apply.  Returns (lhs'', proof : lhs ~ lhs'').
  -- modVarFix: pre-computed flag (see simpGoalRel).
  -- prefix: the non-LHS/RHS args of the relation (levels, bundles) – supplied
  -- explicitly for "global" relations where Agda would otherwise leave metas unsolved.
  simpIterTop : Name → RelInfo → Bool → ℕ → EqDict → Args Term → Term → Term → TC (Term × Term)
  simpIterTop relN ri modVarFix n relD prefix lhs rhs = do
    -- modVarFix=true  (module-local case, e.g. ≈-trans-M inside a Monoid module):
    --   The effective type already has module params as free vars.  We must NOT
    --   re-supply them via prefix; instead pass the carrier-element endpoints as
    --   hidden args so Agda can fill {x y z : Carrier M}.
    -- modVarFix=false (global/top-level case, e.g. ↭-trans, ≤-trans):
    --   Pass the prefix args first, then the endpoint hidden args explicitly so
    --   that the generated proof term has no unsolved metas.
    let reflTerm = if modVarFix
                   then def (RelInfo.relRefl  ri) (hArg lhs ∷ [])
                   else def (RelInfo.relRefl  ri) (prefix ++ hArg lhs ∷ [])
    if lhs =α= rhs
      then return (lhs , reflTerm)
      else case n of λ where
        zero    → return (lhs , reflTerm)
        (suc m) → do
          result ← tryRuleRel relN relD lhs 0
          case result of λ where
            nothing → return (lhs , reflTerm)
            (just (lhs' , step)) → do
              lhs'norm ← normalise lhs'
              (lhs'' , rest) ← simpIterTop relN ri modVarFix m relD prefix lhs'norm rhs
              let chain = if modVarFix
                          then def (RelInfo.relTrans ri)
                                 (hArg lhs ∷ hArg lhs'norm ∷ hArg lhs'' ∷ vArg step ∷ vArg rest ∷ [])
                          else def (RelInfo.relTrans ri)
                                 (prefix ++ hArg lhs ∷ hArg lhs'norm ∷ hArg lhs'' ∷ vArg step ∷ vArg rest ∷ [])
              return (lhs'' , chain)

  -- Build proof of (lhs ~ rhs) given
  --   p1      : lhs ≡ lhs'norm  (≡-normalisation of the LHS)
  --   p2      : rhs ≡ rhs'norm  (≡-normalisation of the RHS)
  --   core    : lhs'norm ~ rhs'norm
  --   lhs'norm: normalised simplified LHS
  --   rhs     : original RHS from the goal
  --
  -- Uses subst with explicit predicate lambdas instead of a helper function.
  -- The explicit lambda lets Agda type-check the predicate body directly,
  -- avoiding function-type unification of the relation (which can generate
  -- problematic constraints under --lossy-unification).
  buildRelProof : Name → Args Term → Term → Term → Term → Term → Term → Term
  buildRelProof relN prefix p1 p2 core lhs'norm rhs =
    let prefixS = map-Args (mapVars suc) prefix
        -- predL: λ ◆ → relN prefix ◆ rhs  (for rewriting the LHS)
        predL   = lam visible (abs "◆" (def relN (prefixS ++ vArg (var 0 []) ∷ vArg (mapVars suc rhs) ∷ [])))
        -- predR: λ ◆ → relN prefix lhs'norm ◆  (for rewriting the RHS)
        predR   = lam visible (abs "◆" (def relN (prefixS ++ vArg (mapVars suc lhs'norm) ∷ vArg (var 0 []) ∷ [])))
        sym' p  = def (quote sym) (vArg p ∷ [])
        subst' P eq t = def (quote subst) (vArg P ∷ vArg eq ∷ vArg t ∷ [])
    in
    if isRefl p1
    then if isRefl p2
         then core                                  -- 1: both refl, use core directly
         else subst' predR (sym' p2) core           -- 2: only RHS simplifies
    else if isRefl p2
         then subst' predL (sym' p1) core           -- 3: only LHS simplifies
         else subst' predL (sym' p1)
                (subst' predR (sym' p2) core)       -- 4: both sides simplify

  -- eqD  : ≡-rules for sub-term normalisation (full cong machinery)
  -- relD : ~-rules chained top-level with relTrans after ≡-normalisation
  simpGoalRel : ℕ → RelInfo → EqDict → EqDict → ITactic
  simpGoalRel 0       _  _   _   = error1 "simpRel: goal has too many binders"
  simpGoalRel (suc n) ri eqD relD = do
    hole ← goalHole
    ty   ← inferType hole >>= reduce
    case ty of λ where
      (pi argTy@(arg (arg-info v _) _) (abs x bodyTy)) → do
        hole′ ← extendContext (x , argTy) (newMeta bodyTy)
        unifyStrict (hole , ty) (lam v (abs x hole′))
        extendContext (x , argTy) (runWithHole hole′ (simpGoalRel n ri eqD relD))
      _ → do
        just (relN , prefix , lhs , rhs) ← return (getRelSides ty)
          where nothing → error1 "simpRel: goal is not a binary relation"
        relReflTy ← getType (RelInfo.relRefl ri)
        let modVarFix = countLeadingHiddenPis relReflTy <ᵇ length prefix
        rawProof ← runAndReset do
          (lhs' , p1raw) ← simpIter 100 eqD lhs
          (rhs' , p2raw) ← simpIter 100 eqD rhs
          p1       ← normalise p1raw
          p2       ← normalise p2raw
          lhs'norm ← normalise lhs'
          rhs'norm ← normalise rhs'
          (_ , core) ← simpIterTop relN ri modVarFix 100 relD prefix lhs'norm rhs'norm
          return (buildRelProof relN prefix p1 p2 core lhs'norm rhs)
        unifyWithGoal rawProof

simpRelTactic : List Name → List Name → RelInfo → ITactic
simpRelTactic eqNames relNames ri = do
  eqD  ← preprocessDict eqNames
  relD ← preprocessDictRel relNames
  simpGoalRel 100 ri eqD relD

macro
  -- Prove a ~ b by (1) ≡-normalising sub-terms with eqRules, then (2) chaining
  -- top-level ~-steps with relRules, then (3) closing with relRefl.
  simpRel : List Name → List Name → RelInfo → Tactic
  simpRel eqRules relRules ri =
    initTacOpts (simpRelTactic eqRules relRules ri) defaultTCOptions

  -- Like simpRel but loads ≡-rules from extensible dict D.
  -- Pass explicit relRules for the top-level ~-steps.
  simpRelD : (D : Set) → List Name → RelInfo → Tactic
  simpRelD D relRules ri = initTacOpts (do
    dictTy ← quoteTC D
    eqNames ← getDictNames dictTy
    simpRelTactic eqNames relRules ri) defaultTCOptions

-- ** The simp tactic

private
  buildProof : Term → Term → Term
  buildProof p1 p2 =
    if isRefl p1
      then (if isRefl p2 then `refl else quote sym ∙⟦ p2 ⟧)
      else (if isRefl p2 then p1 else quote trans ∙⟦ p1 ∣ quote sym ∙⟦ p2 ⟧ ⟧)

  -- Recurse under ∀ binders (fuel bounds the number of binders).
  simpGoal : ℕ → EqDict → ITactic
  simpGoal 0       _ = error1 "simp: goal has too many binders"
  simpGoal (suc n) d = do
    hole ← goalHole
    ty   ← inferType hole >>= reduce
    case ty of λ where
      (pi argTy@(arg (arg-info v _) _) (abs x bodyTy)) → do
        hole′ ← extendContext (x , argTy) (newMeta bodyTy)
        unifyStrict (hole , ty) (lam v (abs x hole′))
        extendContext (x , argTy) (runWithHole hole′ (simpGoal n d))
      _ → do
        (lhs ``≡ rhs) ← return ty
          where _ → error1 "simp: goal is not a propositional equality"
        (_ , p1) ← simpIter 100 d lhs
        (_ , p2) ← simpIter 100 d rhs
        unifyWithGoal (buildProof p1 p2)

-- Simplifies the goal, recursing under ∀ binders and proving the resulting
-- equality by simplifying both sides to a common normal form.
simpTactic : List Name → ITactic
simpTactic names = do
  d ← preprocessDict names
  simpGoal 100 d

macro
  simp : List Name → Tactic
  simp names = initTacOpts (simpTactic names) defaultTCOptions

  simpD : (D : Set) → Tactic
  simpD D = initTacOpts (do
    dictTy ← quoteTC D
    names  ← getDictNames dictTy
    simpTactic names) defaultTCOptions

-- ** Tests

private
  open import Tactic.Defaults

  test₁ : ∀ {x y : ℕ} → (x + 0) + y ≡ x + (0 + y)
  test₁ = simp (quote +-assoc ∷ quote +-identityˡ ∷ quote +-identityʳ ∷ [])

  test₂ : ∀ {x : ℕ} → x + 0 ≡ x
  test₂ = simp (quote +-identityʳ ∷ [])

  test₃ : ∀ {x y : ℕ} → (x + 0) + (0 + y) ≡ x + y
  test₃ = simp (quote +-identityˡ ∷ quote +-identityʳ ∷ [])

  -- Multiple applications of the same rule
  test₄ : ∀ {x : ℕ} → x + 0 + 0 ≡ x
  test₄ = simp (quote +-identityʳ ∷ [])

  -- Simplification in a non-leftmost argument (tryArgs skips the inert x)
  test₅ : ∀ {x y : ℕ} → x + (y + 0) ≡ x + y
  test₅ = simp (quote +-identityʳ ∷ [])

  -- Only the RHS needs simplification (result is sym p₂)
  test₆ : ∀ {x : ℕ} → x ≡ x + 0
  test₆ = simp (quote +-identityʳ ∷ [])

  -- Different operator
  test₇ : ∀ {x : ℕ} → x * 1 ≡ x
  test₇ = simp (quote *-identityʳ ∷ [])

  -- Each argument simplified by a different rule
  test₈ : ∀ {x y : ℕ} → (x * 1) + (0 + y) ≡ x + y
  test₈ = simp (quote *-identityʳ ∷ quote +-identityˡ ∷ [])

  -- Top-level rule exposes a new redex in the result
  test₉ : ∀ {x : ℕ} → (x + 0) * 1 ≡ x
  test₉ = simp (quote *-identityʳ ∷ quote +-identityʳ ∷ [])

  -- Three-rule chain: zero-annihilation, then identity, then identity
  test₁₀ : ∀ {x y : ℕ} → (x + y) * 0 + x * 1 ≡ x
  test₁₀ = simp (quote *-zeroʳ ∷ quote *-identityʳ ∷ quote +-identityˡ ∷ [])

  -- Trivial goal: both sides return refl and unifyWithGoal refl succeeds
  test₁₁ : ∀ {x : ℕ} → x ≡ x
  test₁₁ = simp []

  -- Simplification two levels deep inside an argument
  test₁₂ : ∀ {x y z : ℕ} → (x + 0) + ((y + 0) + z) ≡ x + (y + z)
  test₁₂ = simp (quote +-identityʳ ∷ [])

  -- Left-associativity flattening in two top-level steps
  test₁₃ : ∀ {a b c d : ℕ} → ((a + b) + c) + d ≡ a + (b + (c + d))
  test₁₃ = simp (quote +-assoc ∷ [])

  -- Rewriting under an explicit ∀ binder
  testBinder₁ : ∀ (n : ℕ) → n + 0 ≡ n
  testBinder₁ = simp (quote +-identityʳ ∷ [])

  -- Rewriting under an implicit ∀ binder
  testBinder₂ : ∀ {n : ℕ} → n + 0 ≡ n
  testBinder₂ = simp (quote +-identityʳ ∷ [])

  -- Rewriting under mixed explicit and implicit binders
  testBinder₃ : ∀ (m : ℕ) {n : ℕ} → (m + 0) + (0 + n) ≡ m + n
  testBinder₃ = simp (quote +-identityˡ ∷ quote +-identityʳ ∷ [])

  -- ** simpD: extensible dictionary tests **

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
  testDict₁ = simpD ArithRules

  -- Multiple rules from dictionary
  testDict₂ : ∀ {x y : ℕ} → (x + 0) + (0 + y) ≡ x + y
  testDict₂ = simpD ArithRules

  -- Associativity from dictionary
  testDict₃ : ∀ {a b c d : ℕ} → ((a + b) + c) + d ≡ a + (b + (c + d))
  testDict₃ = simpD ArithRules

  -- ** simpRel: Option C tests (≡-normalisation only, no top-level ~-rules) **

  -- Normalisation on the LHS only; ≤-refl closes the resulting n ≤ n
  testRel₁ : ∀ {n : ℕ} → n + 0 ≤ n
  testRel₁ = simpRel (quote +-identityʳ ∷ []) [] (mkRelInfo (quote ≤-trans) (quote ≤-refl))

  -- Normalisation on the RHS only
  testRel₂ : ∀ {n : ℕ} → n ≤ n + 0
  testRel₂ = simpRel (quote +-identityʳ ∷ []) [] (mkRelInfo (quote ≤-trans) (quote ≤-refl))

  -- Normalisation on both sides independently
  testRel₃ : ∀ {n m : ℕ} → (n + 0) + (0 + m) ≤ n + m
  testRel₃ = simpRel (quote +-identityˡ ∷ quote +-identityʳ ∷ []) []
                     (mkRelInfo (quote ≤-trans) (quote ≤-refl))

  -- Works under an explicit binder
  testRel₄ : ∀ (n : ℕ) → n + 0 ≤ n
  testRel₄ = simpRel (quote +-identityʳ ∷ []) [] (mkRelInfo (quote ≤-trans) (quote ≤-refl))

  -- Works under mixed binders
  testRel₅ : ∀ (m : ℕ) {n : ℕ} → (m + 0) + (0 + n) ≤ m + n
  testRel₅ = simpRel (quote +-identityˡ ∷ quote +-identityʳ ∷ []) []
                     (mkRelInfo (quote ≤-trans) (quote ≤-refl))

  -- Deep sub-term normalisation (two levels inside _+_)
  testRel₆ : ∀ {a b c : ℕ} → (a + 0) + ((b + 0) + c) ≤ a + (b + c)
  testRel₆ = simpRel (quote +-identityʳ ∷ []) [] (mkRelInfo (quote ≤-trans) (quote ≤-refl))

  -- ** simpRelD: extensible-dictionary variant **

  testRelDict₁ : ∀ {n : ℕ} → n + 0 ≤ n
  testRelDict₁ = simpRelD ArithRules [] (mkRelInfo (quote ≤-trans) (quote ≤-refl))

  testRelDict₂ : ∀ {n m : ℕ} → (n + 0) + (0 + m) ≤ n + m
  testRelDict₂ = simpRelD ArithRules [] (mkRelInfo (quote ≤-trans) (quote ≤-refl))

  -- ** Option B tests: top-level ~-rule chaining **

  -- n≤1+n : ∀ n → n ≤ 1 + n  (from Data.Nat.Properties)
  -- ≡-normalise LHS (n+0 → n), then top-level ~-rule closes n ≤ 1+n
  testRelB₁ : ∀ {n : ℕ} → n + 0 ≤ 1 + n
  testRelB₁ = simpRel (quote +-identityʳ ∷ [])
                      (quote n≤1+n ∷ [])
                      (mkRelInfo (quote ≤-trans) (quote ≤-refl))

  -- Both sides ≡-normalise, then a top-level ~-step
  testRelB₂ : ∀ {n : ℕ} → n + 0 ≤ 1 + (n + 0)
  testRelB₂ = simpRel (quote +-identityʳ ∷ [])
                      (quote n≤1+n ∷ [])
                      (mkRelInfo (quote ≤-trans) (quote ≤-refl))

  -- Two top-level ~-steps chained via relTrans
  testRelB₃ : ∀ {n : ℕ} → n + 0 ≤ 2 + n
  testRelB₃ = simpRel (quote +-identityʳ ∷ [])
                      (quote n≤1+n ∷ [])
                      (mkRelInfo (quote ≤-trans) (quote ≤-refl))

  -- Three top-level ~-steps
  testRelB₄ : ∀ {n : ℕ} → n + 0 ≤ 3 + n
  testRelB₄ = simpRel (quote +-identityʳ ∷ [])
                      (quote n≤1+n ∷ [])
                      (mkRelInfo (quote ≤-trans) (quote ≤-refl))

  -- Double ≡-normalisation on LHS, then two ~-steps
  testRelB₅ : ∀ {n : ℕ} → n + 0 + 0 ≤ 2 + n
  testRelB₅ = simpRel (quote +-identityʳ ∷ [])
                      (quote n≤1+n ∷ [])
                      (mkRelInfo (quote ≤-trans) (quote ≤-refl))

  -- Both sides ≡-normalise (double on LHS), then two ~-steps
  testRelB₆ : ∀ {n : ℕ} → n + 0 + 0 ≤ 2 + (n + 0)
  testRelB₆ = simpRel (quote +-identityʳ ∷ [])
                      (quote n≤1+n ∷ [])
                      (mkRelInfo (quote ≤-trans) (quote ≤-refl))

  -- ** List bag-equality: simpRel over _↭_ (list permutation) **

  open import Data.List.Relation.Binary.Permutation.Propositional
    using (_↭_; ↭-refl; ↭-trans)
  import Data.List.Relation.Binary.Permutation.Propositional.Properties as ↭Prop
  import Data.List.Properties as LP

  -- preprocessDict requires the rule's body (after stripping pis) to be
  -- syntactically _≡_ x y.  LP.++-identity{ˡ/ʳ} expose RightIdentity/LeftIdentity
  -- (a type alias) which reduce doesn't unfold.  Wrappers give direct ≡ bodies.
  private
    list-++-identityˡ : ∀ {a} {A : Set a} (xs : List A) → [] ++ xs ≡ xs
    list-++-identityˡ = LP.++-identityˡ

    list-++-identityʳ : ∀ {a} {A : Set a} (xs : List A) → xs ++ [] ≡ xs
    list-++-identityʳ = LP.++-identityʳ

  -- Option C: ≡-normalise sub-terms, ↭-refl closes
  testBag₁ : ∀ {a} {A : Set a} (xs ys : List A) → (xs ++ []) ++ ys ↭ xs ++ ys
  testBag₁ = simpRel (quote list-++-identityʳ ∷ []) []
                     (mkRelInfo (quote ↭-trans) (quote ↭-refl))

  -- Both sides normalise, ↭-refl closes (exercises sym-subst path in buildRelProof)
  testBag₂ : ∀ {a} {A : Set a} (xs : List A) → [] ++ xs ↭ xs ++ []
  testBag₂ = simpRel (quote list-++-identityˡ ∷ quote list-++-identityʳ ∷ []) []
                     (mkRelInfo (quote ↭-trans) (quote ↭-refl))

  -- Option B: ≡-normalise [] ++ ys → ys in the LHS, then ++-comm
  testBag₃ : ∀ {a} {A : Set a} (xs ys : List A) → xs ++ [] ++ ys ↭ ys ++ xs
  testBag₃ = simpRel (quote list-++-identityˡ ∷ []) (quote ↭Prop.++-comm ∷ [])
                     (mkRelInfo (quote ↭-trans) (quote ↭-refl))

  -- Pure ↭: no ≡-rules, a single ++-comm step
  testBag₄ : ∀ {a} {A : Set a} (xs ys : List A) → xs ++ ys ↭ ys ++ xs
  testBag₄ = simpRel [] (quote ↭Prop.++-comm ∷ [])
                     (mkRelInfo (quote ↭-trans) (quote ↭-refl))

  -- Double ≡-normalisation (two [] elim steps) then one ↭-step
  testBag₅ : ∀ {a} {A : Set a} (xs ys : List A) → xs ++ [] ++ ys ++ [] ↭ ys ++ xs
  testBag₅ = simpRel (quote list-++-identityˡ ∷ quote list-++-identityʳ ∷ [])
                     (quote ↭Prop.++-comm ∷ [])
                     (mkRelInfo (quote ↭-trans) (quote ↭-refl))

  -- ** Abstract monoid setoid: simpRel over _≈_ in an arbitrary monoid M **

  import Algebra.Bundles as AlgB

  module _ {mc mℓ} (M : AlgB.Monoid mc mℓ) where
    -- Rename names from the monoid bundle that shadow top-level definitions
    -- (refl, trans conflict with ≡.refl / ≡.trans; assoc/identity names may
    -- conflict with class-monoid equivalents opened earlier).
    open AlgB.Monoid M
      renaming (refl to M-refl; trans to M-trans; sym to M-sym;
                identityˡ to M-identL; identityʳ to M-identR; assoc to M-assocRL;
                ε to M-ε)

    private
      -- Wrappers give the tactic a stable Name with all module parameters as
      -- hidden arguments; getType + removePis then strips them automatically.
      ≈-refl-M  : ∀ {x} → x ≈ x
      ≈-refl-M  = M-refl

      ≈-trans-M : ∀ {x y z} → x ≈ y → y ≈ z → x ≈ z
      ≈-trans-M = M-trans

      ∙-identR : ∀ x → x ∙ M-ε ≈ x
      ∙-identR = M-identR

      ∙-identL : ∀ x → M-ε ∙ x ≈ x
      ∙-identL = M-identL

      ∙-assocRL : ∀ x y z → (x ∙ y) ∙ z ≈ x ∙ (y ∙ z)
      ∙-assocRL = M-assocRL

    -- Single ≈-step: x ∙ M-ε ≈ x
    testMonoid₁ : ∀ x → x ∙ M-ε ≈ x
    testMonoid₁ = simpRel [] (quote ∙-identR ∷ [])
                          (mkRelInfo (quote ≈-trans-M) (quote ≈-refl-M))

    -- Single ≈-step: M-ε ∙ x ≈ x
    testMonoid₂ : ∀ x → M-ε ∙ x ≈ x
    testMonoid₂ = simpRel [] (quote ∙-identL ∷ [])
                          (mkRelInfo (quote ≈-trans-M) (quote ≈-refl-M))

    -- Two ≈-steps: (x ∙ M-ε) ∙ M-ε ≈ x
    testMonoid₃ : ∀ x → (x ∙ M-ε) ∙ M-ε ≈ x
    testMonoid₃ = simpRel [] (quote ∙-identR ∷ [])
                          (mkRelInfo (quote ≈-trans-M) (quote ≈-refl-M))

    -- Two ≈-steps mixing assoc + identity: ((x ∙ y) ∙ z) ∙ M-ε ≈ x ∙ (y ∙ z)
    testMonoid₄ : ∀ x y z → ((x ∙ y) ∙ z) ∙ M-ε ≈ x ∙ (y ∙ z)
    testMonoid₄ = simpRel [] (quote ∙-identR ∷ quote ∙-assocRL ∷ [])
                          (mkRelInfo (quote ≈-trans-M) (quote ≈-refl-M))

  -- ** Known limitations **
  --
  -- 1. Commutative rules cause divergence.
  --    +-comm rewrites x + y → y + x → x + y → ... and after 100 steps (even)
  --    the two normal forms are x + y and y + x respectively, which do not unify.
  --    FAILS: simp (quote +-comm ∷ []) for  x + y ≡ y + x
  --
  -- 2. Local hypotheses cannot be passed to simp; only global Names are accepted.
  --    FAILS: using  h : x ≡ 0  to prove  x + x ≡ 0
  --
  -- 3. Conditional equations are not supported.
  --    preprocessDict strips all pi-types including hypothesis arrows, so only
  --    unconditional equations  ∀ x₁ … xₙ → lhs ≡ rhs  work correctly.
