-- TODO: support goals other than equalities (e.g., boolean goals via decide)

-- Currently requires `--lossy-unification`. To drop that requirement we'd need
-- to implement our own unification (or ask Agda for a lossy `unify` primitive).

{-# OPTIONS --safe #-}
{-# OPTIONS -v allTactics:100 #-}
{-# OPTIONS --lossy-unification #-}

module Tactic.Simp where

open import Class.DecEq
open import Class.Functor
open import Class.MonadReader.Instances
open import Class.MonadTC.Instances
open import Class.Show
open import Class.Traversable

open import Data.Bool
open import Data.Maybe hiding (_>>=_; map; zip)
open import Data.Unit
open import Data.List
open import Data.Nat
open import Data.Nat.Properties
open import Data.Product hiding (map; zip)
open import Data.String hiding (show; map; head; replicate; _==_; length)
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

  _`$_ : Term → Term → Term
  t `$ t' = quote _$_ ∙⟦ t ∣ t' ⟧

  _`$ⁿ_ : Term → List Term → Term
  t `$ⁿ []       = t
  t `$ⁿ (x ∷ t') = (t `$ x) `$ⁿ t'

  `λⁿ : ℕ → Term → Term
  `λⁿ zero    t = t
  `λⁿ (suc n) t = `λ "" ⇒ `λⁿ n t

  replicateM : {A : Set} → ℕ → TC A → TC (List A)
  replicateM n x = sequence (replicate n x)

  isRefl : Term → Bool
  isRefl (con n []) = n == quote refl
  isRefl _          = false

-- ** Matching

-- Try to unify term t with the template (which has freeVars free variables).
-- Returns the instantiated free variables on success.
matchTerms : (freeVars : ℕ) → Term → Term → TC (Maybe (List Term))
matchTerms fv t templ = runSpeculative do
  metas ← replicateM fv (newMeta unknown)
  debugLog ("Match:\n" ∷ᵈ t ∷ᵈ "\nand\n" ∷ᵈ (`λⁿ fv templ) `$ⁿ metas ∷ᵈ [])
  catch
    (unify t ((`λⁿ fv templ) `$ⁿ metas) >> debugLog1 "Success" >> return (just metas , true))
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
    removePis : Term → Term × ℕ
    removePis (pi _ (abs _ b)) = map₂ suc (removePis b)
    removePis t                = (t , 0)

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
