-- TODO: support goals other than equalities (e.g., boolean goals via decide)
-- TODO: rewrite under binders

-- Currently requires `--lossy-unification`. To drop that requirement we'd need
-- to implement our own unification (or ask Agda for a lossy `unify` primitive).

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
open import Reflection.QuotedDefinitions
open import Reflection.Tactic
open import Reflection.Utils hiding (args)
open import Reflection.Utils.TCI using (applyWithVisibility)

open import Class.Monoid
open import Class.Monad
open import Class.MonadError

open MonadError ⦃...⦄

-- ** Private helpers

private
  -- Replace the element at position i using a function
  updateAt : ℕ → (A → A) → List A → List A
  updateAt _       _ []       = []
  updateAt zero    f (x ∷ xs) = f x ∷ xs
  updateAt (suc i) f (x ∷ xs) = x ∷ updateAt i f xs

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
      (def (quote _≡_) (hArg _ ∷ hArg _ ∷ vArg lhs ∷ vArg rhs ∷ []) , numArgs) ←
        return (removePis ty)
        where (ty , _) →
          error1 ("Error while preprocessing simp dict: Not an equation: " <+> show ty)
      return record { lhs = lhs ; rhs = rhs ; name = n ; args = numArgs }

-- Find the first matching rule in the dictionary
findAndUnify : EqDict → Term → TC (Maybe (Equation isInst))
findAndUnify d ty = do
  ty ← reduce ty
  res ← traverse
    (λ where eq@record { args = n ; lhs = lhs } →
        matchTerms n ty lhs >>= return ∘ (_, eq)) d
  return (head (extractMatch res))
  where
    extractMatch : List (Maybe (List Term) × Equation notInst) → List (Equation isInst)
    extractMatch []                     = []
    extractMatch ((just xs , eq) ∷ l)  =
      record { Equation eq ; args = xs } ∷ extractMatch l
    extractMatch ((nothing  , _) ∷ l)  = extractMatch l

-- Apply an instantiated equation to produce the proof term
extractRewrite : Equation isInst → TC Term
extractRewrite record { name = n ; args = xs } = applyWithVisibility n xs

-- ** Simplification

-- Build the congruence lambda: λ ◆ → (def/con f args)[args[i] ↦ ◆]
-- Free variables in all args are shifted by 1 under the lambda.
buildCongLambda : Bool → Name → Args Term → ℕ → Term
buildCongLambda isDef f args i =
  let shiftedArgs = map-Args (mapVars suc) args
      newArgs     = updateAt i (λ (arg info _) → arg info (var 0 [])) shiftedArgs
      body        = if isDef then def f newArgs else con f newArgs
  in `λ "◆" ⇒ body

private
  extractEqRhs : Term → TC Term
  extractEqRhs (_ ``≡ rhs) = return rhs
  extractEqRhs ty = error1 ("Expected equality type, got: " <+> show ty)

-- Try a top-level rule match on t.
-- Returns (rhs, proof : t ≡ rhs) if a rule applies.
tryRule : EqDict → Term → TC (Maybe (Term × Term))
tryRule d t = do
  just eq ← findAndUnify d t
    where nothing → return nothing
  proof ← extractRewrite eq
  ty    ← inferType proof >>= normalise
  rhs   ← extractEqRhs ty
  return (just (rhs , proof))

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
        let newArgs = updateAt i (λ (arg info _) → arg info a') args
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
      return (t'' , if isRefl rest then step else quote trans ∙⟦ step ∣ rest ⟧)

-- ** The simp tactic

-- Simplifies both sides of an equality goal using the given lemmas.
-- Proves lhs ≡ rhs when both sides simplify to a common term.
simpTactic : List Name → ITactic
simpTactic names = do
  d  ← preprocessDict names
  ty ← goalTy >>= reduce
  (lhs ``≡ rhs) ← return ty
    where _ → error1 "simp: goal is not a propositional equality"
  (_ , p1) ← simpIter 100 d lhs
  (_ , p2) ← simpIter 100 d rhs
  unifyWithGoal (buildProof p1 p2)
  where
    buildProof : Term → Term → Term
    buildProof p1 p2 =
      if isRefl p1
        then (if isRefl p2 then `refl else quote sym ∙⟦ p2 ⟧)
        else (if isRefl p2 then p1 else quote trans ∙⟦ p1 ∣ quote sym ∙⟦ p2 ⟧ ⟧)

macro
  simp : List Name → Tactic
  simp names = initTacOpts (simpTactic names) defaultTCOptions

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

  -- ** Known limitations **
  --
  -- 1. Commutative rules cause divergence.
  --    +-comm rewrites x + y → y + x → x + y → ... and after 100 steps (even)
  --    the two normal forms are x + y and y + x respectively, which do not unify.
  --    FAILS: simp (quote +-comm ∷ []) for  x + y ≡ y + x
  --
  -- 2. Rewriting under binders is not implemented (see TODO at top).
  --    simpAll only recurses into def/con; lam nodes are opaque.
  --    FAILS: simp (quote +-identityʳ ∷ []) for  (λ x → x + 0) ≡ id
  --
  -- 3. Local hypotheses cannot be passed to simp; only global Names are accepted.
  --    FAILS: using  h : x ≡ 0  to prove  x + x ≡ 0
  --
  -- 4. Conditional equations are not supported.
  --    preprocessDict strips all pi-types including hypothesis arrows, so only
  --    unconditional equations  ∀ x₁ … xₙ → lhs ≡ rhs  work correctly.
