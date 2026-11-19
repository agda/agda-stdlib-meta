-- Need a dictionary of theorems. How to extend it?
-- What's a reasonable strategy to rewrite with? How much should we reduce?
-- Currently requires `--lossy-unification`. To drop that requirement, we'd need to implement our own unification (or ask for Agda to give us a lossy `unify` TC primitive).
-- TODO: rewrite multiple times
-- TODO: rewrite subexpressions

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

open import Data.String hiding (show; map; head; replicate; _==_; length) renaming (_++_ to _++S_)

open import Function

open import Relation.Binary.PropositionalEquality

open import Meta.Init
open import Reflection.Utils hiding (args)
open import Reflection.Tactic

open import Effect.Monad.State
open import Effect.Monad

open import Class.Monoid
open import Class.Monad
open import Class.MonadError

open import Reflection.Utils.TCI using (applyWithVisibility)

open import Meta.Prelude

open MonadError ⦃...⦄

_`$_ : Term → Term → Term
t `$ t' = quote _$_ ∙⟦ t ∣ t' ⟧

_`$ⁿ_ : Term → List Term → Term
t `$ⁿ []       = t
t `$ⁿ (x ∷ t') = (t `$ x) `$ⁿ t'

`λⁿ : ℕ → Term → Term
`λⁿ zero    t = t
`λⁿ (suc n) t = `λ "" ⇒ `λⁿ n t

NDict = List Name

testDict : NDict
testDict = quote +-assoc ∷ quote +-identityˡ ∷ quote +-identityʳ ∷ []

-- traverseState : {A B S : Set} → (A → State S B) → List A → State S (List B)
-- traverseState = {!!}

-- Matchee → Template → Maybe (List Term)

replicateM : {A : Set} → ℕ → TC A → TC (List A)
replicateM n x = sequence (replicate n x)

matchTerms : (freeVars : ℕ) → Term → Term → TC (Maybe (List Term))
matchTerms fv t templ = runSpeculative do
  metas ← replicateM fv (newMeta unknown)
  debugLog1 t
  --extendContext' (zipWithIndex (λ i x → (("x" ++S show i) , vArg x)) metas) do
  debugLog ("Match:\n" ∷ᵈ t ∷ᵈ "\nand\n" ∷ᵈ (`λⁿ fv templ) `$ⁿ metas ∷ᵈ [])
  catch
    (unify t ((`λⁿ fv templ) `$ⁿ metas) >> debugLog1 "Success" >> return (just metas , true))
    (λ _ → return (nothing , false))

-- case runState (helper 0 fv t templ) (replicate fv nothing) of λ where
--     (s , true)  → nothing -- term/variable assignment conflict
--     (s , false) → let res = catMaybes s in if length res == fv then just res else nothing
--   where
--     open RawMonad (monad {S = List (Maybe Term)}) hiding (zip)

    -- helper : ℕ → (freeVars : ℕ) → Term → Term → State (List (Maybe Term)) Bool
    -- helper n fv (var x args) (var x₁ args₁) = {!traverse!}
    -- helper n fv (con c args) (con c₁ args₁) = if (c == c₁) ∧ (length args == length args₁)
    --   then (do
    --     traverseState {!(λ where (arg _ t , arg _ t') → helper n fv t t')!} (zip args args₁)
    --     return false)
    --   else return true
    -- helper n fv (def f args) (def f₁ args₁) = {!!}
    -- helper n fv (lam v t) (lam v₁ t₁) = {!!}
    -- helper n fv (pat-lam cs args) (pat-lam cs₁ args₁) = {!!}
    -- helper n fv (pi a b) (pi a₁ b₁) = {!!}
    -- helper n fv (sort s) (sort s₁) = {!!}
    -- helper n fv (lit l) (lit l₁) = {!!}
    -- helper n fv (meta x x₁) (meta x₂ x₃) = {!!}
    -- helper n fv unknown unknown = return false
    -- helper n fv _ _ = return true

data Instantiated : Set where
  isInst notInst : Instantiated

Instantiation : Instantiated → Set
Instantiation isInst  = List Term
Instantiation notInst = ℕ

record Equation (i : Instantiated) : Set where
  field lhs rhs : Term
        name : Name
        args : Instantiation i

EqDict = List (Equation notInst)

preprocessDict : NDict → TC EqDict
preprocessDict d = traverse genEq d
  where
   removePis : Term → Term × ℕ
   removePis (pi a (abs _ b)) = map₂ suc (removePis b)
   removePis t = (t , 0)

   genEq : Name → TC (Equation notInst)
   genEq n = do
     ty ← getType n >>= reduce
     (def (quote _≡_) (hArg l ∷ hArg T ∷ vArg lhs ∷ vArg rhs ∷ []) , args) ← return $ removePis ty
       where (ty , _) → error1 ("Error while preprocessing simp dict: Not an equation:" <+> show ty)
     return record { lhs = lhs ; rhs = rhs ; name = n ; args = args }

-- look up a rule in the dictionary & unify with a given type
findAndUnify : EqDict → Type → TC (Maybe (Equation isInst))
findAndUnify d ty = do
  ty ← reduce ty
  res ← traverse (λ where eq@record { args = args ; lhs = lhs } → matchTerms args ty lhs >>= return ∘ (_, eq)) d
  return $ head (extractMatch res)
  where
    extractMatch : List (Maybe (List Term) × Equation notInst) → List (Equation isInst)
    extractMatch [] = []
    extractMatch ((just x , eq) ∷ l) = (record { Equation eq ; args = x }) ∷ extractMatch l
    extractMatch ((nothing , _) ∷ l) = extractMatch l

extractRewrite : Equation isInst → TC Term
extractRewrite record { name = n ; args = a } = applyWithVisibility n a

simp1Test : EqDict → Type → TC ⊤
simp1Test d ty = do
  just res ← findAndUnify d ty
    where nothing → error1 "Couldn't find a rewrite rule!"
  res ← extractRewrite res
  debugLog1 res
  unifyWithGoal res

private
  open import Tactic.Derive.TestTypes
  open import Tactic.Defaults

  testDict' : EqDict
  testDict' = byTC (preprocessDict testDict)

  testTerm : ℕ → ℕ → Term
  testTerm x y = quoteTerm ((x + 0) + y)

  testTerm' : ℕ → ℕ → Term
  testTerm' x y = quoteTerm (x + (0 + y))

  test : ∀ {x y : ℕ} → (x + 0) + y ≡ x + (0 + y)
  test {x} {y} = by (simp1Test testDict' (quoteTerm ((x + 0) + y)))
