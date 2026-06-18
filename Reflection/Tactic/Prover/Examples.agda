------------------------------------------------------------------------
-- Worked examples for `Reflection.Tactic.Prover`.
--
-- Each example demonstrates one of the three failure modes and that
-- the typechecker state is left pristine.

{-# OPTIONS --without-K --safe #-}

module Reflection.Tactic.Prover.Examples where

open import Data.Bool    using (Bool; true; false)
open import Data.List    using (List; []; _∷_)
open import Data.Maybe   using (Maybe; just; nothing)
open import Data.Nat     using (ℕ)
open import Data.Product using (Σ; _,_)
open import Data.Unit    using (⊤; tt)
open import Function     using (case_of_)

open import Agda.Builtin.Equality   using (_≡_; refl)
open import Agda.Builtin.Reflection using (runSpeculative)
open import Reflection
open import Reflection.TCM.Syntax

open import Reflection.Tactic.Prover

private
  -- A value whose type has an implicit that elaboration cannot pin.
  metaArg : {n : ℕ} → ℕ
  metaArg {n} = n

  -- A type with no instance in scope.
  data NoInst : Set where

------------------------------------------------------------------------
-- 1. Failure by *throwing*.

macro
  catch-rolls-back-throw : Term → TC ⊤
  catch-rolls-back-throw hole = do
    nothing ← proveByRefl (quoteTerm (1 ≡ 0))
      where (just _) → typeError (strErr "refl cannot prove 1 ≡ 0" ∷ [])
    just pf ← proveByRefl (quoteTerm (0 ≡ 0))
      where nothing → typeError (strErr "refl should prove 0 ≡ 0" ∷ [])
    unify hole pf

_ : 0 ≡ 0
_ = catch-rolls-back-throw

------------------------------------------------------------------------
-- 2. Failure by *leaving an unsolved metavariable*.

macro
  settle-rejects-unsolved : Term → TC ⊤
  settle-rejects-unsolved hole = do
    nothing ← tryElabAs (def (quote metaArg) []) (quoteTerm ℕ)
      where (just _) → typeError (strErr "settle should reject the unsolved meta" ∷ [])
    unify hole (quoteTerm tt)

_ : ⊤
_ = settle-rejects-unsolved

------------------------------------------------------------------------
-- 3. Failure by a *deferred instance constraint*.

macro
  settle-forces-instances : Term → TC ⊤
  settle-forces-instances hole = do
    nothing ← proveByInstance (quoteTerm NoInst)
      where (just _) → typeError (strErr "no NoInst instance exists" ∷ [])
    unify hole (quoteTerm tt)

_ : ⊤
_ = settle-forces-instances

-- And the positive case: when an instance *does* exist, it is found.
private instance
  ⊤-inst : ⊤
  ⊤-inst = tt

macro
  instance-found : Term → TC ⊤
  instance-found hole = do
    just pf ← proveByInstance (quoteTerm ⊤)
      where nothing → typeError (strErr "should find the ⊤ instance" ∷ [])
    unify hole pf

_ : ⊤
_ = instance-found

------------------------------------------------------------------------
-- 4. `tryUnifyAs` is required for dependent pairs.

macro
  needs-tryUnifyAs : Term → TC ⊤
  needs-tryUnifyAs hole = do
    goalTy ← inferType hole
    let cand = con (quote _,_) (vArg (var 1 []) ∷ vArg (var 0 []) ∷ [])
    nothing ← tryElabAs cand goalTy
      where (just _) → typeError (strErr "tryElabAs unexpectedly succeeded" ∷ [])
    just pf ← tryUnifyAs cand goalTy
      where nothing → typeError (strErr "tryUnifyAs should pin B and succeed" ∷ [])
    unify hole pf

dependentPair : {A : Set} {B : A → Set} (w : A) (h : B w) → Σ A B
dependentPair w h = needs-tryUnifyAs
