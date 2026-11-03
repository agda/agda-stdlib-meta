{-# OPTIONS --safe --without-K #-}
--------------------------------------------------------------------------------
-- tryConstrs: Try to refine the goal with constructors recursively,
-- applying some other tactic at the leaves
--------------------------------------------------------------------------------

module Tactic.Constrs where

open import Meta.Prelude
open import Meta.Init

open import Data.List

open import Reflection.Tactic
open import Reflection.Utils
open import Reflection.Utils.TCI

open import Class.Functor.Instances
open import Class.Monad
open import Class.MonadError.Instances
open import Class.MonadReader.Instances
open import Class.MonadTC.Instances
open import Class.Traversable

applyConstrToUnknowns : Name → Type → Term
applyConstrToUnknowns n ty = con n (map toUnknown $ argTys ty)
  where
    toUnknown : Arg Type → Arg Type
    toUnknown (arg i _) = arg i unknown

tryConstrsWith' : ℕ → ITactic → ITactic
tryConstrsWith' zero        tac =
  inDebugPath "tryConstrs" $ catch tac (λ _ → error1 "Maximum depth reached!")
tryConstrsWith' (suc depth) tac =
  inDebugPath "tryConstrs" $ catch tac λ _ → do
  inj₁ goal ← reader TCEnv.goal
    where _ → error1 "Goal is not a hole!"
  goalTy ← inferType goal
  debugLog ("Find constructor for type " ∷ᵈ goalTy ∷ᵈ [])
  constrs ← getConstrsForTerm goal
  try (Data.List.map (λ constr → do
      debugLog ("Try constructor " ∷ᵈ proj₁ constr ∷ᵈ " of type: " ∷ᵈ proj₂ constr ∷ᵈ [])
      let t = uncurry applyConstrToUnknowns constr
      t' ← local (λ env → record env { reconstruction = true }) $ checkType t goalTy
      unify goal t'
      debugLog1 "Success!"
      traverse ⦃ Class.Functor.Instances.Functor-List ⦄ (λ t → runWithHole t (tryConstrsWith' depth tac)) (findMetas t')
      return tt)
    constrs)
    (logAndError1 "No constructors were able to solve the goal!")

module _ ⦃ _ : TCOptions ⦄ where
  tryConstrsᵗ : ℕ → Tactic
  tryConstrsᵗ n = initTac $ tryConstrsWith' n (error1 "Leaf reached!")

  macro
    tryConstrsWith = λ n tac → initTac $ tryConstrsWith' n tac
    tryConstrs = tryConstrsᵗ

private
  module Test where
    open import Tactic.Assumption
    open import Tactic.Defaults

    open import Data.Sum
    open import Relation.Binary.PropositionalEquality

    startDebug : ⊤
    startDebug = byTC (debugLog1 "\n\n\n\nTesting 'tryConstrs'\n")

    test₁ : (3 ≡ 3) × (1 + 1 ≡ 2)
    test₁ = tryConstrs 2

    test₂ : ℕ
    test₂ = tryConstrs 2

    _ : test₂ ≡ 0
    _ = refl

    test₃ : (1 ≡ 2) ⊎ (1 ≡ 1)
    test₃ = tryConstrs 2

    test₄ : ∀ {a} {A : Set a} {x y : A} → x ≡ y → (1 ≡ 2) ⊎ (x ≡ y)
    test₄ h = tryConstrsWith 2 assumption'
