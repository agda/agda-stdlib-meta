{-# OPTIONS --safe --without-K #-}
--------------------------------------------------------------------------------
-- assumption: try to solve the goal with one of the available assumptions
--------------------------------------------------------------------------------

module Tactic.Assumption where

open import Meta.Prelude
open import Meta.Init

open import Class.Functor
open import Class.Monad
open import Class.MonadError.Instances
open import Class.MonadReader.Instances
open import Class.MonadTC.Instances

open import Reflection.Tactic
open import Reflection.Utils
open import Reflection.Utils.TCI

instance _ = Functor-M

assumption' : ITactic
assumption' = inDebugPath "assumption" do
  c ← getContext
  foldl (λ x k → do
    catch (unifyWithGoal (♯ k) >> debugLog ("Success with: " ∷ᵈ ♯ k ∷ᵈ [])) (λ _ → x))
    (logAndError1 "No valid assumption!") (downFrom $ length c)

module _ ⦃ _ : TCOptions ⦄ where
  macro
    assumption = initTac assumption'
    assumptionOpts = initTacOpts assumption'

private
  open import Tactic.Defaults
  module Test where
    test₁ : {A B : Set} → A → B → A
    test₁ a b = assumption

    test₂ : {A B : Set} → A → B → B
    test₂ a b = assumption
