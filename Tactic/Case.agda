{-# OPTIONS --safe --without-K #-}
{-# OPTIONS -v allTactics:100 #-}
module Tactic.Case where

open import Data.Sum
open import Data.List
open import Data.Product
open import Function
open import Data.Maybe using (Maybe; just; from-just)

open import Tactic.Helpers
open import Tactic.ClauseBuilder

open import Generics

open import Reflection.Syntax
open import Class.Functor
open import Class.Monad
open import Class.MonadTC
open import Reflection.TCI

open import Meta

open MonadTC ⦃...⦄

instance
  _ = MonadTC-TCI
  _ = ContextMonad-MonadTC
  _ = Functor-M

open ClauseExprM

matchInductive : Type → (SinglePattern → TC (ClauseExpr ⊎ Maybe Term)) → TC ClauseExpr
matchInductive ty rhs = do
  ps ← constructorPatterns' ty
  matchExprM (Data.List.map (λ p → p , rhs p) ps)

genMatchingClauses : Type → TC Term → TC ClauseExpr
genMatchingClauses ty x = matchInductive ty (λ _ → (inj₂ ∘ just) <$> x)

-- apply tac to all holes
case : ∀ {a} {A : Set a} → A → ITactic → ITactic
case a tac = inDebugPath "case" do
  t ← quoteTC a
  ty ← inferType t
  unifyWithGoal =<< caseMatch t (genMatchingClauses ty (withGoalHole tac))

private
  module Test (A B : Set) where
    open import Tactic.Assumption
    open import Tactic.Defaults

    record TestType : Set where
      field
        a : A
        b : B

    test₁ : A × B → A
    test₁ x = by (case x assumption')

    test₂ : A × B → B
    test₂ x = by (case x assumption')

    test₃ : A ⊎ A → A
    test₃ x = by (case x assumption')

    test₄ : TestType → A
    test₄ x = by (case x assumption')

    test₅ : TestType → B
    test₅ x = by (case x assumption')
