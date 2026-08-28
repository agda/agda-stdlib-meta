------------------------------------------------------------------------
-- Tests for `Tactic.Solver.Monoid`.

{-# OPTIONS --without-K --safe #-}

module Tactic.Solver.Monoid.Tests where

open import Algebra

open import Data.Bool
open import Data.Bool.Properties
open import Data.List
open import Data.List.Properties
open import Data.Nat
open import Data.Nat.Properties
open import Level using (Level)
open import Relation.Binary.PropositionalEquality

open import Tactic.Solver.Monoid

private variable
  c ℓ a : Level
  A : Set a

------------------------------------------------------------------------
-- Abstract bundles: setoid `_≈_`, operators as stuck projections.

module _ (M : Monoid c ℓ) where
  open Monoid M

  mon-assoc : ∀ x y z → (x ∙ y) ∙ z ≈ x ∙ (y ∙ z)
  mon-assoc = solve-∙ M

  mon-units : ∀ x y → (x ∙ ε) ∙ (ε ∙ y) ≈ x ∙ y
  mon-units = solve-∙ M

  mon-ε : ε ∙ ε ≈ ε
  mon-ε = solve-∙ M

module _ (M : CommutativeMonoid c ℓ) where
  open CommutativeMonoid M

  cmon-comm : ∀ x y z → x ∙ (y ∙ z) ≈ (z ∙ x) ∙ y
  cmon-comm = solve-∙ M

  cmon-units : ∀ x y → (ε ∙ x) ∙ (y ∙ ε) ≈ y ∙ x
  cmon-units = solve-∙ M

module _ (M : IdempotentCommutativeMonoid c ℓ) where
  open IdempotentCommutativeMonoid M

  icmon-idem : ∀ x y → x ∙ (y ∙ x) ≈ x ∙ y
  icmon-idem = solve-∙ M

  icmon-many : ∀ x y → (x ∙ y) ∙ (y ∙ x) ∙ x ≈ x ∙ (y ∙ ε)
  icmon-many = solve-∙ M

------------------------------------------------------------------------
-- Concrete bundles.

nat-+-unit : ∀ x → (x + 0) + 0 ≡ 0 + x
nat-+-unit = solve-∙ +-0-monoid

list-++-unit : ∀ (xs ys : List A) → (xs ++ []) ++ ys ≡ xs ++ ([] ++ ys)
list-++-unit {A = A} = solve-∙ (++-monoid A)

bool-∨-unit : ∀ x y → (x ∨ false) ∨ (false ∨ y) ≡ x ∨ y
bool-∨-unit = solve-∙ ∨-idempotentCommutativeMonoid

nat-+-assoc : ∀ x y z w → ((x + y) + z) + w ≡ x + ((y + z) + w)
nat-+-assoc = solve-∙ +-0-monoid

nat-+-comm : ∀ x y z → x + (y + z) ≡ (z + x) + y
nat-+-comm = solve-∙ +-0-commutativeMonoid

-- Compound atoms are kept exactly as written: `x + y` and `x ∧ y` are
-- opaque atoms for the `⊔`/`∨` theories.
nat-⊔-atoms : ∀ x y z w → ((x + y) ⊔ z) ⊔ w ≡ (x + y) ⊔ (z ⊔ w)
nat-⊔-atoms = solve-∙ ⊔-0-monoid

bool-∨-idem : ∀ x y z → (x ∨ (y ∧ z)) ∨ ((y ∧ z) ∨ x) ≡ x ∨ (y ∧ z)
bool-∨-idem = solve-∙ ∨-idempotentCommutativeMonoid

list-++-assoc : ∀ (xs ys zs : List A) → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
list-++-assoc {A = A} = solve-∙ (++-monoid A)

------------------------------------------------------------------------
-- Goals under a pi-prefix with hidden binders.

hidden-binders : ∀ {x : ℕ} (y : ℕ) {z : ℕ} → (x + y) + z ≡ x + (y + z)
hidden-binders = solve-∙ +-0-monoid

------------------------------------------------------------------------
-- Regression test: A solver call whose expected type is still a
-- metavariable when the macro first runs.

module _ (M : Monoid c ℓ) where
  open Monoid M

  blocked-goal : (x : Carrier) → ℕ
  blocked-goal x = length (solve-∙ M ∷ identityˡ x ∷ [])
