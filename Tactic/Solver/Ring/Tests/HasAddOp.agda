{-# OPTIONS --without-K --safe #-}

------------------------------------------------------------------------
-- Goals whose `_+_` is `Class.HasAdd._+_` rather than the bundle's
-- own addition.
------------------------------------------------------------------------

module Tactic.Solver.Ring.Tests.HasAddOp where

open import Algebra using (CommutativeSemiring; CommutativeRing)
open import Class.HasAdd
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Tactic.Solver.Ring using (solve-≈)

------------------------------------------------------------------------
-- Concrete carriers, via the stdlib `HasAdd` instances.

module ℕ where
  open import Data.Nat using (ℕ)
  open import Data.Nat.Properties using (+-*-commutativeSemiring)

  comm : ∀ (a b : ℕ) → a + b ≡ b + a
  comm a b = solve-≈ +-*-commutativeSemiring

  assoc : ∀ (a b c : ℕ) → (a + b) + c ≡ a + (b + c)
  assoc a b c = solve-≈ +-*-commutativeSemiring

  rearrange : ∀ (a b c d : ℕ) → (a + b) + (c + d) ≡ (d + c) + (b + a)
  rearrange a b c d = solve-≈ +-*-commutativeSemiring

module ℤ where
  open import Data.Integer using (ℤ)
  open import Data.Integer.Properties using (+-*-commutativeRing)

  comm : ∀ (a b : ℤ) → a + b ≡ b + a
  comm a b = solve-≈ +-*-commutativeRing

  rearrange : ∀ (a b c : ℤ) → a + (b + c) ≡ c + (a + b)
  rearrange a b c = solve-≈ +-*-commutativeRing

module ℚ where
  open import Data.Rational using (ℚ)
  import Data.Rational.Properties as ℚP

  comm : ∀ (a b : ℚ) → a + b ≡ b + a
  comm a b = solve-≈ ℚP.+-*-commutativeRing

------------------------------------------------------------------------
-- Abstract bundles, via a `HasAdd Carrier` instance built from the
-- bundle's own addition.

module AbstractCSR {c ℓ} (R : CommutativeSemiring c ℓ) where
  open CommutativeSemiring R using (Carrier; _≈_) renaming (_+_ to _+ᵇ_)

  instance
    hasAdd : HasAdd Carrier
    hasAdd ._+_ = _+ᵇ_

  comm : ∀ a b → (a + b) ≈ (b + a)
  comm a b = solve-≈ R

  assoc : ∀ a b c → ((a + b) + c) ≈ (a + (b + c))
  assoc a b c = solve-≈ R

  rearrange : ∀ a b c d → ((a + b) + (c + d)) ≈ ((d + c) + (b + a))
  rearrange a b c d = solve-≈ R

module AbstractCR {c ℓ} (R : CommutativeRing c ℓ) where
  open CommutativeRing R using (Carrier; _≈_) renaming (_+_ to _+ᵇ_)

  instance
    hasAdd : HasAdd Carrier
    hasAdd ._+_ = _+ᵇ_

  comm : ∀ a b → (a + b) ≈ (b + a)
  comm a b = solve-≈ R

  assoc : ∀ a b c → ((a + b) + c) ≈ (a + (b + c))
  assoc a b c = solve-≈ R
