------------------------------------------------------------------------
-- Side-by-side comparison of `solve-≈` against the stdlib's
-- ring-solver variants.  Each feature shows a working `solve-≈`
-- test and the closest stdlib equivalent (either active or
-- commented out, with the error if uncommented).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Tactic.Solver.Ring.Tests.Comparison where

open import Algebra using (CommutativeSemiring)
open import Data.Nat.Properties                        using (+-*-commutativeSemiring)
import Data.Integer.Properties                         as ℤP
open import Data.List                                  using (_∷_; [])
open import Relation.Binary using (Setoid)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Tactic.Solver.Ring using (solve-≈)
import Data.Nat.Tactic.RingSolver                      as NatSolver
import Data.Integer.Tactic.RingSolver                  as ℤSolver
import Algebra.Solver.Ring.NaturalCoefficients.Default as NCD

------------------------------------------------------------------------
-- Feature 1.  Abstract rings.
--
-- Stdlib's reflective `solve-∀` takes a top-level `Name`; module
-- parameters can't be `quote`-d.

module ParamRing-ours {c ℓ} (R : CommutativeSemiring c ℓ) where
  open CommutativeSemiring R

  comm+ : ∀ a b → a + b ≈ b + a
  comm+ = solve-≈ R

module ParamRing-stdlib {c ℓ} (R : CommutativeSemiring c ℓ) where
  open NCD R
  open CommutativeSemiring R
  private module Eq = Setoid setoid

  -- comm+ : ∀ a b → a + b ≈ b + a
  -- comm+ = RS.solve-∀ R

  -- Workaround: the non-reflective polynomial solver, with the AST
  -- built by hand.
  comm+-explicit : ∀ a b → a + b ≈ b + a
  comm+-explicit = solve 2 (λ a b → a :+ b := b :+ a) Eq.refl

------------------------------------------------------------------------
-- Feature 2.  Auto-quantification.
--
-- Stdlib has two macros — `solve-∀` for `∀-`bound goals and `solve`
-- for equations with an explicit variable list — and requires the
-- user to pick the right one. `solve-≈` uses a single call shape for
-- all three forms below.

module AutoQuant-ours {c ℓ} (R : CommutativeSemiring c ℓ) where
  open CommutativeSemiring R
  open import Relation.Binary.Reasoning.Setoid setoid

  -- a) Pi-bound goal, no variables bound
  closed-∀ : ∀ a b → a + b ≈ b + a
  closed-∀ = solve-≈ R

  -- b) Some variables bound
  with-patterns : ∀ a b → a + b ≈ b + a
  with-patterns a = solve-≈ R

module AutoQuant-stdlib where
  open import Data.Nat using (_+_; _*_)

  -- (a) ∀-bound: `solve-∀` works.
  closed-∀ : ∀ a b → a + b ≡ b + a
  closed-∀ = NatSolver.solve-∀

  -- (b) Patterns introduced: must switch to `solve` + variable list.
  with-patterns : ∀ a b → a + b ≡ b + a
  with-patterns a b = NatSolver.solve (a ∷ b ∷ [])

------------------------------------------------------------------------
-- Feature 3.  Concrete-ring bundles.
--
-- Stdlib ships one preconfigured wrapper per carrier
-- (`Data.Nat.Tactic.RingSolver`, `Data.Integer.Tactic.RingSolver`,
-- `Data.Rational.Tactic.RingSolver`, …). `solve-≈` is a single macro
-- that handles all of them.

module ConcreteRings-ours where
  -- ℕ
  module ℕcase where
    open import Data.Nat using (_+_; _*_)
    distrib : ∀ a b c → a * (b + c) ≡ a * b + a * c
    distrib = solve-≈ +-*-commutativeSemiring

  -- ℤ
  module ℤcase where
    open import Data.Integer using (_+_; _*_)
    open CommutativeSemiring ℤP.+-*-commutativeSemiring using (_≈_)
    assoc* : ∀ a b c → ((a * b) * c) ≈ (a * (b * c))
    assoc* = solve-≈ ℤP.+-*-commutativeSemiring

  -- ℤ with operators projected from the bundle.
  module ℤbundle where
    open CommutativeSemiring ℤP.+-*-commutativeSemiring
    assoc* : ∀ a b c → ((a * b) * c) ≈ (a * (b * c))
    assoc* = solve-≈ ℤP.+-*-commutativeSemiring

module ConcreteRings-stdlib where
  -- ℕ-specific wrapper
  module ℕcase where
    open import Data.Nat using (_+_; _*_)
    distrib : ∀ a b c → a * (b + c) ≡ a * b + a * c
    distrib = NatSolver.solve-∀

  -- ℤ-specific wrapper (separate import)
  module ℤcase where
    open import Data.Integer using (_+_; _*_)
    assoc* : ∀ a b c → ((a * b) * c) ≡ (a * (b * c))
    assoc* = ℤSolver.solve-∀

------------------------------------------------------------------------
-- Feature 4.  The stdlib solver just fails on some goals.
--
-- Under certain circumstances, the stdlib solver doesn't reduce
-- enough, leading to it not being able to solve some equations.

module CongChain-ours where
  open import Data.Nat using (_+_)
  open CommutativeSemiring +-*-commutativeSemiring using (_≈_; +-congˡ; +-comm; trans)

  trans-congˡ : ∀ a b c → a + (b + c) ≈ (a + c) + b
  trans-congˡ a b c = trans (+-congˡ {x = a} (+-comm b c)) (solve-≈ +-*-commutativeSemiring)

  -- stdlib's `solve` fails with `a != a + c of type ℕ`.
  -- trans-congˡ-stdlib : ∀ a b c → a + (b + c) ≈ (a + c) + b
  -- trans-congˡ-stdlib a b c = trans (+-congˡ {x = a} (+-comm b c))
  --                              (NatSolver.solve (a ∷ c ∷ b ∷ []))
