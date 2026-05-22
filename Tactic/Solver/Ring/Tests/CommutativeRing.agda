{-# OPTIONS --safe --without-K #-}

module Tactic.Solver.Ring.Tests.CommutativeRing where

open import Algebra using (CommutativeRing)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Tactic.Solver.Ring using (solve-≈)

------------------------------------------------------------------------
-- Concrete ℤ.

module TestsℤCRConcrete where
  open import Data.Integer using (+_)
  open import Data.Integer.Properties using (+-*-commutativeRing)
  open CommutativeRing +-*-commutativeRing using (_≈_; _+_; _*_; _-_; -_)

  comm+ : ∀ a b → (a + b) ≈ (b + a)
  comm+ = solve-≈ +-*-commutativeRing

  assoc* : ∀ a b c → ((a * b) * c) ≈ (a * (b * c))
  assoc* = solve-≈ +-*-commutativeRing

  distrib-test : ∀ a b c → a * (b + c) ≈ a * b + a * c
  distrib-test = solve-≈ +-*-commutativeRing

  neg-comm : ∀ a b → - (a + b) ≈ - a + - b
  neg-comm = solve-≈ +-*-commutativeRing

  neg-double : ∀ a → - (- a) ≈ a
  neg-double = solve-≈ +-*-commutativeRing

  sub-as-add-neg : ∀ a b → a - b ≈ a + (- b)
  sub-as-add-neg = solve-≈ +-*-commutativeRing

  distrib-over-sub : ∀ a b c → a * (b - c) ≈ a * b - a * c
  distrib-over-sub = solve-≈ +-*-commutativeRing

  cancel-sub : ∀ a → a - a ≈ (+ 0)
  cancel-sub = solve-≈ +-*-commutativeRing

  lit-add : (+ 1) + (+ 1) ≈ (+ 2)
  lit-add = solve-≈ +-*-commutativeRing

  comm+-lit : ∀ a → (a + (+ 1)) ≈ ((+ 1) + a)
  comm+-lit = solve-≈ +-*-commutativeRing

------------------------------------------------------------------------
-- Abstract `CommutativeRing`.

module TestsAbstractCR {c ℓ} (R : CommutativeRing c ℓ) where
  open CommutativeRing R

  comm+ : ∀ a b → (a + b) ≈ (b + a)
  comm+ = solve-≈ R

  assoc+ : ∀ a b c → ((a + b) + c) ≈ (a + (b + c))
  assoc+ = solve-≈ R

  comm* : ∀ a b → (a * b) ≈ (b * a)
  comm* = solve-≈ R

  assoc* : ∀ a b c → ((a * b) * c) ≈ (a * (b * c))
  assoc* = solve-≈ R

  distrib-test : ∀ a b c → a * (b + c) ≈ a * b + a * c
  distrib-test = solve-≈ R

  zero-add : ∀ a → 0# + a ≈ a
  zero-add = solve-≈ R

  one-mul : ∀ a → 1# * a ≈ a
  one-mul = solve-≈ R

  zero-mul : ∀ a → 0# * a ≈ 0#
  zero-mul = solve-≈ R

  one-mul' : ∀ a → a * 1# ≈ a
  one-mul' = solve-≈ R

  neg-self : ∀ a → - a ≈ - a
  neg-self = solve-≈ R

  neg-zero : - 0# ≈ 0#
  neg-zero = solve-≈ R

  neg-double : ∀ a → - (- a) ≈ a
  neg-double = solve-≈ R

  neg-comm : ∀ a b → - (a + b) ≈ - a + - b
  neg-comm = solve-≈ R

  add-inverse-right : ∀ a → a + (- a) ≈ 0#
  add-inverse-right = solve-≈ R

  add-inverse-left : ∀ a → (- a) + a ≈ 0#
  add-inverse-left = solve-≈ R

  sub-self : ∀ a → a - a ≈ 0#
  sub-self = solve-≈ R

  sub-as-add-neg : ∀ a b → a - b ≈ a + (- b)
  sub-as-add-neg = solve-≈ R

  sub-comm-via-neg : ∀ a b → a - b ≈ - (b - a)
  sub-comm-via-neg = solve-≈ R

  distrib-over-sub : ∀ a b c → a * (b - c) ≈ a * b - a * c
  distrib-over-sub = solve-≈ R

  binomial-neg : ∀ a b → (a - b) * (a + b) ≈ a * a - b * b
  binomial-neg = solve-≈ R

  perfect-square-neg : ∀ a b → (a - b) * (a - b) ≈ (a * a - (1# + 1#) * a * b) + b * b
  perfect-square-neg = solve-≈ R

  neg-distrib-mul : ∀ a b → (- a) * b ≈ - (a * b)
  neg-distrib-mul = solve-≈ R

  neg-times-neg : ∀ a b → (- a) * (- b) ≈ a * b
  neg-times-neg = solve-≈ R
