{-# OPTIONS --safe --without-K #-}

------------------------------------------------------------------------
-- Frontend edge cases: goal shapes and bundle shapes beyond the basic
-- Equations matrix. Each module probes one mechanism of the macro
-- frontend (goal whnf-stripping, atom identity, literal recognition,
-- binder handling, bundle resolution).
------------------------------------------------------------------------

module Tactic.Solver.Ring.Tests.EdgeCases where


open import Algebra using (CommutativeRing; CommutativeSemiring)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Tactic.Solver.Ring using (solve-≈)

------------------------------------------------------------------------
-- 1. Goal type behind a definition (whnf must unfold the alias).

module GoalTypeAlias where
  open import Data.Nat using (ℕ; _+_)
  open import Data.Nat.Properties using (+-*-commutativeSemiring)

  Goal : ℕ → ℕ → Set
  Goal a b = a + b ≡ b + a

  test : ∀ a b → Goal a b
  test a b = solve-≈ +-*-commutativeSemiring

------------------------------------------------------------------------
-- 2. Goal *side* behind a definition (whnf must unfold to expose ops).

module GoalSideAlias where
  open import Data.Nat using (ℕ; _+_)
  open import Data.Nat.Properties using (+-*-commutativeSemiring)

  myExpr : ℕ → ℕ → ℕ
  myExpr a b = a + b

  test : ∀ a b → myExpr a b ≡ b + a
  test a b = solve-≈ +-*-commutativeSemiring

------------------------------------------------------------------------
-- 3. Ops exposed only by computation (foldr over a concrete list).

module FoldrExposed where
  open import Data.Nat using (ℕ; _+_)
  open import Data.Nat.Properties using (+-*-commutativeSemiring)
  open import Data.List using (foldr; _∷_; [])

  test : ∀ a b → foldr _+_ 0 (a ∷ b ∷ []) ≡ b + a
  test a b = solve-≈ +-*-commutativeSemiring

------------------------------------------------------------------------
-- 4. Hidden and mixed-visibility pi binders.

module HiddenPis where
  open import Data.Nat using (ℕ; _+_)
  open import Data.Nat.Properties using (+-*-commutativeSemiring)

  hidden : ∀ {a b} → a + b ≡ b + a
  hidden = solve-≈ +-*-commutativeSemiring

  mixed : ∀ {a} b → a + b ≡ b + a
  mixed = solve-≈ +-*-commutativeSemiring

------------------------------------------------------------------------
-- 5. `0#`/`1#` written as projections of a *concrete* bundle.

module ProjectionLiterals where
  open import Data.Nat using (ℕ)
  open import Data.Nat.Properties using (+-*-commutativeSemiring)
  open CommutativeSemiring +-*-commutativeSemiring using (_≈_; _*_; _+_; 1#; 0#)

  one-mul : ∀ a → 1# * a ≈ a
  one-mul a = solve-≈ +-*-commutativeSemiring

  zero-add : ∀ a → 0# + a ≈ a
  zero-add a = solve-≈ +-*-commutativeSemiring

------------------------------------------------------------------------
-- 6. Same, on ℚ (projection must stop at the blocked literal name).

module ProjectionLiteralsℚ where
  import Data.Rational.Properties as ℚP
  open CommutativeRing ℚP.+-*-commutativeRing using (_≈_; _*_; 1#)

  one-mul : ∀ q → 1# * q ≈ q
  one-mul q = solve-≈ ℚP.+-*-commutativeRing

------------------------------------------------------------------------
-- 7. Concrete ℚ subtraction and negation (CR side; `_-_` is a
-- derived slot and must be matched via unfolding).

module ℚSubNeg where
  open import Data.Rational using (ℚ; 0ℚ; _+_; _*_; _-_; -_)
  import Data.Rational.Properties as ℚP

  sub-comm : ∀ p q → p - q ≡ - q + p
  sub-comm p q = solve-≈ ℚP.+-*-commutativeRing

  neg-zero : - 0ℚ ≡ 0ℚ
  neg-zero = solve-≈ ℚP.+-*-commutativeRing

  neg-distrib : ∀ p q → - (p + q) ≡ - p - q
  neg-distrib p q = solve-≈ ℚP.+-*-commutativeRing

------------------------------------------------------------------------
-- 8. Negation applied to a literal (CR ℤ).

module NegLiteral where
  open import Data.Integer using (ℤ; +_; _+_; _*_; -_)
  open import Data.Integer.Properties using (+-*-commutativeRing)

  neg-lit : ∀ a → - (+ 1) * a ≡ - a
  neg-lit a = solve-≈ +-*-commutativeRing

------------------------------------------------------------------------
-- 9. ℤ literal *aliases* (`0ℤ`, `1ℤ` unfold to `+ 0`, `+[1+ 0 ]`).

module ℤLiteralAliases where
  open import Data.Integer using (ℤ; 0ℤ; 1ℤ; +_; _+_; _*_)
  open import Data.Integer.Properties using (+-*-commutativeSemiring)

  one-mul : ∀ a → 1ℤ * a ≡ a
  one-mul a = solve-≈ +-*-commutativeSemiring

  zero-add : ∀ a → 0ℤ + a ≡ a
  zero-add a = solve-≈ +-*-commutativeSemiring

  two : 1ℤ + 1ℤ ≡ + 2
  two = solve-≈ +-*-commutativeSemiring

------------------------------------------------------------------------
-- 10. ℕ: zero-annihilation with bare literals.

module ℕZero where
  open import Data.Nat using (ℕ; _+_; _*_)
  open import Data.Nat.Properties using (+-*-commutativeSemiring)

  zero-mul : ∀ a → a * 0 ≡ 0
  zero-mul a = solve-≈ +-*-commutativeSemiring

------------------------------------------------------------------------
-- 11. Bundle written inline at the call site (accessor application,
-- no top-level alias).

module InlineAccessor where
  open import Data.Rational using (ℚ; 1ℚ; _+_; _*_)
  import Data.Rational.Properties as ℚP

  one-mul : ∀ q → q * 1ℚ ≡ q
  one-mul q = solve-≈ (CommutativeRing.commutativeSemiring ℚP.+-*-commutativeRing)

------------------------------------------------------------------------
-- 12. Bundle defined in a where-clause (lifted, applied to module
-- params; record expressions there are copattern definitions too).

module WhereBundle where
  open import Data.Integer as ℤ using (ℤ)
  import Data.Integer.Properties as ℤP

  test : ∀ (a b : ℤ) → a ℤ.+ b ≡ b ℤ.+ a
  test a b = solve-≈ myR
    where
      myR : CommutativeSemiring _ _
      myR = record
        { Carrier = ℤ ; _≈_ = _≡_
        ; _+_ = ℤ._+_ ; _*_ = ℤ._*_
        ; 0# = ℤ.+ 0 ; 1# = ℤ.+ 1
        ; isCommutativeSemiring = ℤP.+-*-isCommutativeSemiring
        }

------------------------------------------------------------------------
-- 13. Moderately large ℕ literal (encodeNat currently builds a
-- suc-chain Term of that depth).

module BigLiteral where
  open import Data.Nat using (ℕ; _+_)
  open import Data.Nat.Properties using (+-*-commutativeSemiring)

  test : ∀ a → 100 + a ≡ a + 100
  test a = solve-≈ +-*-commutativeSemiring

------------------------------------------------------------------------
-- 14. The equation stated via `Setoid._≈_` of the bundle's setoid.

module ViaSetoid where
  open import Data.Nat using (ℕ; _+_)
  open import Data.Nat.Properties using (+-*-commutativeSemiring)
  open import Relation.Binary using (Setoid)
  open CommutativeSemiring +-*-commutativeSemiring using (setoid)

  test : ∀ a b → Setoid._≈_ setoid (a + b) (b + a)
  test a b = solve-≈ +-*-commutativeSemiring

------------------------------------------------------------------------
-- 15. `solve-≈` under `trans` (one side of the hole's equation is a
-- meta that the other proof determines; must block + retry, not hang).

module UnderTrans where
  open import Data.Nat using (ℕ; _+_; _*_)
  open import Data.Nat.Properties using (+-*-commutativeSemiring; *-comm)
  open import Relation.Binary.PropositionalEquality using (trans; sym)

  test : ∀ a b → (a + b) * a ≡ a * a + b * a
  test a b = trans (*-comm (a + b) a) (solve-≈ +-*-commutativeSemiring)

------------------------------------------------------------------------
-- 16. Negative ℤ literals (`-[1+_]`/`-1ℤ`), recognised on the CR side
-- and encoded as negative ℤ coefficients.

module NegativeLiterals where
  open import Data.Integer using (ℤ; -1ℤ; 1ℤ; -[1+_]; +_; _+_; _*_; -_)
  open import Data.Integer.Properties using (+-*-commutativeRing)

  neg-one-mul : ∀ a → -1ℤ * a ≡ - a
  neg-one-mul a = solve-≈ +-*-commutativeRing

  neg-lit-add : -[1+ 1 ] + (+ 2) ≡ + 0
  neg-lit-add = solve-≈ +-*-commutativeRing

  neg-times-neg : -1ℤ * -1ℤ ≡ 1ℤ
  neg-times-neg = solve-≈ +-*-commutativeRing

------------------------------------------------------------------------
-- 17. Atom identity is up to whnf: two definitions of the same value
-- on opposite sides count as one atom (the first spelling is what
-- lands in the emitted call).

module AtomSpelling where
  open import Data.Rational using (ℚ; ½; _+_; _*_)
  import Data.Rational.Properties as ℚP

  q₁ q₂ : ℚ
  q₁ = ½
  q₂ = ½

  spelled : ∀ q → q₁ + q ≡ q + q₂
  spelled q = solve-≈ ℚP.+-*-commutativeRing

------------------------------------------------------------------------
-- 18. `suc` under ℤ's `+_` wrapper peels to `1 + _` (sound because
-- `+_` is an additive homomorphism).

module WrappedSuc where
  open import Data.Nat using (suc)
  open import Data.Integer using (ℤ; +_; _+_; _*_; -_)
  open import Data.Integer.Properties using (+-*-commutativeSemiring; +-*-commutativeRing)

  wrapped-suc : ∀ n → + suc n ≡ + n + + 1
  wrapped-suc n = solve-≈ +-*-commutativeSemiring

  wrapped-suc-cr : ∀ n → + suc (suc n) ≡ + n + + 2
  wrapped-suc-cr n = solve-≈ +-*-commutativeRing

  mixed : ∀ n → (- (+ suc n)) * (+ 1) ≡ (- (+ 1)) + (- (+ n))
  mixed n = solve-≈ +-*-commutativeRing
