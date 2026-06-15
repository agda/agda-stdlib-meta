# Ring solver

`solve-≈` proves equalities that hold in any commutative semiring or
commutative ring. It is a practical, reflection-based frontend to the
standard library's `Algebra.Solver.Ring`.

This file is literate Agda. The implementation lives in
`Tactic.Solver.Ring.Core`; here we only define the macro, so that
jumping to its definition lands on this documentation.

The solver handles both `CommutativeSemiring` and `CommutativeRing`,
see below.

```agda
{-# OPTIONS --without-K --safe #-}
module Tactic.Solver.Ring where

open import Algebra using (CommutativeSemiring; CommutativeRing)
open import Reflection using (Term; TC)
open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Tactic.Solver.Ring.Core using (solve-≈-macro)

macro
  solve-≈ : Term → Term → TC ⊤
  solve-≈ = solve-≈-macro
```

# Examples

## A first example: ℕ

Pass the bundle whose operations appear in the goal; `∀`-bound
variables are handled.

```agda
module ℕ-example where
  open import Data.Nat using (ℕ; _+_; _*_)
  open import Data.Nat.Properties using (+-*-commutativeSemiring)

  distrib : ∀ a b c → (a + b) * c ≡ (c * a) + (c * b)
  distrib a b = solve-≈ +-*-commutativeSemiring
```

## Rings: subtraction and negation

A `CommutativeRing` bundle additionally lets the goal use `_-_` and
`-_`.

```agda
module ℤ-example where
  open import Data.Integer using (ℤ; _+_; _*_; _-_; -_)
  open import Data.Integer.Properties using (+-*-commutativeRing)

  difference-of-squares : ∀ a b → (a - b) * (a + b) ≡ a * a - b * b
  difference-of-squares a b = solve-≈ +-*-commutativeRing

  negation : ∀ a b → - (a + b) ≡ - a - b
  negation a b = solve-≈ +-*-commutativeRing
```

## Literals

Each carrier's numeric literals are recognised as ring constants —
`0`/`1` on ℕ, `+ n` on ℤ, `0ℚ`/`1ℚ` on ℚ.

```agda
module ℚ-example where
  open import Data.Rational using (ℚ; 0ℚ; 1ℚ; _+_; _*_)
  import Data.Rational.Properties as ℚP

  unit : ∀ q → q * 1ℚ ≡ q
  unit q = solve-≈ ℚP.+-*-commutativeRing

  zero : ∀ q → (q + 0ℚ) * 1ℚ ≡ q
  zero q = solve-≈ ℚP.+-*-commutativeRing
```

## Abstract bundles

The carrier need not be concrete; under an abstract bundle, state the
goal with its `_≈_`.

```agda
module abstract-example {c ℓ} (R : CommutativeSemiring c ℓ) where
  open CommutativeSemiring R

  rearrange : ∀ a b c d → ((a + b) + (c + d)) ≈ ((d + c) + (b + a))
  rearrange a b c d = solve-≈ R
```

## Scope and limitations

- The goal's relation may be the bundle's `_≈_`, or propositional
  `_≡_` when that is the bundle's equality (as for ℕ/ℤ/ℚ).
- Subterms the solver does not recognise as ring syntax become opaque
  *atoms*: it proves the goal treating them as fresh variables, so an
  identity that depends on their internal structure will not be found.
- Carriers that are themselves function types (with a pointwise
  `_≈_`) are not supported.

`Tactic.Solver.Ring.Tests.*` exercises many more goals and bundle
shapes.
