------------------------------------------------------------------------
-- Tests `solve-≈` against various ways a `CommutativeSemiring` can
-- be defined.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Tactic.Solver.Ring.Tests.BundleVariants where

open import Algebra using (CommutativeSemiring)
open import Data.Integer as ℤ              using (ℤ)
import Data.Integer.Base                   as ℤB
open import Data.Integer.Properties        as ℤP
  using (+-*-commutativeSemiring)
open import Data.Nat                       as ℕ using (ℕ)
import Data.Nat.Base                       as ℕB
open import Data.Nat.Properties            as ℕP
open import Relation.Binary.PropositionalEquality
  using (_≡_)
open import Tactic.Solver.Ring using (solve-≈)

------------------------------------------------------------------------
-- 1. Trivial alias.

myZ : CommutativeSemiring _ _
myZ = ℤP.+-*-commutativeSemiring

module AliasZ where
  open CommutativeSemiring myZ

  assoc* : ∀ a b c → ((a * b) * c) ≈ (a * (b * c))
  assoc* = solve-≈ myZ

  comm+ : ∀ a b → (a + b) ≈ (b + a)
  comm+ = solve-≈ myZ

------------------------------------------------------------------------
-- 2. Inline record literal with direct field values.

myZ'' : CommutativeSemiring _ _
myZ'' = record
  { Carrier               = ℤ
  ; _≈_                   = _≡_
  ; _+_                   = ℤB._+_
  ; _*_                   = ℤB._*_
  ; 0#                    = ℤB.+ 0
  ; 1#                    = ℤB.+ 1
  ; isCommutativeSemiring = ℤP.+-*-isCommutativeSemiring
  }

module InlineRecordZ where
  open CommutativeSemiring myZ''

  assoc* : ∀ a b c → ((a * b) * c) ≈ (a * (b * c))
  assoc* = solve-≈ myZ''

  comm+ : ∀ a b → (a + b) ≈ (b + a)
  comm+ = solve-≈ myZ''

------------------------------------------------------------------------
-- 3. η-expanded operators.

myZη : CommutativeSemiring _ _
myZη = record
  { Carrier               = ℤ
  ; _≈_                   = _≡_
  ; _+_                   = λ a b → a ℤB.+ b
  ; _*_                   = λ a b → a ℤB.* b
  ; 0#                    = ℤB.+ 0
  ; 1#                    = ℤB.+ 1
  ; isCommutativeSemiring = ℤP.+-*-isCommutativeSemiring
  }

module EtaExpandedZ where
  open CommutativeSemiring myZη

  assoc* : ∀ a b c → ((a * b) * c) ≈ (a * (b * c))
  assoc* = solve-≈ myZη

  comm+ : ∀ a b → (a + b) ≈ (b + a)
  comm+ = solve-≈ myZη

------------------------------------------------------------------------
-- 4. ℕ analogues of the above.

myN : CommutativeSemiring _ _
myN = ℕP.+-*-commutativeSemiring

module AliasN where
  open CommutativeSemiring myN

  assoc* : ∀ a b c → ((a * b) * c) ≈ (a * (b * c))
  assoc* = solve-≈ myN

  comm+ : ∀ a b → (a + b) ≈ (b + a)
  comm+ = solve-≈ myN

myN' : CommutativeSemiring _ _
myN' = record
  { Carrier               = ℕ
  ; _≈_                   = _≡_
  ; _+_                   = ℕB._+_
  ; _*_                   = ℕB._*_
  ; 0#                    = 0
  ; 1#                    = 1
  ; isCommutativeSemiring = ℕP.+-*-isCommutativeSemiring
  }

module InlineRecordN where
  open CommutativeSemiring myN'

  assoc* : ∀ a b c → ((a * b) * c) ≈ (a * (b * c))
  assoc* = solve-≈ myN'

  comm+ : ∀ a b → (a + b) ≈ (b + a)
  comm+ = solve-≈ myN'

------------------------------------------------------------------------
-- 5. Bundle defined as the result of a function.

makeZ : ℤ → CommutativeSemiring _ _
makeZ _ = ℤP.+-*-commutativeSemiring

myZf : CommutativeSemiring _ _
myZf = makeZ (ℤB.+ 0)

module FunctionResultZ where
  open CommutativeSemiring myZf

  assoc* : ∀ a b c → ((a * b) * c) ≈ (a * (b * c))
  assoc* = solve-≈ myZf

  comm+ : ∀ a b → (a + b) ≈ (b + a)
  comm+ = solve-≈ myZf

------------------------------------------------------------------------
-- 6. Two-level alias chain.

myZAlias1 : CommutativeSemiring _ _
myZAlias1 = ℤP.+-*-commutativeSemiring

myZAlias2 : CommutativeSemiring _ _
myZAlias2 = myZAlias1

module DoubleAliasZ where
  open CommutativeSemiring myZAlias2

  assoc* : ∀ a b c → ((a * b) * c) ≈ (a * (b * c))
  assoc* = solve-≈ myZAlias2

  comm+ : ∀ a b → (a + b) ≈ (b + a)
  comm+ = solve-≈ myZAlias2

------------------------------------------------------------------------
-- 7. Record update on top of an alias.

myZUpdated : CommutativeSemiring _ _
myZUpdated = record myZAlias1 { 0# = ℤB.+ 0 }

module RecordUpdateOfAliasZ where
  open CommutativeSemiring myZUpdated

  assoc* : ∀ a b c → ((a * b) * c) ≈ (a * (b * c))
  assoc* = solve-≈ myZUpdated

  comm+ : ∀ a b → (a + b) ≈ (b + a)
  comm+ = solve-≈ myZUpdated

------------------------------------------------------------------------
-- 8. Record update with η-expanded field values.

myZUpdatedη : CommutativeSemiring _ _
myZUpdatedη = record ℤP.+-*-commutativeSemiring
  { _+_ = λ a b → a ℤB.+ b
  ; _*_ = λ a b → a ℤB.* b
  }

module RecordUpdateηZ where
  open CommutativeSemiring myZUpdatedη

  assoc* : ∀ a b c → ((a * b) * c) ≈ (a * (b * c))
  assoc* = solve-≈ myZUpdatedη

  comm+ : ∀ a b → (a + b) ≈ (b + a)
  comm+ = solve-≈ myZUpdatedη

------------------------------------------------------------------------
-- 9. Inlined operator body (KNOWN FAILURE). Instead of referring to
--    `ℤB._*_`, write its definition `sign i Sign.* sign j ◃ ∣i∣ ℕ.*
--    ∣j∣` directly in the bundle.
--
--    We cannot tell Agda to stop reduction at a record projection
--    (this is a limitation of reflection primitives) and we have to
--    reduce enough for other use cases, so we have no way to stop
--    reduction before it expands to the RHS of the record, which is
--    too late.
--
--    The workaround is to give the inlined formula its own top-level
--    definition.

open import Data.Sign.Base as Sign using (Sign)

myZInlined : CommutativeSemiring _ _
myZInlined = record ℤP.+-*-commutativeSemiring
  { _*_ = λ i j → ℤB.sign i Sign.* ℤB.sign j ℤB.◃ ℤB.∣ i ∣ ℕB.* ℤB.∣ j ∣
  }

module InlinedBodyZ where
  open CommutativeSemiring myZInlined

  -- assoc* : ∀ a b c → ((a * b) * c) ≈ (a * (b * c))
  -- assoc* = solve-≈ myZInlined

  -- comm+ : ∀ a b → (a + b) ≈ (b + a)
  -- comm+ = solve-≈ myZInlined
