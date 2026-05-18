-- A standalone, dependently-typed proof-witness algebra.
--
-- This module provides:
--
--   * `Chain R a b`  — a typed equality witness with `rfl`, `trns`,
--                      `invs`, and atomic `rule` constructors;
--   * `_∙_`          — smart sequential composition (`rfl`-eliding);
--   * `reify`        — a dependent fold from `Chain` to `_≡_`;
--   * `Expr Σ s`     — a generic, many-sorted symbolic expression
--                      language over a `Signature`.
--
-- Nothing in this file references Agda's reflection types (Term, Name)
-- or uses the `macro` keyword.
--
-- Examples that exercise this machinery live in `Tactic.Simp.Witness.Tests`.

{-# OPTIONS --safe #-}

module Tactic.Simp.Witness where

open import Data.List               using (List; []; _∷_)
open import Data.Nat                using (ℕ)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; trans; sym)

----------------------------------------------------------------
-- Typed chains: a dependently-indexed proof witness.
--
-- `Chain R a b` is a proof in the free 2-category over the relation
-- `R`, with source `a` and target `b`.  The four constructors are
-- the standard groupoid generators.
----------------------------------------------------------------

data Chain {S : Set} (R : S → S → Set) : S → S → Set where
  rfl  : ∀ {a}     → Chain R a a
  trns : ∀ {a b c} → Chain R a b → Chain R b c → Chain R a c
  invs : ∀ {a b}   → Chain R a b → Chain R b a
  rule : ∀ {a b}   → R a b → Chain R a b

-- Smart trans:  `rfl` on either side disappears.
infixr 5 _∙_
_∙_ : ∀ {S} {R : S → S → Set} {a b c : S}
    → Chain R a b → Chain R b c → Chain R a c
rfl ∙ w   = w
w   ∙ rfl = w
w₁  ∙ w₂  = trns w₁ w₂

-- Reification: a dependent fold from `Chain` to `_≡_`.  Given an
-- atom-interpretation, fold a chain into a typed equality proof.
reify : ∀ {S} {R : S → S → Set} {a b : S}
      → (∀ {x y} → R x y → x ≡ y)
      → Chain R a b → a ≡ b
reify _ rfl        = refl
reify f (trns x y) = trans (reify f x) (reify f y)
reify f (invs x)   = sym (reify f x)
reify f (rule a)   = f a

----------------------------------------------------------------
-- Generic, many-sorted expression language.
--
-- A signature specifies a set of sorts, and a set of operation
-- symbols.  Each symbol `Op Σ args s` declares its input sorts
-- (`args : List Sort`) and output sort (`s : Sort`) in its type,
-- so pattern matching `apply o args` against `Expr Σ s` only
-- enumerates the operations whose codomain is `s`.
----------------------------------------------------------------

-- Heterogeneous, sort-indexed argument vector.
data Args {S : Set} (E : S → Set) : List S → Set where
  ε   : Args E []
  _◂_ : ∀ {s ss} → E s → Args E ss → Args E (s ∷ ss)
infixr 5 _◂_

record Signature : Set₁ where
  field
    Sort : Set
    Op   : List Sort → Sort → Set
open Signature public

-- The generic expression language: sort-indexed variables and
-- operation applications.
data Expr (Σ : Signature) : Sort Σ → Set where
  var   : ∀ {s} → ℕ → Expr Σ s
  apply : ∀ {args s} → Op Σ args s → Args (Expr Σ) args → Expr Σ s
