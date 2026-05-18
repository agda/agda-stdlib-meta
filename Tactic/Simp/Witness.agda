-- A standalone, dependently-typed proof-witness algebra.
--
-- This module provides:
--
--   * `Chain R a b`  — a typed equality witness with `rfl`, `trns`,
--                      `invs`, and atomic `rule` constructors;
--   * `_∙_`          — smart sequential composition (`rfl`-eliding);
--   * `reify`        — a dependent fold from `Chain` to `_≡_`;
--   * `Expr Σ s`     — a generic, many-sorted symbolic expression
--                      language over a `Signature`;
--   * `greedy`       — a generic iterative solver that builds a
--                      typed chain from a user-supplied one-step
--                      matcher.
--
-- Nothing in this file references Agda's reflection types (Term, Name)
-- or uses the `macro` keyword.
--
-- Examples that exercise this machinery live in `Tactic.Simp.Witness.Tests`.

{-# OPTIONS --safe #-}

module Tactic.Simp.Witness where

open import Data.List                using (List; []; _∷_)
open import Data.Maybe               using (Maybe; just; nothing)
open import Data.Nat                 using (ℕ; zero; suc)
open import Data.Product             using (_,_; Σ)
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
-- A signature specifies a set of sorts and a set of operation
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

----------------------------------------------------------------
-- Generic greedy solver.
--
-- Given an evaluator `eval` and a one-step matcher that either
-- rewrites the top of an expression via some `Chain` step or
-- returns `nothing`, `greedy` iterates up to a fuel limit and
-- produces a typed chain whose source and target are the source
-- and final evaluated expressions.
--
-- This subsumes any per-signature greedy: the user supplies the
-- evaluator and a sort-specific matcher; everything else — the
-- iteration loop, the chain composition, the no-op fallback — is
-- handled here once and for all.
----------------------------------------------------------------

-- A matcher inspects the top of an expression in some environment
-- and either rewrites it via a single `Chain` step or declines.
-- (`Sg` rather than `Σ` here to avoid shadowing the dependent-sum
-- type former.)
Matcher : (Sg : Signature) (s : Sort Sg) {Env X : Set}
        → (Expr Sg s → Env → X) → (X → X → Set) → Set
Matcher Sg s {Env} eval R =
  (ρ : Env) (e : Expr Sg s)
  → Maybe (Σ (Expr Sg s) λ e′ → Chain R (eval e ρ) (eval e′ ρ))

greedy : ∀ {Sg : Signature} {s : Sort Sg} {Env X : Set} {R : X → X → Set}
       → (eval : Expr Sg s → Env → X)
       → Matcher Sg s eval R
       → (ρ : Env) → ℕ → (e : Expr Sg s)
       → Σ (Expr Sg s) λ e′ → Chain R (eval e ρ) (eval e′ ρ)
greedy eval m ρ 0       e = e , rfl
greedy eval m ρ (suc n) e with m ρ e
... | just (e′ , step) =
        let (e″ , rest) = greedy eval m ρ n e′
        in  e″ , step ∙ rest
... | nothing = e , rfl

----------------------------------------------------------------
-- A bundled "setup" for running the simplifier.
--
-- `SimpSetup` packages everything that's needed (apart from the
-- domain-specific matcher and the seed expression) to run `greedy`
-- and reify its result to a propositional equality: the signature,
-- the target sort, the environment / carrier types, the evaluator,
-- the atom relation, and the atom interpretation.
--
-- `runSimp` is the standard pipeline: it runs `greedy` to discover
-- a chain and then `reify`s it to a propositional equality.
----------------------------------------------------------------

record SimpSetup : Set₁ where
  field
    {Sg}      : Signature
    {s}       : Sort Sg
    {Env}     : Set
    {X}       : Set
    eval      : Expr Sg s → Env → X
    {R}       : X → X → Set
    interpret : ∀ {a b} → R a b → a ≡ b
    match     : Matcher Sg s eval R

module _ (setup : SimpSetup) where
  open SimpSetup setup

  runSimp : (ρ : Env) → ℕ → (e : Expr Sg s)
          → Σ (Expr Sg s) λ e′ → eval e ρ ≡ eval e′ ρ
  runSimp ρ fuel e =
    let (e′ , chain) = greedy eval match ρ fuel e
    in  e′ , reify interpret chain
