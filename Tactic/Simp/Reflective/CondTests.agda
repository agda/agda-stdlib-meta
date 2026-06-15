-- Conditional-rule tests that need a GENUINELY opaque operator.
--
-- The main suite (`Tests.agda`, `--safe`, Section K) exercises conditional
-- rules over `_⊓_`, but `_⊓_` *computes* on ground literals — so e.g.
-- `3 ⊓ 5 ≡ 3` is closed by simp's definitional fallback even with NO rule,
-- and the by-*decision* discharge is never actually exercised there.  To
-- test the discharge machinery we need an operator that does not reduce,
-- which means a `postulate` (hence no `--safe` here).
--
-- This file is checked manually (like `Tests.agda`); it is not part of the
-- `standard-library-meta` CI aggregator.

module Tactic.Simp.Reflective.CondTests where

open import Data.List using (_∷_; [])
open import Data.Nat using (ℕ; _+_; _≤_)
open import Relation.Binary.PropositionalEquality
open import Class.Decidable               -- `_⁇` instances for `_≤_` etc.
open import Tactic.Defaults
open import Tactic.Simp.Reflective

-- An opaque binary operator (no computation rules) with a decidable-
-- conditional equation, and an opaque `g` with an unconditional rule.
postulate
  _⊕_  : ℕ → ℕ → ℕ
  ⊕-le : ∀ {m n} → m ≤ n → m ⊕ n ≡ m
  g    : ℕ → ℕ
  g-eq : ∀ x → g x ≡ 3

----------------------------------------------------------------
-- By DECISION (the side condition is decided via `Class.Decidable._⁇`).
-- Genuine: `3 ⊕ 5` does not reduce, so the definitional fallback cannot
-- close this — only the discharged `⊕-le` rule can.
----------------------------------------------------------------

byDec₁ : 3 ⊕ 5 ≡ 3
byDec₁ = simp! (quote ⊕-le ∷ [])

-- two INDEPENDENT ⊕-redexes, both present in the goal, each discharged by
-- decision (3 ≤ 5 and 2 ≤ 8).  (NB a *nested* `(3 ⊕ 5) ⊕ 9` would NOT work:
-- the inner `3 ⊕ 5 → 3` materialises `3 ⊕ 9`, which is no goal candidate —
-- that is the residual case documented below.)
byDec₂ : (3 ⊕ 5) + (2 ⊕ 8) ≡ 5
byDec₂ = simp! (quote ⊕-le ∷ [])

----------------------------------------------------------------
-- By ASSUMPTION (the side condition is taken from the context).  `m`/`n`
-- are abstract, so the premise is not decidable; it is discharged from the
-- `m ≤ n` binder.
----------------------------------------------------------------

byAsm₁ : ∀ {m n : ℕ} → m ≤ n → m ⊕ n ≡ m
byAsm₁ _ = simp! (quote ⊕-le ∷ [])

----------------------------------------------------------------
-- MATERIALISED redex (was the open residual; now handled in-engine).
----------------------------------------------------------------

-- `3 ⊕ 5` appears nowhere in the goal `g x ⊕ 5 ≡ 3`; it materialises only
-- after `g-eq` rewrites the inner `g x → 3` IN CONTEXT.  The macro cannot
-- pre-instantiate `⊕-le` for it (no goal candidate, no `3 ≤ 5` in scope),
-- but the engine now carries it as a `CondRule` and decides the premise at
-- firing time (`3 ≤ 5`, once the operands are normalised).
resid : ∀ {x : ℕ} → g x ⊕ 5 ≡ 3
resid = simp! (quote g-eq ∷ quote ⊕-le ∷ [])

----------------------------------------------------------------
-- LIMITATIONS (kept commented; each fails cleanly, "failed to close").
----------------------------------------------------------------

-- False ground condition: 5 ≤ 3 does not hold, so ⊕-le must not fire.
--   bad : 5 ⊕ 3 ≡ 5
--   bad = simp! (quote ⊕-le ∷ [])
-- Abstract operands with no assumption: the premise `m ≤ n` is neither
-- decidable nor available, so the rule cannot fire.
--   nope : ∀ {m n : ℕ} → m ⊕ n ≡ m
--   nope = simp! (quote ⊕-le ∷ [])
