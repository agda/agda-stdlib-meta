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
-- LIMITATIONS (kept commented; each fails by design).
----------------------------------------------------------------

-- False ground condition: 5 ≤ 3 does not hold, so ⊕-le must not fire.
--   bad : 5 ⊕ 3 ≡ 5
--   bad = simp! (quote ⊕-le ∷ [])        -- "failed to close the goal"

-- Side condition on a MATERIALISED redex (the open residual).  `3 ⊕ 5`
-- appears nowhere in the goal `g x ⊕ 5 ≡ 3`; it materialises only after
-- `g-eq` rewrites the inner `g x → 3` IN CONTEXT.  So ⊕-le is never
-- instantiated for it (it is no goal candidate, and `3 ≤ 5` is neither in
-- the goal nor in scope to discharge by assumption).  Provable by hand as
-- `trans (cong (_⊕ 5) (g-eq x)) (⊕-le {3} {5} _)`, but not by simp.
-- Discharging this needs the *engine* to carry conditional rules and decide
-- the premise at firing time — a `--safe` Core extension, not a frontend
-- pre-pass.
--   resid : ∀ {x : ℕ} → g x ⊕ 5 ≡ 3
--   resid = simp! (quote g-eq ∷ quote ⊕-le ∷ [])   -- stuck at `3 ⊕ 5`
