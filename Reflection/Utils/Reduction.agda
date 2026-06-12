------------------------------------------------------------------------
-- Controlled reduction for syntactic inspection of Terms.
--
-- Agda's two reflection primitives sit at the wrong extremes for a
-- macro that wants to *look at* a term rather than compute with it:
--
--   * `reduce` (whnf) unfolds until the head is canonical. That loses
--     names: the whnf of `1ℚ` is `mkℚ (+ 1) 0 ⟨proof⟩`, useless if the
--     macro needs to recognise or block the *name* `1ℚ`.
--   * `normalise` does that everywhere at once, and on proof-carrying
--     carriers (ℚ, …) routinely produces enormous terms.
--
-- The remedy is `withReduceDefs`, which restricts which definitions
-- may unfold — but it needs to be told names *in advance*, and when
-- chasing a definition chain you only learn the next name by taking a
-- step. The functions here package the resulting step-by-step
-- patterns:
--
--   * `whnfBlocking ns t` — plain whnf with the names `ns` left
--     opaque. Use when you know exactly which boundary to stop at
--     (e.g. reducing a goal while keeping its operators intact).
--
--   * `headReduce n t` — unfold the head definition one name at a
--     time (re-targeting the allow-list at each step), until the term
--     is structural (constructor, lambda, …) or stuck. Use when you
--     want a term's *shape* and the names along the way are noise:
--     e.g. pushing a record value through alias layers to find the
--     record constructor — or the stuck application obstructing it.
--
--   * `resolveToName extra n t` — like `headReduce`, but stops at the
--     last *name* of the chain: a nullary definition is only entered
--     if its body is again a bare name (an alias). Use when the name
--     is the answer: resolving `CommutativeSemiring.1# R` should
--     yield `1ℚ`, not its unfolding. The `extra` names are
--     additionally allowed to unfold at every step; see
--     `Reflection.Utils.Records` for why that matters when
--     projecting out of record values.
--
-- All three are depth-limited (`n` is fuel) and total.

{-# OPTIONS --safe --without-K #-}
module Reflection.Utils.Reduction where

open import Meta.Prelude

open import Reflection
open import Reflection.AST.Term using (clause)
open import Reflection.AST.Definition using (function)
open import Reflection.AST.AlphaEquality using (_=α=_)
import Agda.Builtin.Reflection as B using (withReduceDefs)

-- Weak-head normalisation with white/blacklisted names
whnfBlocking : List Name → Term → TC Term
whnfBlocking ns t = B.withReduceDefs (false , ns) (reduce t)

whnfOnlyUnfolding : List Name → Term → TC Term
whnfOnlyUnfolding ns t = B.withReduceDefs (true , ns) (reduce t)

private
  mutual
    -- The shared worker. `peel` selects the policy for a nullary
    -- `def`: entered unconditionally (structure mode, `false`), or
    -- only while its body is again a bare name (name mode, `true`).
    --
    -- For an applied `def`, one step unfolds *only* the current head
    -- (plus `extra`): reduction can't skip past an intermediate name,
    -- because that name was not in this step's allow-list. The loop
    -- then re-targets the new head and continues while progress is
    -- made.
    --
    -- Arguments are reduced in structure mode first: when the head is
    -- a projection, this lets `reduce` compute it by projecting from
    -- the (now exposed) record value, rather than falling back to
    -- inlining the projection's clauses.
    go : (peel : Bool) (extra : List Name) → ℕ → Term → TC Term
    go peel extra 0       t = pure t
    go peel extra (suc k) t@(def nm []) = do
      d ← getDefinition nm
      case (peel , d) of λ where
        (false , function (clause [] [] body            ∷ _)) → go peel extra k body
        (true  , function (clause [] [] body@(def _ []) ∷ _)) → go peel extra k body
        _ → pure t
    go peel extra (suc k) (def nm args) = do
      args' ← goArgs k args
      t' ← whnfOnlyUnfolding (nm ∷ extra) (def nm args')
      if t' =α= def nm args'
        then pure t' -- no progress
        else go peel extra k t'
    go peel extra (suc _) t = pure t

    -- Recursing with `go` here (rather than plain `reduce`) is
    -- required: whnf treats a nullary definition whose body is a
    -- record expression as a value and will not unfold it.
    goArgs : ℕ → Args Term → TC (Args Term)
    goArgs _ []             = pure []
    goArgs k (arg i t ∷ as) = do
      t'  ← go false [] k t
      as' ← goArgs k as
      pure (arg i t' ∷ as')

-- Structure mode
headReduce : ℕ → Term → TC Term
headReduce = go false []

-- Name mode
resolveToName : List Name → ℕ → Term → TC Term
resolveToName = go true
