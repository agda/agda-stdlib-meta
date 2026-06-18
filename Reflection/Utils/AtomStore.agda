------------------------------------------------------------------------
-- A store mapping "atoms" — subterms a macro abstracts over — to
-- variable indices.
--
-- An atom is stored as a pair of its *original spelling* — what the
-- macro should splice into emitted terms, so nothing the user wrote
-- ever appears unfolded — and its weak-head normal form, which acts
-- as a second identity key: two spellings of the same value (two
-- definitions unfolding to the same constructor form) count as one
-- atom. Whnf-equality implies definitional equality, so emitting the
-- first-seen spelling for both stays type-correct.
--
-- PERFORMANCE WARNING: keep the store operations as separate,
-- first-order list traversals whose results the caller forces
-- promptly (e.g. a `just i ← pure (atomStoreIndex …)` pattern). A
-- fused insert-and-index traversal returning a pair looks equivalent
-- but builds thunk chains that Agda's reflection evaluator
-- re-evaluates without sharing — on an 8-atom goal this blew up from
-- milliseconds to an out-of-memory kill
-- (see `Tactic.Solver.Ring.Tests.EdgeCases` / big8).

{-# OPTIONS --safe --without-K #-}
module Reflection.Utils.AtomStore where

open import Meta.Prelude

import Data.Maybe as Maybe
import Data.Fin as Fin
open import Data.List using (map; findIndexᵇ)
open import Reflection
open import Reflection.AST.AlphaEquality using (_=α=_)

Atom : Set
Atom = Term × Term   -- (original spelling , whnf key)

AtomStore : Set
AtomStore = List Atom

atomMatches : Atom → Atom → Bool
atomMatches (orig , whnf) (o , w) = (orig =α= o) ∨ (whnf =α= w)

insertAtomStore : Atom → AtomStore → AtomStore
insertAtomStore a []         = a ∷ []
insertAtomStore a (b ∷ rest) =
  if atomMatches a b then b ∷ rest else b ∷ insertAtomStore a rest

atomStoreIndex : Atom → AtomStore → Maybe ℕ
atomStoreIndex a []         = nothing
atomStoreIndex a (b ∷ rest) =
  if atomMatches a b then just 0 else Maybe.map suc (atomStoreIndex a rest)

atomSpellings : AtomStore → List Term
atomSpellings = map proj₁

------------------------------------------------------------------------
-- Simple α-keyed atom table.
--
-- A lighter tier than the dual-key `AtomStore` above: atoms are kept as
-- a bare `List Term`, deduplicated up to α-equality, with no separate
-- whnf key. Use this when the macro never re-emits an atom in unfolded
-- form (e.g. the first-order solver, whose atoms are opaque predicate
-- occurrences). Equation solvers that splice atoms back into the proof
-- term — and so must preserve the user's exact spelling while still
-- deduplicating definitionally-equal spellings — want the dual-key
-- `AtomStore` above instead.

insertAtom : Term → List Term → List Term
insertAtom t []       = t ∷ []
insertAtom t (a ∷ as) = if t =α= a then a ∷ as else a ∷ insertAtom t as

findAtomIndex : Term → List Term → Maybe ℕ
findAtomIndex t xs = Maybe.map Fin.toℕ (findIndexᵇ (t =α=_) xs)
