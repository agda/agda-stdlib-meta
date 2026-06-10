{-# OPTIONS --without-K --guardedness #-}
--------------------------------------------------------------------------------
-- Companion to `Tactic.Solver.FirstOrder.Tests`: real lemmas over musical
-- colists, re-proved by a single `firstorderWith` call.  These live in their
-- own module because `Codata.Musical.Colist` is not `--safe`, so they cannot
-- join the (safe) main test suite.  The module is also deliberately not
-- imported from the `Tactic` index: `--guardedness` is infective and would
-- impose itself on every importer.  Check it standalone:
--   agda Tactic/Solver/FirstOrder/Tests/Colist.agda
--------------------------------------------------------------------------------

module Tactic.Solver.FirstOrder.Tests.Colist where

open import Data.Product using (_×_)
open import Data.Sum     using (_⊎_)
open import Relation.Nullary using (¬_)
open import Codata.Musical.Colist
  using (Colist; Finite; Infinite; not-finite-is-infinite; not-finite-and-infinite)

open import Tactic.Solver.FirstOrder

module _ {A : Set} where

  -- = Codata.Musical.Colist.finite-or-infinite : every colist is finite or
  -- infinite, classically.  The original goes through excluded middle, with a
  -- `Dec` inversion helper:
  --   finite-or-infinite xs = helper <$> ¬¬-excluded-middle
  --     where
  --     helper : Dec (Finite xs) → Finite xs ⊎ Infinite xs
  --     helper ( true because  [fin]) = inj₁ (invert [fin])
  --     helper (false because [¬fin]) =
  --       inj₂ $ not-finite-is-infinite xs (invert [¬fin])
  -- Supplying the one coinductive ingredient — `not-finite-is-infinite xs :
  -- ¬ Finite xs → Infinite xs` — lets the engine find a direct intuitionistic
  -- proof instead.  Plain `firstorder` fails here: `Finite xs` and
  -- `Infinite xs` are unrelated atoms without the lemma.
  finite-or-infinite : (xs : Colist A) → ¬ ¬ (Finite xs ⊎ Infinite xs)
  finite-or-infinite xs = firstorderWith (not-finite-is-infinite xs)

  -- The *exclusive* strengthening — classically, every colist is finite or
  -- infinite and not both — is not stated by the library.  It needs a second
  -- stdlib lemma, `Codata.Musical.Colist.not-finite-and-infinite : Finite xs →
  -- Infinite xs → ⊥`; given both, the engine assembles the case analysis
  -- (each lemma feeds one branch of the implicit split).
  finite-xor-infinite : (xs : Colist A) →
    ¬ ¬ ((Finite xs × ¬ Infinite xs) ⊎ (¬ Finite xs × Infinite xs))
  finite-xor-infinite xs =
    firstorderWith (not-finite-is-infinite xs ◂ not-finite-and-infinite {xs = xs})
