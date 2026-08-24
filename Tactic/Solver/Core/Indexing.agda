------------------------------------------------------------------------
-- De Bruijn index conventions for `Tactic.Solver.Core`: how encoders
-- address the atom binders x₁ … xₙ and the bundle inside the emitted
-- proof term (see `Tactic.Solver.Core` for its shape).
--
-- This module contains the index conventions every encoder computes
-- against. Binder order itself is decided elsewhere — atoms are
-- grouped by sort, group order is first discovery, within-group order
-- is insertion order (see `Reflection.Utils.AtomStore`); here an atom
-- is addressed by its stable (group , slot) pair, and its flat
-- position — hence its de Bruijn index — is computable only once both
-- goal sides are parsed, which is why encodings take `EncodeEnv` as
-- an argument.

{-# OPTIONS --without-K --safe #-}

module Tactic.Solver.Core.Indexing where

open import Data.List using (List; _∷_; []; take)
open import Data.Nat
open import Data.Nat.ListAction

open import Reflection
open import Reflection.AST.DeBruijn

private
  flatPos : List ℕ → (g s : ℕ) → ℕ
  flatPos sizes g s = sum (take g sizes) + s

  posVarIx : (n p : ℕ) → ℕ
  posVarIx n p = n ∸ suc p

------------------------------------------------------------------------
-- The encoding environment: everything an encoder needs that is only
-- known once both sides of the goal have been parsed.

record EncodeEnv : Set where
  field
    -- The bundle, weakened past the k pi-binders.
    R↓         : Term
    -- Final atom-group sizes, in binder-group order.
    groupSizes : List ℕ

  numAtoms : ℕ -- this is `n`
  numAtoms = sum groupSizes

  -- The bundle for splicing inside the `λ x₁ … xₙ → …` body.
  R↓↓ : Term
  R↓↓ = weaken numAtoms R↓

-- The binder reference for the atom at (group , slot), for use inside
-- the `λ x₁ … xₙ → …` body.
atomVar : EncodeEnv → (g s : ℕ) → Term
atomVar env g s = var (posVarIx numAtoms (flatPos groupSizes g s)) []
  where open EncodeEnv env
