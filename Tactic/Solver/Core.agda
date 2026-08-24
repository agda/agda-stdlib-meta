------------------------------------------------------------------------
-- Generic core for reflection-based equational-solver frontends:
-- turns a description of a structure (a `Theory`) into a working
-- solver macro. `Tactic.Solver.Ring` and `Tactic.Solver.Monoid` are
-- the model instances.
--
-- To prove a goal of the shape
--
--   ∀ p₁ … pₖ → lhs ≈ rhs
--
-- a solver macro emits a proof term of a shape such as
--
--   λ p₁ … pₖ → solve R n (λ x₁ … xₙ → lhs′ := rhs′) refl a₁ … aₙ
--
-- with n the number of atoms (the maximal subterms not recognised as
-- theory syntax), the aᵢ the atoms themselves, and lhs′/rhs′ the
-- goal's two sides re-encoded as backend expressions over the
-- variables xᵢ. The submodules split that job:
--
--   * `Tactic.Solver.Core.Signature` — what a theory author writes:
--     slot tables, operators/constants, literals, `DetectedTheory`;
--   * `Tactic.Solver.Core.Indexing`  — the de Bruijn index
--     conventions of the emitted proof term (unit-tested, pure);
--   * `Tactic.Solver.Core.Frontend`  — goal analysis, parsing, and
--     the `solveByTheory` driver;
--   * `Tactic.Solver.Core.StdlibBackend` — call-shape helpers for
--     stdlib `Relation.Binary.Reflection`-style backends.

{-# OPTIONS --without-K --safe #-}

module Tactic.Solver.Core where

open import Tactic.Solver.Core.Indexing  public
open import Tactic.Solver.Core.Signature public
open import Tactic.Solver.Core.Frontend  public
