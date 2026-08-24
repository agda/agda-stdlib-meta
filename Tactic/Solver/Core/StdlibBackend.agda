------------------------------------------------------------------------
-- Call-shape helpers for backends exposed through a *parameterized
-- wrapper module*
--
--   module W {c ℓ} (R : Bundle c ℓ) where
--     open import Some.Stdlib.Solver R public
--
-- which gives every re-exported backend name the uniform telescope
-- `{c ℓ} (R) {…} → …`, so encoders can splice the bundle and the atom
-- count explicitly.

{-# OPTIONS --without-K --safe #-}

module Tactic.Solver.Core.StdlibBackend where

open import Data.List as List
open import Data.Nat.Reflection
open import Data.Vec as Vec

open import Reflection
open import Reflection.AST.Argument
open import Reflection.AST.Term

open import Tactic.Solver.Core.Indexing

-- A backend name with telescope `{c ℓ} (R) {n} → …`, applied to the
-- given visible args inside the `λ x₁ … xₙ → …` body.
defP : EncodeEnv → Name → List Term → Term
defP env nm args =
  def nm (2 ⋯⟅∷⟆ EncodeEnv.R↓↓ env ⟨∷⟩ toTerm (EncodeEnv.numAtoms env) ⟅∷⟆ List.map vArg args)

-- A `def`-headed backend operator, applied to the encoded operands.
opEnc : ∀ {n} → Name → EncodeEnv → Vec Term n → Term
opEnc nm env args = defP env nm (Vec.toList args)

-- Generate the solver expression.
finishViaSolve : (solveName reflName : Name) → EncodeEnv → Term → List Term → Term
finishViaSolve solveName reflName env body atoms =
  def solveName
    (2 ⋯⟅∷⟆ R↓ ⟨∷⟩ toTerm (EncodeEnv.numAtoms env) ⟨∷⟩ body ⟨∷⟩ `refl ⟨∷⟩ List.map vArg atoms)
  where
  R↓ = EncodeEnv.R↓ env
  `refl = def reflName (2 ⋯⟅∷⟆ R↓ ⟨∷⟩ 1 ⋯⟅∷⟆ [])
