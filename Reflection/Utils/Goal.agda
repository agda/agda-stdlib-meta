------------------------------------------------------------------------
-- Helpers for macros that inspect the hole's type and build a term
-- for it.

{-# OPTIONS --safe --without-K #-}
module Reflection.Utils.Goal where

open import Meta.Prelude

open import Reflection
open import Reflection.AST.Argument
open import Reflection.Utils.Args using (getVisibleArgs)
open import Reflection.Utils.Metas using (isMeta; findMetaIds; firstMeta; shareMeta)
import Data.Vec as Vec
open import Data.List using (null)

-- Run a continuation under the goal type's pi-prefix (weak-head
-- reducing each layer, never normalising). The continuation gets the
-- number of binders entered and the type beneath them; its result is
-- wrapped in lambdas of matching visibility. The ℕ is fuel.
underPis : ℕ → Type → (ℕ → Type → TC Term) → TC Term
underPis = go 0
  where
  go : ℕ → ℕ → Type → (ℕ → Type → TC Term) → TC Term
  go n 0       ty k = k n ty
  go n (suc fuel) ty k = do
    ty' ← reduce ty
    case ty' of λ where
      (pi a@(arg (arg-info av _) dom) (abs s b)) → do
        case firstMeta dom of λ where
          (just m) → blockOnMeta m
          nothing  → pure tt
        body ← extendContext s a (go (suc n) fuel b k)
        pure (lam av (abs s body))
      t → k n t

-- The last two visible arguments of a relation application.
equationSides : Term → Maybe (Term × Term)
equationSides t = case getVisibleArgs 2 t of λ where
  (just (lhs Vec.∷ rhs Vec.∷ Vec.[])) → just (lhs , rhs)
  _                                   → nothing

-- `equationSides`, with a friendly error for non-equation goals.
requireEquationSides : Term → TC (Term × Term)
requireEquationSides t = case equationSides t of λ where
  (just p) → pure p
  nothing  → typeError
    ( strErr "Malformed call to algebraic solver. "
    ∷ strErr "Expected target type to be of shape  LHS ≈ RHS.  "
    ∷ strErr "Instead: "
    ∷ termErr t
    ∷ [])

-- Metavariable policy for solver-style macros: if one side has metas
-- not shared with the other, only this macro could solve them, so
-- blocking would retry forever — error instead. Otherwise block on
-- the first meta and retry once elaboration has resolved it.
blockOnEquationMetas : String → (equation lhs rhs : Term) → TC ⊤
blockOnEquationMetas macroName equation lhs rhs = do
  let bothStructured = not (isMeta lhs) ∧ not (isMeta rhs)
  let metasL         = findMetaIds lhs
  let metasR         = findMetaIds rhs
  let anyMetas       = not (null metasL ∧ null metasR)
  let sharedMeta     = shareMeta metasL metasR
  if bothStructured ∧ anyMetas ∧ not sharedMeta
    then typeError
      ( strErr macroName
      ∷ strErr ": the goal `LHS ≈ RHS` has at least one side "
      ∷ strErr "containing a metavariable that could not be resolved. To run this "
      ∷ strErr "solver you must add type annotations to resolve these variables."
      ∷ [])
    else pure tt
  case firstMeta equation of λ where
    (just m) → blockOnMeta m
    nothing  → pure tt
