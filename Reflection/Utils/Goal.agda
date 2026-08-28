------------------------------------------------------------------------
-- Helpers for macros that inspect the hole's type and build a term
-- for it.

{-# OPTIONS --safe --without-K #-}
module Reflection.Utils.Goal where

open import Meta.Prelude

open import Reflection
open import Reflection.AST.Argument
open import Reflection.Utils.Args
open import Reflection.Utils.Metas
import Data.Vec as Vec
import Data.List

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
      (meta m _) → blockOnMeta m
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

-- Collect every meta anywhere in the goal equation and block on all
-- of them, retrying once elaboration has resolved the lot.
blockOnEquationMetas : Term → TC ⊤
blockOnEquationMetas equation =
  case findMetaIds equation of λ where
    []         → pure tt
    ms@(_ ∷ _) → blockTC (blockerAll (Data.List.map blockerMeta ms))
