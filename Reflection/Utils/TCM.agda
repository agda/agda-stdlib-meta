{-# OPTIONS --safe --without-K #-}
module Reflection.Utils.TCM where

open import Reflection

import Class.Monad as C
import Class.MonadError as C
import Class.MonadReader as C
import Class.MonadTC as C
open import Reflection.Utils.TCI {TC} ⦃ C.Monad-TC ⦄ ⦃ C.MonadError-TC ⦄
  ⦃ record { ask = C.initTCEnv ; local = λ _ x → x } ⦄ ⦃ C.MonadTC-TC ⦄ public

open import Meta.Prelude
open import Reflection.AST.Term using (clause)
open import Reflection.AST.Definition using (function)
open import Reflection.AST.AlphaEquality using (_=α=_)
import Agda.Builtin.Reflection as B using (withReduceDefs)

-- Depth-limited weak-head reduction that unfolds one `def` at a time.
--
-- Each step head-reduces every argument first, then asks Agda's
-- `reduce` to unfold *only* the outer `def`. Stops at a fixed point
-- or when fuel runs out. More aggressive than `reduce` (which won't
-- chase a chain of `def x = def y = …`) but more controlled than
-- `normalise`.
--
-- The argument pass is required to reduce record projections, so that
-- when the outer def is a projection, `reduce` can compute it cleanly
-- instead of falling back to inlining the projection's whole body.
--
-- It's a bit awkward that we only reduce the `nm` in the case with no
-- arguments, but this is the only configuration I've found that makes
-- the ring solver work.

mutual
  headReduce : ℕ → Term → TC Term
  headReduce 0       t = pure t
  headReduce (suc k) (def nm [])   = do
    d ← getDefinition nm
    case d of λ where
      (function (clause [] [] body ∷ _)) → headReduce k body
      _                                  → pure (def nm [])
  headReduce (suc k) (def nm args) = do
    args' ← reduceArgs k args
    t' ← B.withReduceDefs (true , nm ∷ []) (reduce (def nm args'))
    if t' =α= def nm args'
      then pure t' -- no progress
      else headReduce k t'
  headReduce (suc _) t = pure t

  reduceArgs : ℕ → Args Term → TC (Args Term)
  reduceArgs _ []             = pure []
  reduceArgs k (arg i t ∷ as) = do
    t'  ← headReduce k t
    as' ← reduceArgs k as
    pure (arg i t' ∷ as')
