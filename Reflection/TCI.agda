{-# OPTIONS --safe --without-K #-}
--------------------------------------------------------------------------------
-- Improved TC
--------------------------------------------------------------------------------

module Reflection.TCI where

open import Meta.Prelude

open import Data.List using (map)

import Agda.Builtin.Reflection as R'
import Reflection as R
open import Reflection.Syntax

open import Class.Monad hiding (Monad-TC)
open import Class.MonadError using (MonadError)
open import Class.MonadReader
open import Class.MonadTC

open Monad

TC : Set ℓ → Set ℓ
TC = ReaderT TCEnv R.TC

Monad-TC : Monad TC
Monad-TC = Monad-ReaderT ⦃ Class.Monad.Monad-TC ⦄

MonadReader-TC : MonadReader TCEnv TC ⦃ Monad-TC ⦄
MonadReader-TC = MonadReader-ReaderT ⦃ Class.Monad.Monad-TC ⦄

MonadError-TC : MonadError (List ErrorPart) TC
MonadError-TC = MonadError-ReaderT ⦃ Class.Monad.Monad-TC ⦄ ⦃ Class.MonadError.MonadError-TC ⦄

applyReductionOptions : TC A → TC A
applyReductionOptions x r@record { reduction = onlyReduce red } = R'.withReduceDefs (true ,  red) (x r)
applyReductionOptions x r@record { reduction = dontReduce red } = R'.withReduceDefs (false , red) (x r)

applyNormalisation : TC A → TC A
applyNormalisation x r@record { normalisation = n } = R.withNormalisation n (applyReductionOptions x r)

applyReconstruction : TC A → TC A
applyReconstruction x r@record { reconstruction = false } = x r
applyReconstruction x r@record { reconstruction = true  } = R'.withReconstructed true (x r)

applyNoConstraints : TC A → TC A
applyNoConstraints x r@record { noConstraints = false } = x r
applyNoConstraints x r@record { noConstraints = true  } = R'.noConstraints (x r)

applyExtContext : Telescope → R.TC A → R.TC A
applyExtContext [] x       = x
applyExtContext (t ∷ ts) x = applyExtContext ts $ (uncurry R.extendContext) t x

liftTC : R.TC A → TC A
liftTC x = λ r → applyExtContext (r .TCEnv.localContext) x

liftTC1 : (A → R.TC B) → A → TC B
liftTC1 f a = liftTC (f a)

liftTC2 : (A → B → R.TC C) → A → B → TC C
liftTC2 f a b = liftTC (f a b)

liftTC3 : (A → B → C → R.TC D) → A → B → C → TC D
liftTC3 f a b c = liftTC (f a b c)

module MonadTCI where
  unify             : Term → Term → TC ⊤
  unify             = applyNoConstraints ∘₂ liftTC2 R.unify

  typeError         : List ErrorPart → TC A
  typeError         = liftTC1 R.typeError

  inferType         : Term → TC Type
  inferType         = applyReconstruction ∘ applyNormalisation ∘ liftTC1 R.inferType

  checkType         : Term → Type → TC Term
  checkType         = (applyReconstruction ∘ applyNormalisation) ∘₂ liftTC2 R.checkType

  normalise         : Term → TC Term
  normalise         = applyReductionOptions ∘ applyReconstruction ∘ liftTC1 R.normalise

  reduce            : Term → TC Term
  reduce            = applyReductionOptions ∘ applyReconstruction ∘ liftTC1 R.reduce

  quoteTC           : A → TC Term
  quoteTC           = applyNormalisation ∘ liftTC1 R.quoteTC

  unquoteTC         : Term → TC A
  unquoteTC         = liftTC1 R.unquoteTC

  quoteωTC          : ∀ {A : Setω} → A → TC Term
  quoteωTC          = λ a → liftTC (R'.quoteωTC a)

  freshName         : String → TC Name
  freshName         = liftTC1 R.freshName

  declareDef        : Arg Name → Type → TC ⊤
  declareDef        = liftTC2 R.declareDef

  declarePostulate  : Arg Name → Type → TC ⊤
  declarePostulate  = liftTC2 R.declarePostulate

  defineFun         : Name → List Clause → TC ⊤
  defineFun         = liftTC2 R.defineFun

  getType           : Name → TC Type
  getType           = applyReconstruction ∘ liftTC1 R.getType

  getDefinition     : Name → TC Definition
  getDefinition     = applyReconstruction ∘ liftTC1 R.getDefinition

  blockOnMeta       : Meta → TC A
  blockOnMeta       = liftTC1 R.blockOnMeta

  commitTC          : TC ⊤
  commitTC          = liftTC R.commitTC

  isMacro           : Name → TC Bool
  isMacro           = liftTC1 R.isMacro

  debugPrint        : String → ℕ → List ErrorPart → TC ⊤
  debugPrint        = liftTC3 R.debugPrint

  runSpeculative    : TC (A × Bool) → TC A
  runSpeculative    = R.runSpeculative ∘_

  getInstances      : Meta → TC (List Term)
  getInstances      = liftTC1 R'.getInstances

MonadTC-TCI : MonadTC TC ⦃ Monad-TC ⦄ ⦃ MonadError-TC ⦄
MonadTC-TCI = record { MonadTCI }
