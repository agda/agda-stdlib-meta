{-# OPTIONS --safe --without-K #-}
--------------------------------------------------------------------------------
-- Types & functions for interacting with tactics/metaprograms
--------------------------------------------------------------------------------

module Reflection.Tactic where

import Reflection as R
open import Class.Monad hiding (Monad-TC)
open import Class.MonadTC
open import Meta.Prelude
open import Meta.Init

open MonadTC ⦃...⦄

Tactic = Term → R.TC ⊤
UnquoteDecl = R.TC ⊤

ITactic : Set
ITactic = TC ⊤

initTacEnv : (TCEnv → TCEnv) → ITactic → Tactic
initTacEnv f tac goal = (initTCEnvWithGoal goal) R.>>= tac ∘ f

initTacOpts : ITactic → TCOptions → Tactic
initTacOpts tac opts = initTacEnv (λ env → record env { options = opts }) tac

module _ ⦃ opts : TCOptions ⦄ where

  initTac : ITactic → Tactic
  initTac tac = initTacOpts tac opts

  initUnquoteWithGoal : Term → TC ⊤ → UnquoteDecl
  initUnquoteWithGoal g unq = (initTCEnvWithGoal g) R.>>= unq
                            ∘ (λ env → record env { options = opts })

  initUnquote : TC ⊤ → UnquoteDecl
  initUnquote unq = initUnquoteWithGoal unknown unq

  macro
    byTC : TC A → Tactic
    byTC comp = initTac ((comp >>= quoteTC) >>= unifyWithGoal)

    by : ITactic → Tactic
    by = initTac
