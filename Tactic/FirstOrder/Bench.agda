{-# OPTIONS --without-K #-}
--------------------------------------------------------------------------------
-- Performance probe for the fuel-free decider `Tactic.FirstOrder.Decide`.
--
-- Goals are built engine-level so their Dyckhoff weight `w` — and hence the
-- termination measure μ = 3^w — is enormous, confirming that `decideFast`'s
-- runtime tracks the *actual* search size, not μ (which it passes as a lazy,
-- GMP-backed `ℕ` fuel ceiling; see the note at `Decide.decideFast`).
--
-- Each goal below is a `[] ⊢ φ`, so type-checking it forces the search. This
-- module is deliberately *not* imported by `Tactic`, to keep the main build
-- fast. Reproduce with:  agda --profile=definitions Tactic/FirstOrder/Bench.agda
--
-- Measured (Agda 2.8.0, w(tree d) = 2^(d+1)−1):
--
--   goal       leaves   w      μ ≈        time
--   chain 400  —        401    10¹⁹¹      <1ms   (below profiler threshold)
--   tree 8     256      511    10²⁴³      76ms
--   tree 9     512      1023   10⁴⁸⁸      185ms
--   tree 10    1024     2047   10⁹⁷⁶      436ms
--   tree 11    2048     4095   10¹⁹⁵³     1020ms
--
-- Time roughly doubles as the leaf count doubles (~linear in search size) while
-- μ grows by hundreds of orders of magnitude: μ is irrelevant to cost.
--------------------------------------------------------------------------------

module Tactic.FirstOrder.Bench where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (zero)
open import Data.List using ([])
open import Data.Maybe using (from-just)

open import Tactic.FirstOrder.Core   using (Formula; atom; _∧′_; _⇒′_; _⊢_)
open import Tactic.FirstOrder.Decide using (decideFast)

a : Formula 1
a = atom zero

-- right-nested implication chain  a ⇒ a ⇒ … ⇒ a  (n arrows). w = n+1, μ = 3^(n+1).
chain : ℕ → Formula 1
chain zero    = a
chain (suc n) = a ⇒′ chain n

-- balanced ∧-tree of depth d: 2^d leaves, w = 2^(d+1)−1, μ = 3^w.
tree : ℕ → Formula 1
tree zero    = a
tree (suc d) = tree d ∧′ tree d

chain400 : [] ⊢ chain 400
chain400 = from-just (decideFast [] (chain 400))

tree8 : [] ⊢ (tree 8 ⇒′ tree 8)
tree8 = from-just (decideFast [] (tree 8 ⇒′ tree 8))

tree11 : [] ⊢ (tree 11 ⇒′ tree 11)
tree11 = from-just (decideFast [] (tree 11 ⇒′ tree 11))
