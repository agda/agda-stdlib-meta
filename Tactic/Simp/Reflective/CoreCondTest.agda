-- Operational smoke test for the conditional-rule wiring in the engine.
--
-- Pure Core (no macros, no postulates, `--safe`): build a one-sort engine
-- by hand with an identity operator `g` and a constant `c`, and a
-- conditional rule `g x ≡ x` (here the side condition is trivially true,
-- `fire = λ τ → just refl`).  Then check that `solveAt`, threaded with this
-- `CondRule`, actually fires it — i.e. `tryRulesC` is genuinely consulted by
-- `rewrite₁`/`simplify`/`solve`, not dead code.

{-# OPTIONS --safe #-}

module Tactic.Simp.Reflective.CoreCondTest where

open import Data.Nat     using (ℕ)
open import Data.List    using (List; []; _∷_)
open import Data.Maybe   using (just; nothing; is-just)
open import Data.Bool    using (T)
open import Data.Product using (_,_)
open import Data.Unit    using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

import Tactic.Simp.Reflective.Core as RC

-- One sort, sort 0 = ℕ (default 0).
Ts : List (RC.Pointed _)
Ts = (ℕ , 0) ∷ []

open RC.WithSorts Ts using (Op)

-- op 0 = `g`, the identity ℕ → ℕ; op 1 = `c`, the constant 7.
ops : List Op
ops = ((0 ∷ [] , 0) , λ x → x)
    ∷ (([]     , 0) , 7)
    ∷ []

open RC.Eval Ts ops using (CondRule; mkCondRule; solveAt)

-- Goal sides: `g c` and `c`.  Not syntactically equal, so the goal closes
-- only if a rule rewrites `g c → c`.
gc c : RC.Expr
gc = RC.op 0 0 (RC.op 1 0 [] ∷ [])
c  = RC.op 1 0 []

-- Conditional rule `g x ≡ x`; both sides eval to the same value, so the
-- side condition holds with `refl`.
cr : CondRule
cr = mkCondRule (RC.op 0 0 (RC.var 0 0 ∷ [])) (RC.var 0 0) refl (λ τ → just refl)

-- WITH the conditional rule the engine fires it and closes the goal.
condFires : T (is-just (solveAt 0 100 [] (cr ∷ []) gc c))
condFires = tt

-- WITHOUT it the goal does not close — so it really was the conditional
-- path (`tryRulesC`) that fired above, not the ordinary engine.
condNeeded : solveAt 0 100 [] [] gc c ≡ nothing
condNeeded = refl
