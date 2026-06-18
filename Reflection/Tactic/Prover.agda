------------------------------------------------------------------------
-- Provers: speculative, declinable proof attempts.
--
-- A `Prover` is a side procedure that, given a goal type, may produce
-- a proof term for it. It is the building block for tactics that "try
-- something and cleanly back out if it doesn't fully work".
--
-- The hard part is doing the "try, else back out" cleanly inside
-- `TC`. An attempt can fail in three ways, two of them silent: it
-- throws; it "succeeds" but leaves unsolved metavariables; or it
-- leaves deferred instance constraints that leak past the caller and
-- only explode later. `speculate` and `settle` handle all three.

{-# OPTIONS --without-K --safe #-}

module Reflection.Tactic.Prover where

open import Data.List                  using (List; []; _∷_)
open import Data.Maybe                 using (Maybe; just; nothing; is-just)
open import Data.Product               using (_,_)
open import Data.Empty                 using (⊥)
open import Data.Unit                  using (⊤)
open import Function
open import Relation.Nullary           using (¬_)
open import Relation.Nullary.Decidable using (True; False; toWitness; toWitnessFalse)

open import Agda.Builtin.Equality   using (refl)
open import Agda.Builtin.Reflection using (runSpeculative; solveInstanceConstraints)
open import Reflection
open import Reflection.AST.Argument using (vArg)
open import Reflection.TCM.Syntax
open import Reflection.Utils.Metas  using (firstMeta)

open import Class.Decidable using (_⁇; ¿_¿)

private variable A : Set

Prover : Set
Prover = Type → TC (Maybe Term)

------------------------------------------------------------------------
-- Combinators.

infixr 2 _orElse_

_orElse_ : TC (Maybe A) → TC (Maybe A) → TC (Maybe A)
m orElse k = m >>= λ where
  (just r) → pure (just r)
  nothing  → k

-- Run `act` speculatively: unless it returns `just`, every typechecking
-- effect it had (metavariables, constraints) is rolled back.
speculate : TC (Maybe A) → TC (Maybe A)
speculate act = runSpeculative ((λ r → r , is-just r) <$> catchTC act (pure nothing))

-- Accept `pf` as a proof only once it is fully resolved: force any
-- deferred instance search, then reject if a metavariable is left.
settle : Term → TC (Maybe Term)
settle pf = do
  solveInstanceConstraints
  pf′ ← normalise pf
  pure $ case firstMeta pf′ of λ where
    (just _) → nothing
    nothing  → just pf′

-- A synchronous attempt: try `cand` at `ty`; it either checks or fails
-- immediately, so plain `catchTC` suffices (used for `refl`, which has
-- no instance arguments to defer).
trySynAs : Term → Type → TC (Maybe Term)
trySynAs cand ty = catchTC (do pf ← checkType cand ty; pure (just pf)) (pure nothing)

-- Elaborate `cand` at `ty`, then `settle` (forcing instances).
tryElabAs : Term → Type → TC (Maybe Term)
tryElabAs cand ty = speculate (checkType cand ty >>= λ pf → settle pf)

-- Like `tryElabAs`, but elaborates `cand` against a fresh metavariable
-- of type `ty` and `unify`s the two. For a constructor application with
-- a dependent field (`_,_ {A}{B} w h` against `Σ D P`), `unify` pins `B`
-- from the known hole type, whereas `checkType` elaborates the fields
-- bottom-up and is left with the non-pattern constraint `B w = P w`,
-- leaking an unsolved metavariable.
tryUnifyAs : Term → Type → TC (Maybe Term)
tryUnifyAs cand ty = speculate (do h ← newMeta ty; unify h cand; settle h)

-- Run a whole sub-tactic on a fresh hole of the goal type, keeping the
-- *raw* result: such proofs carry obligations Agda discharges at the
-- enclosing `unify`, so `settle`'s meta-freeness check would wrongly
-- reject them. `speculate` still rolls the orphan hole back on failure.
viaTactic : (Term → TC ⊤) → Prover
viaTactic tac t = speculate (do h ← newMeta t; tac h; pure (just h))

tryProvers : List Prover → Prover
tryProvers []       t = pure nothing
tryProvers (p ∷ ps) t = p t orElse tryProvers ps t

-- `¬ t` built as the bare function type `t → ⊥` (which is what `¬_`
-- unfolds to): this avoids an unsolved level metavariable from `¬_`'s
-- implicit.
¬-of : Term → Term
¬-of t = pi (vArg t) (abs "_" (def (quote ⊥) []))

------------------------------------------------------------------------
-- Ready-made leaf provers.

private
  -- A decidable proposition that holds: `True ¿ P ¿` is solved by η when
  -- the decision is `yes`, so this fails exactly when `P` is false or has
  -- no decidability instance.
  byDec : ∀ {ℓ} {P : Set ℓ} ⦃ _ : P ⁇ ⦄ {_ : True ¿ P ¿} → P
  byDec {_} {_} ⦃ _ ⦄ {pr} = toWitness pr

  -- Dually: a decidably-*false* proposition yields a proof of its
  -- negation. `byDecFalse` recovers `P` from the expected `¬ P` (= `P → ⊥`)
  -- goal, so `proveByDecFalse` is an ordinary prover of a negation goal.
  byDecFalse : ∀ {ℓ} {P : Set ℓ} ⦃ _ : P ⁇ ⦄ {_ : False ¿ P ¿} → ¬ P
  byDecFalse {_} {_} ⦃ _ ⦄ {pr} = toWitnessFalse pr

-- Prove a goal by reflexivity of `_≡_`.
proveByRefl : Prover
proveByRefl t = trySynAs (con (quote refl) []) t

-- Prove a goal by instance search.
proveByInstance : Prover
proveByInstance t = tryElabAs (def (quote it) []) t

-- Prove a decidable goal that holds.
proveByDec : Prover
proveByDec t = tryElabAs (def (quote byDec) []) t

-- Prove a negation goal `t → ⊥` whose `t` is decidably false.
proveByDecFalse : Prover
proveByDecFalse t = tryElabAs (def (quote byDecFalse) []) t
