-- Operational smoke test for the preorder step layer (`WithRel`) in the
-- engine.
--
-- Pure Core (no macros, no postulates, `--safe`): build a one-sort engine
-- by hand with ops `_+_`, `suc`, and atoms `x`/`0`/`y`, take R = ≤ on the
-- sort, and check that the fueled R-search `rsolveAt` fires along ≤:
--   * a root R-step after an ≡-step  (`x + 0 ≤ suc x`),
--   * an R-step INSIDE `_+_` via its monotonicity witness in the
--     `MonoTable` (`(x + 0) + y ≤ suc x + y`),
-- plus a negative control (WITHOUT the R-rule the same goal does not close,
-- so the R-layer is genuinely doing the work, not the ≡-fallback).
--
-- Mirrors `CoreCondTest.agda`: positive tests via `from-just!`, negative
-- control via `≡ nothing`.

{-# OPTIONS --safe #-}

module Tactic.Simp.Reflective.CoreRelTest where

open import Level using (0ℓ)
open import Data.Bool    using (false)
open import Data.List    using (List; []; _∷_)
open import Data.Maybe   using (nothing)
open import Data.Nat     using (ℕ; zero; suc; _+_; _≤_; s≤s)
open import Data.Nat.Properties
  using (+-identityʳ; n≤1+n; +-mono-≤; ≤-refl; ≤-trans)
open import Data.Product using (_,_)
open import Data.Unit    using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Tactic.Simp.Reflective.Core

module MicroTest (x y : ℕ) where

  -- One sort (ℕ, default 0); ops 0=`_+_`, 1=`suc`, 2=atom x,
  -- 3=literal 0, 4=atom y.
  Ts₀ : List (Pointed 0ℓ)
  Ts₀ = (ℕ , 0) ∷ []

  ops₀ : List (WithSorts.Op Ts₀)
  ops₀ = ((0 ∷ 0 ∷ [] , 0) , _+_)
       ∷ ((0 ∷ []     , 0) , suc)
       ∷ (([]         , 0) , x)
       ∷ (([]         , 0) , 0)
       ∷ (([]         , 0) , y)
       ∷ []

  open Eval Ts₀ ops₀

  R₀ : (s : ℕ) → ⟦ s ⟧ → ⟦ s ⟧ → Set
  R₀ zero    m n = m ≤ n
  R₀ (suc _) _ _ = ⊤

  R₀-refl : ∀ s (v : ⟦ s ⟧) → R₀ s v v
  R₀-refl zero    _ = ≤-refl
  R₀-refl (suc _) _ = tt

  R₀-trans : ∀ s {a b c : ⟦ s ⟧} → R₀ s a b → R₀ s b c → R₀ s a c
  R₀-trans zero    p q = ≤-trans p q
  R₀-trans (suc _) _ _ = tt

  -- Direct instantiation of the layer with `R₀`/`R₀-refl`/`R₀-trans`
  -- (submodule so its `open WithRel` does not clash with `ViaRFam`'s).
  module Direct where

    open WithRel R₀ R₀-refl R₀-trans

    -- ≡-rule (with an engine pattern variable):  n + 0 → n.
    idʳ : Rule
    idʳ = mkRule (op 0 0 (var 0 0 ∷ op 3 0 [] ∷ [])) (var 0 0) refl
                 (λ τ → +-identityʳ (τ 0 0)) false

    -- R-rule, var-free targeted instance (as the frontend would emit it
    -- from goal candidates):  x ≤ suc x.
    x≤sx : RRule
    x≤sx = mkRRule (op 2 0 []) (op 1 0 (op 2 0 [] ∷ [])) refl
                   (λ τ → n≤1+n x)

    -- Monotonicity table (first-order list): `_+_` (op 0) and `suc`
    -- (op 1) are ≤-monotone; atoms carry no witness.
    mt : MonoTable
    mt = (0 , λ p q → +-mono-≤ p q)
       ∷ (1 , λ p → s≤s p)
       ∷ []

    -- x + 0 ≤ suc x : ≡-step (idʳ) then a root R-step.
    t₁ : x + 0 ≤ suc x
    t₁ = from-just!
      (rsolveAt 0 20 (idʳ ∷ []) (x≤sx ∷ []) mt
        (op 0 0 (op 2 0 [] ∷ op 3 0 [] ∷ []))
        (op 1 0 (op 2 0 [] ∷ [])))

    -- (x + 0) + y ≤ suc x + y : the R-step fires INSIDE `_+_`'s first
    -- argument, i.e. genuinely through the monotonicity witness.
    t₂ : (x + 0) + y ≤ suc x + y
    t₂ = from-just!
      (rsolveAt 0 20 (idʳ ∷ []) (x≤sx ∷ []) mt
        (op 0 0 (op 0 0 (op 2 0 [] ∷ op 3 0 [] ∷ []) ∷ op 4 0 [] ∷ []))
        (op 0 0 (op 1 0 (op 2 0 [] ∷ []) ∷ op 4 0 [] ∷ [])))

    -- Negative control: without the R-rule (`noRRules`) the same goal
    -- does NOT close (so the R-layer is genuinely doing the work).
    noR : rsolveAt 0 20 (idʳ ∷ []) noRRules mt
            (op 0 0 (op 2 0 [] ∷ op 3 0 [] ∷ []))
            (op 1 0 (op 2 0 [] ∷ []))
          ≡ nothing
    noR = refl

  ----------------------------------------------------------------
  -- Same tests, but with R built by the first-order `RFam` builder from
  -- a `RelTable` (as the frontend emits it): the goal sort 0 carries ≤,
  -- everything else falls back to ≡.  This exercises the exact `WithRel
  -- (RFam tab) …` instantiation + the definitional reduction of the goal
  -- type through `RFam`/`lookupRel` that the macro relies on.
  ----------------------------------------------------------------

  module ViaRFam where

    tab : RelTable
    tab = (0 , mkRelPack _≤_ (λ v → ≤-refl) (λ p q → ≤-trans p q)) ∷ []

    open WithRel (RFam tab) (RFam-refl tab) (RFam-trans tab)

    idʳ′ : Rule
    idʳ′ = mkRule (op 0 0 (var 0 0 ∷ op 3 0 [] ∷ [])) (var 0 0) refl
                  (λ τ → +-identityʳ (τ 0 0)) false

    x≤sx′ : RRule
    x≤sx′ = mkRRule (op 2 0 []) (op 1 0 (op 2 0 [] ∷ [])) refl
                    (λ τ → n≤1+n x)

    mt′ : MonoTable
    mt′ = (0 , λ p q → +-mono-≤ p q)
        ∷ (1 , λ p → s≤s p)
        ∷ []

    -- The result type `RFam tab 0 (evalAt …) (evalAt …)` must reduce to
    -- the literal `x + 0 ≤ suc x`.
    t₁′ : x + 0 ≤ suc x
    t₁′ = from-just!
      (rsolveAt 0 20 (idʳ′ ∷ []) (x≤sx′ ∷ []) mt′
        (op 0 0 (op 2 0 [] ∷ op 3 0 [] ∷ []))
        (op 1 0 (op 2 0 [] ∷ [])))

    t₂′ : (x + 0) + y ≤ suc x + y
    t₂′ = from-just!
      (rsolveAt 0 20 (idʳ′ ∷ []) (x≤sx′ ∷ []) mt′
        (op 0 0 (op 0 0 (op 2 0 [] ∷ op 3 0 [] ∷ []) ∷ op 4 0 [] ∷ []))
        (op 0 0 (op 1 0 (op 2 0 [] ∷ []) ∷ op 4 0 [] ∷ [])))
