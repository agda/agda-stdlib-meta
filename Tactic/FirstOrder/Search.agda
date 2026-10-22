{-# OPTIONS --safe --without-K #-}
--------------------------------------------------------------------------------
-- Fuel-bounded proof search in the G4ip calculus of `Tactic.FirstOrder.Core`.
--
-- `search` is the *untrusted* component: it may fail or give up when fuel runs
-- out, but every derivation it returns is a genuine `Γ ⊢ φ`, which
-- `Core.soundness` turns into a real proof.
--
-- Because G4ip is contraction-free — every left rule discards its principal
-- formula (`Γ ∖ i`) — the search never reprocesses a hypothesis, so any fuel
-- exceeding the sequent's Dyckhoff weight is complete for IPL. `Decide` turns
-- that into a fuel-free, provably-terminating decision procedure.
--------------------------------------------------------------------------------

module Tactic.FirstOrder.Search where

open import Data.Fin.Properties using (_≟_)
open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; just; nothing; map; _<∣>_)
open import Data.Nat using (ℕ; zero; suc)
open import Function using (case_of_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (yes; no)

open import Tactic.FirstOrder.Core

private
  variable
    n : ℕ

--------------------------------------------------------------------------------
-- Locating hypotheses
--
-- Partial syntactic equality, returning a proof only on a match. The single
-- catch-all clause is what spares us the quadratic blow-up of a full
-- `DecidableEquality`; the rules only ever need to confirm a match, not refute.
--------------------------------------------------------------------------------

eq? : (φ ψ : Formula n) → Maybe (φ ≡ ψ)
eq? (atom i) (atom j) = case i ≟ j of λ where
  (yes refl) → just refl
  (no _)     → nothing
eq? ⊤′ ⊤′ = just refl
eq? ⊥′ ⊥′ = just refl
eq? (a ∧′ b) (c ∧′ d) = case eq? a c of λ where
  (just refl) → map (λ { refl → refl }) (eq? b d)
  nothing     → nothing
eq? (a ∨′ b) (c ∨′ d) = case eq? a c of λ where
  (just refl) → map (λ { refl → refl }) (eq? b d)
  nothing     → nothing
eq? (a ⇒′ b) (c ⇒′ d) = case eq? a c of λ where
  (just refl) → map (λ { refl → refl }) (eq? b d)
  nothing     → nothing
eq? _ _ = nothing

find : (φ : Formula n) (Γ : List (Formula n)) → Maybe (φ ∈ Γ)
find φ []      = nothing
find φ (ψ ∷ Γ) = case eq? φ ψ of λ where
  (just refl) → just (here refl)
  nothing     → map there (find φ Γ)

--------------------------------------------------------------------------------
-- The search. Recursion is on the fuel argument; `search` decrements it before
-- delegating to the helpers. Each left rule recurses on `Γ ∖ i`, so contexts
-- shrink and fuel proportional to formula size suffices.
--------------------------------------------------------------------------------

mutual
  search : ∀ {n} → ℕ → (Γ : List (Formula n)) (G : Formula n) → Maybe (Γ ⊢ G)
  search zero    Γ G = nothing
  search (suc m) Γ G =
        right m Γ G
    <∣> map ⊥L (find ⊥′ Γ)
    <∣> fromHyps m Γ G

  -- axioms and right rules (decompose the goal)
  right : ∀ {n} → ℕ → (Γ : List (Formula n)) (G : Formula n) → Maybe (Γ ⊢ G)
  right m Γ ⊤′       = just ⊤R
  right m Γ (atom k) = map init (find (atom k) Γ)
  right m Γ ⊥′       = nothing
  right m Γ (A ⇒′ B) = map ⊃R (search m (A ∷ Γ) B)
  right m Γ (A ∨′ B) = map ∨R₁ (search m Γ A) <∣> map ∨R₂ (search m Γ B)
  right m Γ (A ∧′ B) = case search m Γ A of λ where
    (just d) → map (∧R d) (search m Γ B)
    nothing  → nothing

  -- left rules: try each hypothesis in turn
  fromHyps : ∀ {n} → ℕ → (Γ : List (Formula n)) (G : Formula n) → Maybe (Γ ⊢ G)
  fromHyps {n} m Γ G = go Γ (λ z → z)
    where
    go : (Δ : List (Formula n)) → (∀ {x} → x ∈ Δ → x ∈ Γ) → Maybe (Γ ⊢ G)
    go []      f = nothing
    go (χ ∷ Δ) f = tryHyp m Γ G χ (f (here refl)) <∣> go Δ (λ z → f (there z))

  -- the left rule selected by the shape of hypothesis χ (located by i)
  tryHyp : ∀ {n} → ℕ → (Γ : List (Formula n)) (G χ : Formula n) → χ ∈ Γ → Maybe (Γ ⊢ G)
  tryHyp m Γ G (A ∧′ B) i = map (∧L i) (search m (A ∷ B ∷ (Γ ∖ i)) G)
  tryHyp m Γ G (A ∨′ B) i = case search m (A ∷ (Γ ∖ i)) G of λ where
    (just d) → map (∨L i d) (search m (B ∷ (Γ ∖ i)) G)
    nothing  → nothing
  tryHyp m Γ G (⊤′      ⇒′ B) i = map (⊃L⊤ i) (search m (B ∷ (Γ ∖ i)) G)
  tryHyp m Γ G (⊥′      ⇒′ B) i = map (⊃L⊥ i) (search m (Γ ∖ i) G)
  tryHyp m Γ G (atom k  ⇒′ B) i = case find (atom k) (Γ ∖ i) of λ where
    (just j) → map (⊃Lat i j) (search m (B ∷ (Γ ∖ i)) G)
    nothing  → nothing
  tryHyp m Γ G ((C ∧′ D) ⇒′ B) i = map (⊃L∧ i) (search m ((C ⇒′ (D ⇒′ B)) ∷ (Γ ∖ i)) G)
  tryHyp m Γ G ((C ∨′ D) ⇒′ B) i = map (⊃L∨ i) (search m ((C ⇒′ B) ∷ (D ⇒′ B) ∷ (Γ ∖ i)) G)
  tryHyp m Γ G ((C ⇒′ D) ⇒′ B) i = case search m ((D ⇒′ B) ∷ (Γ ∖ i)) (C ⇒′ D) of λ where
    (just d) → map (⊃L⊃ i d) (search m (B ∷ (Γ ∖ i)) G)
    nothing  → nothing
  tryHyp m Γ G _ i = nothing
