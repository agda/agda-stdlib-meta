{-# OPTIONS --safe --without-K #-}
--------------------------------------------------------------------------------
-- First-order solver, propositional core:
--   * a deep embedding of (intuitionistic) propositional formulas,
--   * their denotation into Agda `Set`s,
--   * the contraction-free sequent calculus G4ip (Dyckhoff's LJT) as the
--     certificate calculus, and
--   * soundness: a derivation interprets into an inhabitant of the denotation.
--
-- G4ip is chosen because its shape-split implication-left rules make proof
-- search terminating and complete for intuitionistic propositional logic: every
-- left rule *deletes* its principal formula (`Γ ∖ i`), so nothing is ever
-- reprocessed. Search (which produces derivations) is still not part of the
-- trusted base: it only has to return a `Γ ⊢ φ`, which `soundness` turns into a
-- real proof. Bugs in search show up as failure, never as unsoundness.
--------------------------------------------------------------------------------

module Tactic.FirstOrder.Core where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin; zero; suc)
open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat using (ℕ; suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_])
open import Data.Unit using (⊤; tt)
open import Level using (Level; 0ℓ; _⊔_; Setω)
open import Relation.Binary.PropositionalEquality using (refl)

private
  variable
    n : ℕ
    λs : Fin n → Level

--------------------------------------------------------------------------------
-- Syntax
--
-- `n` is the number of distinct atomic propositions; the reifier will collect
-- the atoms occurring in a goal into an environment and index them by `Fin n`.
--------------------------------------------------------------------------------

infixr 7 _∧′_
infixr 6 _∨′_
infixr 5 _⇒′_
infix  8 ¬′_

data Formula (n : ℕ) : Set where
  atom        : Fin n → Formula n
  ⊤′ ⊥′       : Formula n
  _∧′_ _∨′_ _⇒′_ : Formula n → Formula n → Formula n

¬′_ : Formula n → Formula n
¬′ φ = φ ⇒′ ⊥′

--------------------------------------------------------------------------------
-- Denotation
--
-- Each atom may live at its own level: an environment assigns levels `λs i` to
-- the atoms and types `ρ i : Set (λs i)`. A formula's denotation then sits at
-- the join `levels φ λs` of the levels it mentions (with `⊤′`/`⊥′` the genuine
-- `Set₀` units, not lifted copies — so monomorphic `⊤`/`⊥`/`¬_` goals are
-- matched exactly). This is the most permissive scheme: a goal may freely mix
-- hypotheses at different levels.
--
-- The environment is an `Env`: a cons-list whose index *constructs* `λs` via
-- `_◂_`. That is what lets the reflection macro emit a flat `A ∷ … ∷ []` and
-- have `n`, `λs` and `ρ = lookupᴱ` all inferred, sidestepping both the `Setω`
-- function type and higher-order unification of `λs`.
--------------------------------------------------------------------------------

infixr 5 _◂_ _∷_

_◂_ : Level → (Fin n → Level) → (Fin (suc n) → Level)
(ℓ ◂ λs) zero    = ℓ
(ℓ ◂ λs) (suc i) = λs i

data Env : (n : ℕ) → (Fin n → Level) → Setω where
  []  : Env 0 (λ ())
  _∷_ : ∀ {ℓ n} {λs : Fin n → Level} → Set ℓ → Env n λs → Env (suc n) (ℓ ◂ λs)

lookupᴱ : Env n λs → (i : Fin n) → Set (λs i)
lookupᴱ (A ∷ _)  zero    = A
lookupᴱ (_ ∷ as) (suc i) = lookupᴱ as i

levels : Formula n → (Fin n → Level) → Level
levels (atom i) λs = λs i
levels ⊤′       λs = 0ℓ
levels ⊥′       λs = 0ℓ
levels (φ ∧′ ψ) λs = levels φ λs ⊔ levels ψ λs
levels (φ ∨′ ψ) λs = levels φ λs ⊔ levels ψ λs
levels (φ ⇒′ ψ) λs = levels φ λs ⊔ levels ψ λs

⟦_⟧ : (φ : Formula n) (λs : Fin n → Level) → ((i : Fin n) → Set (λs i)) → Set (levels φ λs)
⟦ atom i ⟧ λs ρ = ρ i
⟦ ⊤′     ⟧ λs ρ = ⊤
⟦ ⊥′     ⟧ λs ρ = ⊥
⟦ φ ∧′ ψ ⟧ λs ρ = ⟦ φ ⟧ λs ρ × ⟦ ψ ⟧ λs ρ
⟦ φ ∨′ ψ ⟧ λs ρ = ⟦ φ ⟧ λs ρ ⊎ ⟦ ψ ⟧ λs ρ
⟦ φ ⇒′ ψ ⟧ λs ρ = ⟦ φ ⟧ λs ρ → ⟦ ψ ⟧ λs ρ

levelsᶜ : List (Formula n) → (Fin n → Level) → Level
levelsᶜ []      λs = 0ℓ
levelsᶜ (φ ∷ Γ) λs = levels φ λs ⊔ levelsᶜ Γ λs

⟦_⟧ᶜ : (Γ : List (Formula n)) (λs : Fin n → Level) → ((i : Fin n) → Set (λs i)) → Set (levelsᶜ Γ λs)
⟦ []    ⟧ᶜ λs ρ = ⊤
⟦ φ ∷ Γ ⟧ᶜ λs ρ = ⟦ φ ⟧ λs ρ × ⟦ Γ ⟧ᶜ λs ρ

--------------------------------------------------------------------------------
-- Context deletion: remove the hypothesis pointed at by a membership proof.
-- Used by the left rules to discard their principal formula.
--------------------------------------------------------------------------------

infixl 5 _∖_
_∖_ : (Γ : List (Formula n)) {φ : Formula n} → φ ∈ Γ → List (Formula n)
(_ ∷ Γ) ∖ here _  = Γ
(x ∷ Γ) ∖ there i = x ∷ (Γ ∖ i)

--------------------------------------------------------------------------------
-- Certificate calculus: Dyckhoff's contraction-free sequent calculus G4ip.
--------------------------------------------------------------------------------

infix 2 _⊢_

data _⊢_ {n} : List (Formula n) → Formula n → Set where
  -- axioms
  init : ∀ {Γ k}     → atom k ∈ Γ                         → Γ ⊢ atom k
  ⊤R   : ∀ {Γ}                                            → Γ ⊢ ⊤′
  ⊥L   : ∀ {Γ G}     → ⊥′ ∈ Γ                             → Γ ⊢ G
  -- right rules
  ∧R   : ∀ {Γ A B}   → Γ ⊢ A → Γ ⊢ B                      → Γ ⊢ A ∧′ B
  ∨R₁  : ∀ {Γ A B}   → Γ ⊢ A                              → Γ ⊢ A ∨′ B
  ∨R₂  : ∀ {Γ A B}   → Γ ⊢ B                              → Γ ⊢ A ∨′ B
  ⊃R   : ∀ {Γ A B}   → A ∷ Γ ⊢ B                          → Γ ⊢ A ⇒′ B
  -- invertible left rules
  ∧L   : ∀ {Γ A B G} → (i : A ∧′ B ∈ Γ) → A ∷ B ∷ (Γ ∖ i) ⊢ G → Γ ⊢ G
  ∨L   : ∀ {Γ A B G} → (i : A ∨′ B ∈ Γ) → A ∷ (Γ ∖ i) ⊢ G → B ∷ (Γ ∖ i) ⊢ G → Γ ⊢ G
  -- implication-left, split by the shape of the antecedent
  ⊃L⊤  : ∀ {Γ B G}     → (i : ⊤′ ⇒′ B ∈ Γ)        → B ∷ (Γ ∖ i) ⊢ G → Γ ⊢ G
  ⊃L⊥  : ∀ {Γ B G}     → (i : ⊥′ ⇒′ B ∈ Γ)        → (Γ ∖ i) ⊢ G → Γ ⊢ G
  ⊃Lat : ∀ {Γ k B G}   → (i : atom k ⇒′ B ∈ Γ)    → atom k ∈ (Γ ∖ i) → B ∷ (Γ ∖ i) ⊢ G → Γ ⊢ G
  ⊃L∧  : ∀ {Γ C D B G} → (i : (C ∧′ D) ⇒′ B ∈ Γ)  → (C ⇒′ (D ⇒′ B)) ∷ (Γ ∖ i) ⊢ G → Γ ⊢ G
  ⊃L∨  : ∀ {Γ C D B G} → (i : (C ∨′ D) ⇒′ B ∈ Γ)  → (C ⇒′ B) ∷ (D ⇒′ B) ∷ (Γ ∖ i) ⊢ G → Γ ⊢ G
  ⊃L⊃  : ∀ {Γ C D B G} → (i : (C ⇒′ D) ⇒′ B ∈ Γ)
       → (D ⇒′ B) ∷ (Γ ∖ i) ⊢ C ⇒′ D → B ∷ (Γ ∖ i) ⊢ G → Γ ⊢ G

--------------------------------------------------------------------------------
-- Soundness: interpret a derivation into an inhabitant of the denotation.
-- This is the entire trusted base of the solver.
--------------------------------------------------------------------------------

private
  ρ-syntax : (λs : Fin n → Level) → Setω
  ρ-syntax {n} λs = (i : Fin n) → Set (λs i)

look : ∀ {φ Γ} (ρ : ρ-syntax λs) → φ ∈ Γ → ⟦ Γ ⟧ᶜ λs ρ → ⟦ φ ⟧ λs ρ
look ρ (here refl) (x , _) = x
look ρ (there i)   (_ , γ) = look ρ i γ

drop : ∀ {φ Γ} (ρ : ρ-syntax λs) (i : φ ∈ Γ) → ⟦ Γ ⟧ᶜ λs ρ → ⟦ Γ ∖ i ⟧ᶜ λs ρ
drop ρ (here refl) (_ , γ) = γ
drop ρ (there i)   (x , γ) = x , drop ρ i γ

soundness : ∀ {Γ G} (ρ : ρ-syntax λs) → Γ ⊢ G → ⟦ Γ ⟧ᶜ λs ρ → ⟦ G ⟧ λs ρ
soundness ρ (init i)    γ = look ρ i γ
soundness ρ ⊤R          γ = tt
soundness ρ (⊥L i)      γ = ⊥-elim (look ρ i γ)
soundness ρ (∧R d e)    γ = soundness ρ d γ , soundness ρ e γ
soundness ρ (∨R₁ d)     γ = inj₁ (soundness ρ d γ)
soundness ρ (∨R₂ d)     γ = inj₂ (soundness ρ d γ)
soundness ρ (⊃R d)      γ = λ a → soundness ρ d (a , γ)
soundness ρ (∧L i d)    γ = soundness ρ d (proj₁ (look ρ i γ) , proj₂ (look ρ i γ) , drop ρ i γ)
soundness ρ (∨L i d e)  γ = [ (λ a → soundness ρ d (a , drop ρ i γ))
                            , (λ b → soundness ρ e (b , drop ρ i γ)) ] (look ρ i γ)
soundness ρ (⊃L⊤ i d)   γ = soundness ρ d (look ρ i γ tt , drop ρ i γ)
soundness ρ (⊃L⊥ i d)   γ = soundness ρ d (drop ρ i γ)
soundness ρ (⊃Lat i j d) γ = soundness ρ d (look ρ i γ (look ρ j (drop ρ i γ)) , drop ρ i γ)
soundness ρ (⊃L∧ i d)   γ = soundness ρ d ((λ c e → look ρ i γ (c , e)) , drop ρ i γ)
soundness ρ (⊃L∨ i d)   γ = soundness ρ d ( (λ c → look ρ i γ (inj₁ c))
                                          , (λ e → look ρ i γ (inj₂ e))
                                          , drop ρ i γ)
soundness ρ (⊃L⊃ i d e) γ =
  soundness ρ e (look ρ i γ (soundness ρ d ((λ z → look ρ i γ (λ _ → z)) , drop ρ i γ)) , drop ρ i γ)

-- specialised to the empty context: the entry point the reflection macro uses
solve : ∀ {φ} (ρ : ρ-syntax λs) → [] ⊢ φ → ⟦ φ ⟧ λs ρ
solve ρ p = soundness ρ p tt
