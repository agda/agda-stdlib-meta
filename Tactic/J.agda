{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- J: solve the goal by path-induction
--
-- this is quantified over the names of `J` and `refl`, so you should import it
-- via `open import Tactic.J (quote J) (quote refl)`
--------------------------------------------------------------------------------

open import Meta.Init

module Tactic.J (J-name refl-name : Name) where

open import Meta.Prelude hiding (J)

open import Class.Monad
open import Class.MonadError
open import Class.MonadTC

open import Reflection.AntiUnification
open import Reflection.Tactic
open import Reflection.Utils.TCI

open MonadTC ⦃...⦄
open MonadError ⦃...⦄

private
  J-tac : Name → Name → ⦃ _ : TCOptions ⦄ → Term → Term → Tactic
  J-tac J-name refl-name t t' = initTac $ inDebugPath "J" do
    ty ← goalTy
    debugLog ("anti-unify " ∷ᵈ ty ∷ᵈ [])
    ty' ← inferType t
    debugLog ("with:      " ∷ᵈ ty' ∷ᵈ [])
    let gen = `λ⟦ "x" ∣ "y" ⇒ antiUnify 0 ty ty' ⟧
    debugLog (gen ∷ᵈ [])
    unifyWithGoal (J-name ∙⟦ gen ∣ t ∣ t' ⟧)
    where
      reflHelper : Term → Term → ℕ
      reflHelper _ (con refl-name _) = 0
      reflHelper _ _ = 1

      open AntiUnification reflHelper 2

macro
  by-J = J-tac J-name refl-name

private
  module Test where
    open import Relation.Binary.PropositionalEquality hiding (J)
    open ≡-Reasoning
    open import Tactic.Defaults

    -- since we can't use names abstractly, we need to do some yoga here

    private variable
      x y z w : A

    J : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {x : A} (P : (y : A) → x ≡ y → Set ℓ₂)
      → P x refl → {y : A} (p : x ≡ y) → P y p
    J _ Px refl = Px

    macro
      by-Jᵗ = J-tac (quote J) (quote refl)

    -- in this case, by-Jᵗ needs a type annotation or it can't anti-unify properly
    _∙_ : x ≡ y → y ≡ z → x ≡ z
    _∙_ {x = x} {y} {z} p = by-Jᵗ (λ q → x ≡ z ∋ q) p

    ∙-id-l : (p : y ≡ z) → refl ∙ p ≡ p
    ∙-id-l refl = refl

    ∙-assoc : (p : w ≡ x) (q : x ≡ y) (r : y ≡ z) → p ∙ (q ∙ r) ≡ (p ∙ q) ∙ r
    ∙-assoc {w = w} {x} {y} {z} p = by-Jᵗ lemma p
      where
        lemma : (q : w ≡ y) (r : y ≡ z) → (refl ∙ (q ∙ r)) ≡ ((refl ∙ q) ∙ r)
        lemma q r = begin
          (refl ∙ (q ∙ r)) ≡⟨ ∙-id-l (q ∙ r) ⟩
          q ∙ r            ≡˘⟨ cong (λ x → x ∙ r) (∙-id-l q) ⟩
          (refl ∙ q) ∙ r   ∎
