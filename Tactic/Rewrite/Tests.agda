{-# OPTIONS --without-K #-}
-- {-# OPTIONS -v tactic.rewrite:100 #-}
module Tactic.Rewrite.Tests where

open import Data.List.NonEmpty using (List⁺; _∷_)
open import Data.Nat hiding (_≟_; _^_)
open import Data.Nat.Properties using (≤-refl) renaming (m≤n⇒m≤1+n to ≤-step)
open import Data.Maybe.Relation.Unary.Any using (just)

open import Class.DecEq

open import Meta.Prelude hiding (_^_)
open import Tactic.Rewrite

rw-just : ∀ {m} {n : ℕ} → m ≡ just n → Is-just m
rw-just eq
  -- rewrite eq = M.Any.just tt
  -- = subst Is-just (sym eq) (M.Any.just tt)
  = eq ≈: just tt
  -- = just tt :≈ eq -- does not work

postulate
  X : Set
  a b : X
  eq : a ≡ b

  P : X → Set
  Pa : P a

-- syntactic sugar for giving multiple terms of the same type
-- only the first is actually returned, but all are type-checked
_∋⋮_ : (A : Set ℓ) → List⁺ A → A
_∋⋮_ _ (x ∷ _) = x
pattern _⋮_ x xs = x ∷ xs
pattern _⋮_ x xs = x ∷ xs
pattern _⋮∅ x = x ∷ []
infixl -10 _∋⋮_
infixr -9  _⋮_
infix  -8  _⋮∅

_ = ∃ (_≤ 3)
 ∋⋮ 3 , ≤-refl
  ⋮ 2 , ≤-step ≤-refl
  ⋮ 1 , ≤-step (≤-step ≤-refl)
  ⋮ 0 , ≤-step (≤-step (≤-step ≤-refl))
  ⋮∅


_ = P b
 ∋⋮ subst (λ x → P x) eq Pa
  ⋮ Pa :≈ eq
  ⋮ sym eq ≈: Pa
  ⋮∅

_ = P a ≡ P b
 ∋⋮ subst (λ x → P a ≡ P x) eq refl
  ⋮ subst (λ x → P x ≡ P b) (sym eq) refl
  ⋮ eq ≈: refl
  ⋮ sym eq ≈: refl
  ⋮ ⟪ _== 1 ⟫ refl {x = P a} :≈ eq
  ⋮ ⟪[ 1 , 2 , 3 ]⟫ refl {x = P a} :≈ eq
  ⋮∅

postulate
  P² : X → X → Set
  P²a : P² a a

_ = P² b b
 ∋⋮ subst (λ x → P² x x) eq P²a
  ⋮ P²a :≈ eq
  ⋮ sym eq ≈: P²a
  ⋮∅

postulate
  P³ : X → X → X → Set
  P³a : P³ a b a

_ = P³ b a a
 ∋⋮ ⟪[ 1 ]⟫ (⟪[ 0 ]⟫ P³a :≈ eq) :≈ sym eq
  ⋮ ⟪[ 0 ]⟫ eq ≈: ⟪[ 0 ]⟫ P³a :≈ eq
  ⋮∅

postulate g : P b → X

_ = (∃ λ (A : Set) → A)
 ∋⋮ (-, g (Pa :≈ eq))
  ⋮ (-, g (sym eq ≈: Pa))
  ⋮∅

postulate
  f : P a ≡ P b → X
  f′ : (P a ≡ P b) × (P b ≡ P a) → X

rw-in-argument : X
rw-in-argument = f Pa≡Pb
  where Pa≡Pb : P a ≡ P b
        Pa≡Pb rewrite eq = refl

_ = X
 ∋⋮ f $ subst (λ x → P a ≡ P x) eq refl
  ⋮ f $ subst (λ x → P x ≡ P b) (sym eq) refl
  ⋮ (f $ ⟪ _== 1 ⟫ refl {x = P a} :≈ eq)
  ⋮ f $ eq ≈: refl
  ⋮∅

_ = X
 ∋⋮ f′ $ eq     ≈: (refl , refl)
  ⋮ f′ $ sym eq ≈: (refl , refl)
  ⋮∅
