module Class.Convertible.Core where

open import Meta.Prelude

open import Class.Core
open import Class.Functor
open import Class.Bifunctor

record Convertible (A B : Set) : Set where
  field to   : A → B
        from : B → A
open Convertible ⦃...⦄ public

Convertible-Refl : ∀ {A} → Convertible A A
Convertible-Refl = λ where .to → id; .from → id

Convertible₁ : (Set → Set) → (Set → Set) → Set₁
Convertible₁ T U = ∀ {A B} → ⦃ Convertible A B ⦄ → Convertible (T A) (U B)

Convertible₂ : (Set → Set → Set) → (Set → Set → Set) → Set₁
Convertible₂ T U = ∀ {A B} → ⦃ Convertible A B ⦄ → Convertible₁ (T A) (U B)

Functor⇒Convertible : ∀ {F : Type↑} → ⦃ Functor F ⦄ → Convertible₁ F F
Functor⇒Convertible = λ where
  .to   → fmap to
  .from → fmap from

Bifunctor⇒Convertible : ∀ {F} → ⦃ Bifunctor F ⦄ → Convertible₂ F F
Bifunctor⇒Convertible = λ where
  .to   → bimap to to
  .from → bimap from from

_⨾_ : ∀ {A B C} → Convertible A B → Convertible B C → Convertible A C
(c ⨾ c') .to   = c' .to   ∘ c  .to
(c ⨾ c') .from = c  .from ∘ c' .from
