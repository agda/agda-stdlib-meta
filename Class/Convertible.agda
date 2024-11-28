module Class.Convertible where

open import Function
open import Class.HasHsType
open import Class.Core
open import Class.Functor
open import Class.Bifunctor
open import Data.Maybe
open import Data.Product
open import Data.Sum
open import Data.List

record Convertible (A B : Set) : Set where
  field to   : A → B
        from : B → A
open Convertible ⦃...⦄ public

HsConvertible : (A : Set) → ⦃ HasHsType A ⦄ → Set
HsConvertible A = Convertible A (HsType A)

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

-- ** instances

open import Foreign.Haskell
open import Foreign.Haskell.Coerce using (coerce)

open import Data.Nat

instance
  Convertible-ℕ : Convertible ℕ ℕ
  Convertible-ℕ = λ where
    .to   → id
    .from → id

  Convertible-Maybe : Convertible₁ Maybe Maybe
  Convertible-Maybe = Functor⇒Convertible

  Convertible-× : Convertible₂ _×_ _×_
  Convertible-× = Bifunctor⇒Convertible

  Convertible-Pair : Convertible₂ _×_ Pair
  Convertible-Pair = λ where
    .to   → coerce ∘ bimap to to
    .from → bimap from from ∘ coerce

  Convertible-⊎ : Convertible₂ _⊎_ _⊎_
  Convertible-⊎ = Bifunctor⇒Convertible

  Convertible-Either : Convertible₂ _⊎_ Either
  Convertible-Either = λ where
    .to   → coerce ∘ bimap to to
    .from → bimap from from ∘ coerce

  Convertible-List : Convertible₁ List List
  Convertible-List = λ where
    .to   → fmap to
    .from → fmap from

  Convertible-Fun : ∀ {A A' B B'} → ⦃ Convertible A A' ⦄ → ⦃ Convertible B B' ⦄ → Convertible (A → B) (A' → B')
  Convertible-Fun = λ where
    .to   → λ f → to   ∘ f ∘ from
    .from → λ f → from ∘ f ∘ to
