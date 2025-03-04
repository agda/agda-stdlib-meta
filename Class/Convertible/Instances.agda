module Class.Convertible.Instances where

open import Meta.Prelude

open import Class.Functor
open import Class.Bifunctor

open import Class.Convertible.Core

open import Class.HasHsType.Core

HsConvertible : (A : Set) → ⦃ HasHsType A ⦄ → Set
HsConvertible A = Convertible A (HsType A)

open import Foreign.Haskell using (Pair; Either)
open import Foreign.Haskell.Coerce using (coerce)

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

  Convertible-Fun : ∀ {A A' B B'} →
    ⦃ Convertible A A' ⦄ → ⦃ Convertible B B' ⦄ → Convertible (A → B) (A' → B')
  Convertible-Fun = λ where
    .to   → λ f → to   ∘ f ∘ from
    .from → λ f → from ∘ f ∘ to
