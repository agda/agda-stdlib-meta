{-# OPTIONS --without-K #-}
module Class.Convertible.Foreign where

open import Meta.Prelude

open import Class.Functor
open import Class.Bifunctor

open import Class.Convertible.Core
open import Class.HasHsType.Core

open import Foreign.Haskell using (Pair; Either)
open import Foreign.Haskell.Coerce using (coerce)

instance
  Convertible-Pair : Convertible₂ _×_ Pair
  Convertible-Pair = λ where
    .to   → coerce ∘ bimap to to
    .from → bimap from from ∘ coerce

  Convertible-Either : Convertible₂ _⊎_ Either
  Convertible-Either = λ where
    .to   → coerce ∘ bimap to to
    .from → bimap from from ∘ coerce
