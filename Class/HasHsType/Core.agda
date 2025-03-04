module Class.HasHsType.Core where

open import Meta.Prelude

record HasHsType (A : Set ℓ) : Set₁ where
  field HsType : Set

module _ (A : Set ℓ) where
  mkHsType : Set → HasHsType A
  mkHsType Hs .HasHsType.HsType = Hs

  module _ ⦃ i : HasHsType A ⦄ where
    HsType : Set
    HsType = i .HasHsType.HsType
