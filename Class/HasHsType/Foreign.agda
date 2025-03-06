{-# OPTIONS --without-K #-}
module Class.HasHsType.Foreign where

open import Meta.Prelude

open import Class.HasHsType.Core

open import Foreign.Haskell.Pair using (Pair)
open import Foreign.Haskell.Either using (Either)

module _ ⦃ _ : HasHsType A ⦄ ⦃ _ : HasHsType B ⦄ where instance

  iHsTy-Sum : HasHsType (A ⊎ B)
  iHsTy-Sum .HasHsType.HsType = Either (HsType A) (HsType B)

  iHsTy-Pair : HasHsType (A × B)
  iHsTy-Pair .HasHsType.HsType = Pair (HsType A) (HsType B)
