{-# OPTIONS --safe --without-K #-}
module Class.HasHsType.Instances where

open import Meta.Prelude

open import Class.HasHsType.Core

instance
  iHsTy-ℕ      = mkHsType ℕ ℕ
  iHsTy-Bool   = mkHsType Bool Bool
  iHsTy-⊤      = mkHsType ⊤ ⊤
  iHsTy-String = mkHsType String String

-- TODO: macro for these kind of congruence instances
module _ ⦃ _ : HasHsType A ⦄ where instance
  iHsTy-List : HasHsType (List A)
  iHsTy-List .HasHsType.HsType = List (HsType A)

  iHsTy-Maybe : HasHsType (Maybe A)
  iHsTy-Maybe .HasHsType.HsType = Maybe (HsType A)

  iHsTy-Fun : ⦃ HasHsType B ⦄ → HasHsType (A → B)
  iHsTy-Fun {B = B} .HasHsType.HsType = HsType A → HsType B
