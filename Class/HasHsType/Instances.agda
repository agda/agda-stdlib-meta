module Class.HasHsType.Instances where

open import Meta.Prelude

open import Foreign.Haskell.Pair using (Pair)
open import Foreign.Haskell.Either using (Either)

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

  module _ ⦃ _ : HasHsType B ⦄ where instance
    iHsTy-Fun : HasHsType (A → B)
    iHsTy-Fun .HasHsType.HsType = HsType A → HsType B

    iHsTy-Sum : HasHsType (A ⊎ B)
    iHsTy-Sum .HasHsType.HsType = Either (HsType A) (HsType B)

    iHsTy-Pair : HasHsType (A × B)
    iHsTy-Pair .HasHsType.HsType = Pair (HsType A) (HsType B)
