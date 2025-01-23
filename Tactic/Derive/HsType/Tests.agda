
open import Class.HasHsType
open import Tactic.Derive.HsType
open import Tactic.Derive.TestTypes

module Tactic.Derive.HsType.Tests where

{-# FOREIGN GHC
  {-# LANGUAGE NoImplicitPrelude #-}
#-}
{-# FOREIGN GHC import Prelude (Show, Eq, Bool, Integer) #-}
private
  HSTy-ℕ : HasHsType ℕ
  HSTy-ℕ = autoHsType ℕ

  HSTy-ℤ : HasHsType ℤ
  HSTy-ℤ = autoHsType ℤ

  data X : Set where
    MkX : (Bool → Bool) → X

  record RecX : Set where
    field f : (Bool → Bool)

  instance
    HSTy-E1 : HasHsType E1
    HSTy-E1 = autoHsType E1

    HSTy-X : HasHsType X
    HSTy-RecX : HasHsType RecX

    HSTy-X = autoHsType X
    HSTy-RecX = autoHsType RecX
