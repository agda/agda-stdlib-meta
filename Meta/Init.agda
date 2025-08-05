{-# OPTIONS --safe --without-K #-}

module Meta.Init where

open import Reflection.Debug public
open import Reflection.TCI public
open import Reflection.Syntax public

instance
  iMonad-TC = Monad-TC
  iMonadTC-TCI = MonadTC-TCI
  iMonadReader-TC = MonadReader-TC
  iMonadError-TC = MonadError-TC
