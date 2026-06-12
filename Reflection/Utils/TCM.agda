{-# OPTIONS --safe --without-K #-}
module Reflection.Utils.TCM where

open import Reflection

import Class.Monad as C
import Class.MonadError as C
import Class.MonadReader as C
import Class.MonadTC as C
open import Reflection.Utils.TCI {TC} ⦃ C.Monad-TC ⦄ ⦃ C.MonadError-TC ⦄
  ⦃ record { ask = C.initTCEnv ; local = λ _ x → x } ⦄ ⦃ C.MonadTC-TC ⦄ public
