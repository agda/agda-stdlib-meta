module standard-library-meta where

open import Algebra.Function

open import Class.MonadReader
open import Class.MonadError
open import Class.MonadTC

open import Class.HasHsType
open import Class.HasHsType.Foreign
open import Class.Convertible
open import Class.Convertible.Foreign

open import Reflection.Syntax
open import Reflection.Debug
open import Reflection.Tactic
open import Reflection.TCI
open import Reflection.Utils
open import Reflection.Utils.Debug
open import Reflection.Utils.TCI
open import Reflection.Utils.TCM
open import Reflection.AlphaEquality
open import Reflection.AntiUnification

open import Tactic
