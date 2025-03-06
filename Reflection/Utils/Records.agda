{-# OPTIONS --safe --without-K #-}
module Reflection.Utils.Records where

open import Meta.Prelude
open import Meta.Init

open import Data.List using (map)
open import Class.DecEq using (_==_)

mkRecord : List (Name × Term) → Term
mkRecord fs = pat-lam (map (λ (fn , e) → clause [] [ vArg (proj fn) ] e) fs) []

updateField : List Name → Term → Name → Term → Term
updateField fs rexp fn fexp =
  flip pat-lam [] $ flip map fs $ λ f →
    clause [] [ vArg (proj f) ] $
      if f == fn then fexp else (f ∙⟦ rexp ⟧)
