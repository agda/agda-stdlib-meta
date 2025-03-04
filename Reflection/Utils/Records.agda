{-# OPTIONS --safe --without-K #-}
module Reflection.Utils.Records where

open import Meta.Prelude
open import Meta.Init

open import Data.List using (map)
open import Relation.Nullary.Decidable using (⌊_⌋)

import Reflection.AST.Name as Name

mkRecord : List (Name × Term) → Term
mkRecord fs = pat-lam (map (λ where (fn , e) → clause [] [ vArg (proj fn) ] e) fs) []

updateField : List Name → Term → Name → Term → Term
updateField fs rexp fn fexp =
  pat-lam (flip map fs $ λ f →
    if ⌊ f Name.≟ fn ⌋ then
      clause [] [ vArg (proj fn) ] fexp
    else
      clause [] [ vArg (proj f) ] (f ∙⟦ rexp ⟧)
    ) []
