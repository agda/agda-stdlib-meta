{-# OPTIONS --safe --without-K #-}
module Reflection.Utils.Records where

open import Meta.Prelude
open import Meta.Init

open import Data.List using (map)
open import Class.DecEq using (_==_)

open import Reflection.AST.Term using (_⋯⟅∷⟆_)
open import Reflection.TCM.Syntax using (_>>=_)
open import Reflection.Utils.Reduction using (headReduce; resolveToName)
import Agda.Builtin.Reflection as B using (TC)

mkRecord : List (Name × Term) → Term
mkRecord fs = pat-lam (map (λ (fn , e) → clause [] [ vArg (proj fn) ] e) fs) []

updateField : List Name → Term → Name → Term → Term
updateField fs rexp fn fexp =
  flip pat-lam [] $ flip map fs $ λ f →
    clause [] [ vArg (proj f) ] $
      if f == fn then fexp else (f ∙⟦ rexp ⟧)

------------------------------------------------------------------------
-- Projecting reasonable terms of fields out of record value
--
-- Getting a field from a record value in such a way that we don't
-- reduce too little or to much is quite delicate. For example, from the
-- semiring ℚ, the `1#` field should give us `1ℚ`, never its `mkℚ ...`
-- unfolding. `projectField` handles this appropriately.

private
  fieldFuel : ℕ
  fieldFuel = 16

module _ (k : ℕ) (r : Term) (f : Name) where

  fieldProjection : Term
  fieldProjection = def f (k ⋯⟅∷⟆ r ⟨∷⟩ [])

  projectField : B.TC Term
  projectField = do
    r' ← headReduce fieldFuel r
    resolveToName (stuckOn r') fieldFuel fieldProjection
    where
      stuckOn : Term → List Name
      stuckOn (def nm _) = nm ∷ []
      stuckOn _          = []
