{-# OPTIONS --safe --without-K #-}

module Reflection.QuotedDefinitions where

open import Meta.Prelude

open import Reflection.Syntax

infix 4 _`≡_ _``≡_
_`≡_ : Term → Term → Term
t `≡ t' = quote _≡_ ∙⟦ t ∣ t' ⟧

pattern _``≡_ t t' = def (quote _≡_) (_ ∷ _ ∷ vArg t ∷ vArg t' ∷ [])

`refl : Term
`refl = quote refl ◆

pattern ``refl = quote refl ◇

`case_of_ : Term → Term → Term
`case t of t' = quote case_of_ ∙⟦ t ∣ t' ⟧

-- Syntax for quoting `yes` and `no`
open import Relation.Nullary

`yes `no : Term → Term
`yes x = quote _because_ ◆⟦ quote true  ◆ ∣ quote ofʸ ◆⟦ x ⟧ ⟧
`no  x = quote _because_ ◆⟦ quote false ◆ ∣ quote ofⁿ ◆⟦ x ⟧ ⟧

pattern ``yes x = quote _because_ ◇⟦ quote true  ◇ ∣ quote ofʸ ◇⟦ x ⟧ ⟧
pattern ``no x  = quote _because_ ◇⟦ quote false ◇ ∣ quote ofⁿ ◇⟦ x ⟧ ⟧
