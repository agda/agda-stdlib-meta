{-# OPTIONS --safe --without-K #-}

module Reflection.Debug where

open import Meta.Prelude hiding (⊤; _∧_; _∨_; filter)

import Data.Bool as B
import Data.String as S
open import Data.Char
open import Data.List using (map)

open import Relation.Nullary.Decidable using (⌊_⌋)

open import Reflection

record IsErrorPart (A : Set) : Set where
  field toErrorPart : A → ErrorPart

open IsErrorPart ⦃...⦄ public

instance
  IsErrorPart-String : IsErrorPart String
  IsErrorPart-String .toErrorPart = ErrorPart.strErr

  IsErrorPart-Term : IsErrorPart Term
  IsErrorPart-Term .toErrorPart = ErrorPart.termErr

  IsErrorPart-Name : IsErrorPart Name
  IsErrorPart-Name .toErrorPart = ErrorPart.nameErr

  IsErrorPart-Pattern : IsErrorPart Pattern
  IsErrorPart-Pattern .toErrorPart = ErrorPart.pattErr

  IsErrorPart-Clause : IsErrorPart Clause
  IsErrorPart-Clause .toErrorPart c = ErrorPart.termErr (pat-lam [ c ] [])

  IsErrorPart-ListClause : IsErrorPart (List Clause)
  IsErrorPart-ListClause .toErrorPart cs = ErrorPart.termErr (pat-lam cs [])

infixr 5 _∷ᵈ_ _++ᵈ_
_∷ᵈ_ : A → ⦃ _ : IsErrorPart A ⦄ → List ErrorPart → List ErrorPart
e ∷ᵈ es = toErrorPart e ∷ es

_++ᵈ_ : List A → ⦃ _ : IsErrorPart A ⦄ → List ErrorPart → List ErrorPart
es ++ᵈ es' = map toErrorPart es ++ es'

_ᵈ : ⦃ _ : IsErrorPart A ⦄ → List A → List ErrorPart
_ᵈ = map toErrorPart

data DebugSelection : Set where
  FullPath : DebugSelection
  Last     : DebugSelection
  All      : DebugSelection
  Custom   : (List String → String) → DebugSelection

-- If All is selected, this pragma shows all debug info
-- {-# OPTIONS -v allTactics:100 #-}

Filter : Set
Filter = List String → Bool

module Filter where
  open import Algebra.Lattice
  open import Data.Bool.Properties
  import Algebra.Function

  Filter-Alg : BooleanAlgebra _ _
  Filter-Alg = Algebra.Function.hom (List String) ∨-∧-booleanAlgebra

  open BooleanAlgebra Filter-Alg public

  private
    _≣_ : String → String → Bool
    s ≣ s' = ⌊ s S.≟ s' ⌋

  contains : String → Filter
  contains s l = foldl (λ acc s' → acc B.∨ s ≣ s') false l

  noneOf : List String → Filter
  noneOf [] = ⊤
  noneOf (x ∷ l) = ¬ contains x ∧ noneOf l

  endsWith : String → Filter
  endsWith s l with last l
  ... | just x  = s ≣ x
  ... | nothing = false

  beginsWith : String → Filter
  beginsWith s l with head l
  ... | just x  = s ≣ x
  ... | nothing = false

record DebugOptions : Set where
  field
    path      : List String
    selection : DebugSelection
    filter    : Filter
    level     : ℕ
    prefix    : Char

defaultDebugOptions : DebugOptions
defaultDebugOptions = record
  { path = []; selection = All; filter = Filter.⊤; level = 100; prefix = '|' }

specializeDebugOptions : DebugOptions → DebugOptions → DebugOptions
specializeDebugOptions record { path = path₁ } opts@record { path = path₂ } =
  record opts { path = path₁ ++ path₂ }

debugOptionsPath : DebugOptions → String
debugOptionsPath record { path = path ; selection = FullPath } = S.intersperse "/" path
debugOptionsPath record { path = path ; selection = Last } with last path
... | just x  = x
... | nothing = ""
debugOptionsPath record { path = path ; selection = All } = "allTactics"
debugOptionsPath record { path = path ; selection = Custom f } = f path

debugPrintPrefix : DebugOptions → ErrorPart
debugPrintPrefix o = let open DebugOptions o in strErr (S.replicate (length path) prefix)
