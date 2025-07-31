{-# OPTIONS --safe --without-K #-}
module Reflection.Utils.Core where

open import Meta.Prelude
open import Meta.Init

open import Data.Product using (map₁)
open import Data.List using (map)

import Reflection.AST.Abstraction as Abs
import Reflection.AST.Argument as Arg

-- ** basics

absName : Abs A → String
absName (abs s x) = s

tyName : Type → Maybe Name
tyName = λ where
  (con n _) → just n
  (def n _) → just n
  _         → nothing

-- ** alternative view of function types as a pair of a list of arguments and a return type
TypeView = List (Abs (Arg Type)) × Type

viewTy : Type → TypeView
viewTy (Π[ s ∶ a ] ty) = map₁ ((abs s a) ∷_) (viewTy ty)
viewTy ty              = [] , ty

tyView : TypeView → Type
tyView ([] , ty) = ty
tyView (abs s a ∷ as , ty) = Π[ s ∶ a ] tyView (as , ty)

argumentWise : (Type → Type) → Type → Type
argumentWise f ty =
  let
    as , r = viewTy ty
    as′ = map (Abs.map $ Arg.map f) as
  in tyView (as′ , r)

viewTy′ : Type → Args Type × Type
viewTy′ (Π[ _ ∶ a ] ty) = map₁ (a ∷_) (viewTy′ ty)
viewTy′ ty              = [] , ty

argTys : Type → Args Type
argTys = proj₁ ∘ viewTy′

resultTy : Type → Type
resultTy = proj₂ ∘ viewTy′

tyTele : Type → Telescope
tyTele = λ where
  (Π[ s ∶ a ] ty) → (s , a) ∷ tyTele ty
  _ → []

-- ** definitions

record DataDef : Set where
  field
    name : Name
    constructors : List (Name × TypeView)
    params : List (Abs (Arg Type))
    indices : List (Abs (Arg Type))

record RecordDef : Set where
  field
    name : Name
    fields : List (Arg Name)
    params : List (Abs (Arg Type))

parameters : Definition → ℕ
parameters (data-type pars _) = pars
parameters _                  = 0

-- ** telescopes

toTelescope : List (Abs (Arg Type)) → Telescope
toTelescope = map (λ where (abs n x) → (n , x))

fromTelescope : Telescope → List (Abs (Arg Type))
fromTelescope = map (λ where (n , x) → (abs n x))
