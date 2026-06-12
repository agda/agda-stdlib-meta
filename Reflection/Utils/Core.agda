{-# OPTIONS --safe --without-K #-}
module Reflection.Utils.Core where

open import Meta.Prelude
open import Meta.Init

open import Data.Product using (map₁)
open import Data.List using (map; findIndexᵇ)
import Data.List as List
import Data.Maybe as Maybe
import Data.Fin as Fin
import Reflection.AST.Name as Name
open import Reflection.AST.AlphaEquality using (_=α=_)
open import Reflection.AST.Literal using (nat)

import Reflection.AST.Abstraction as Abs
import Reflection.AST.Argument as Arg
open import Reflection.Utils.Args using (vArgs)

-- ** basics

absName : Abs A → String
absName (abs s x) = s

tyName : Type → Maybe Name
tyName = λ where
  (con n _) → just n
  (def n _) → just n
  _         → nothing

insertName : Name → List Name → List Name
insertName n []       = n ∷ []
insertName n (m ∷ ms) = if n Name.≡ᵇ m then m ∷ ms else m ∷ insertName n ms

-- Boolean equality on optional names. Deliberately *not*
-- `Class.DecEq`'s `_==_`: this sits on solver hot paths
-- and measured ~15% slower per macro call.
_≡ᵐ_ : Maybe Name → Maybe Name → Bool
just n  ≡ᵐ just m  = n Name.≡ᵇ m
nothing ≡ᵐ nothing = true
_       ≡ᵐ _       = false

-- Peels leading λ-binders before reading the head Name.
headName : Term → Maybe Name
headName (def nm _)            = just nm
headName (lam _ (abs _ body))  = headName body
headName _                     = nothing

-- Insert the def-name of `t` to `xs`, η-contract if required
pickDefName : Term → List Name → List Name
pickDefName t xs = Maybe.maybe′ (λ n → insertName n xs) xs (headName t)

-- Extract a `ℕ` value from a term shaped as `lit (nat n)` or a chain
-- of `suc`/`zero` constructors.
extractNat : Term → Maybe ℕ
extractNat (lit (nat n))        = just n
extractNat (quote ℕ.zero ◆)     = just 0
extractNat (quote ℕ.suc ◆⟦ x ⟧) = Maybe.map ℕ.suc (extractNat x)
extractNat _ = nothing

-- For wrapped numeric carriers like ℤ's `+_`: peel one
-- `con C (n ∷ [])` layer.
peelLitCon : Name → Term → Maybe ℕ
peelLitCon C (con nm xs) = case nm Name.≡ᵇ C of λ where
  false → nothing
  true  → case vArgs xs of λ where
    (a ∷ []) → extractNat a
    _        → nothing
peelLitCon _ _ = nothing

-- `extractNat`, also accepting numerals under the given wrapper.
extractCarrierNat : Maybe Name → Term → Maybe ℕ
extractCarrierNat mC t = case extractNat t of λ where
  (just n) → just n
  nothing  → case mC of λ where
    (just C) → peelLitCon C t
    nothing  → nothing

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
