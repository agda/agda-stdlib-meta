{-# OPTIONS --safe --without-K #-}
module Reflection.Utils where

open import Meta.Prelude
open import Meta.Init hiding (toℕ)

import Reflection.AST.Abstraction as Abs
import Reflection.AST.Name as Name
open import Reflection.AST.Argument as Arg hiding (map)
open import Reflection.AST.Argument.Information
open import Reflection.AST.Argument.Visibility as Vis

open import Data.Product using (map₁)
open import Data.List using (map; zip; zipWith)
open import Data.Nat using (_≤ᵇ_)
open import Data.Fin using (toℕ)

open import Relation.Nullary using (Dec)
open import Relation.Nullary.Decidable using (⌊_⌋)

private variable
  ℓ : Level
  A B : Set ℓ

-- alternative view of function types as a pair of a list of arguments and a return type
TypeView = List (Abs (Arg Type)) × Type

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

absName : Abs A → String
absName (abs s x) = s

getVisibility : ∀ {a} {A : Set a} → Arg A → Visibility
getVisibility (arg (arg-info v _) _) = v

findMetas : Term → List Term
findMetas' : List (Arg Term) → List Term
findMetasCl : List Clause → List Term

findMetas (var x args) = findMetas' args
findMetas (con c args) = findMetas' args
findMetas (def f args) = findMetas' args
findMetas (lam v (abs _ x)) = findMetas x
findMetas (pat-lam cs args) = findMetasCl cs Data.List.++ findMetas' args
findMetas (pi (arg _ a) (abs _ b)) = findMetas a Data.List.++ findMetas b
findMetas (agda-sort s) = []
findMetas (lit l) = []
findMetas m@(meta x args) = m ∷ findMetas' args
findMetas unknown = []

findMetas' [] = []
findMetas' ((arg _ t) ∷ ts) = findMetas t Data.List.++ findMetas' ts

findMetasCl [] = []
findMetasCl (Clause.clause tel ps t ∷ c) = findMetas t Data.List.++ findMetasCl c
findMetasCl (Clause.absurd-clause tel ps ∷ c) = findMetasCl c

isMeta : Term → Bool
isMeta (meta _ _) = true
isMeta _ = false

unArgs : Args A → List A
unArgs = map unArg

mapVariables : (ℕ → ℕ) → (Pattern → Pattern)
mapVariables f (Pattern.var n)      = Pattern.var (f n)
mapVariables f (Pattern.con c args) = Pattern.con c $ go args
  where
    go : List (Arg Pattern) → List (Arg Pattern)
    go [] = []
    go (arg i p ∷ l) = arg i (mapVariables f p) ∷ go l
mapVariables _ p                    = p

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

tyName : Type → Maybe Name
tyName (con n _) = just n
tyName (def n _) = just n
tyName _         = nothing

args : Term → Args Term
args (var _ xs)  = xs
args (def _ xs)  = xs
args (con _ xs)  = xs
args _           = []

args′ : Term → List Term
args′ = unArgs ∘ args

module _ (f : ℕ → ℕ) where

  private
    _⁇_ : ℕ → ℕ → ℕ
    bound ⁇ x = if bound ≤ᵇ x then f x else x

  mutual
    mapFreeVars : ℕ → (Term → Term)
    mapFreeVars bound = λ where
      (var x as)
        → var (bound ⁇ x) (mapFreeVars∗ bound as)
      (def c as)
        → def c (mapFreeVars∗ bound as)
      (con c as)
        → con c (mapFreeVars∗ bound as)
      (lam v (abs x t))
        → lam v (abs x (mapFreeVars (suc bound) t))
      (pat-lam cs as)
        → pat-lam (mapFreeVarsᶜ∗ bound cs) (mapFreeVars∗ bound as)
      (pi (arg i t) (abs x t′))
        → pi (arg i (mapFreeVars bound t)) (abs x (mapFreeVars (suc bound) t′))
      (agda-sort s)
        → agda-sort (mapFreeVarsˢ bound s)
      (meta x as)
        → meta x (mapFreeVars∗ bound as)
      t → t
    mapFreeVars∗ : ℕ → (Args Term → Args Term)
    mapFreeVars∗ b = λ where
      [] → []
      (arg i t ∷ ts) → arg i (mapFreeVars b t) ∷ mapFreeVars∗ b ts

    mapFreeVarsᵖ : ℕ → (Pattern → Pattern)
    mapFreeVarsᵖ b = λ where
      (con c ps) → con c (mapFreeVarsᵖ∗ b ps)
      (dot t)    → dot (mapFreeVars b t)
      (absurd x) → absurd (b ⁇ x)
      p → p
    mapFreeVarsᵖ∗ : ℕ → (Args Pattern → Args Pattern)
    mapFreeVarsᵖ∗ b = λ where
      [] → []
      (arg i p ∷ ps) → arg i (mapFreeVarsᵖ b p) ∷ mapFreeVarsᵖ∗ (suc b) ps

    mapFreeVarsᵗ : ℕ → (Telescope → Telescope)
    mapFreeVarsᵗ b = λ where
      [] → []
      ((s , arg i t) ∷ ts) → (s , arg i (mapFreeVars b t)) ∷ mapFreeVarsᵗ (suc b) ts

    mapFreeVarsᶜ : ℕ → (Clause → Clause)
    mapFreeVarsᶜ b = λ where
      (clause tel ps t) → clause (mapFreeVarsᵗ b tel) (mapFreeVarsᵖ∗ b ps)
                                 (mapFreeVars (length tel + b) t)
      (absurd-clause tel ps) → absurd-clause (mapFreeVarsᵗ b tel) (mapFreeVarsᵖ∗ b ps)
    mapFreeVarsᶜ∗ : ℕ → (List Clause → List Clause)
    mapFreeVarsᶜ∗ b = λ where
      [] → []
      (c ∷ cs) → mapFreeVarsᶜ b c ∷ mapFreeVarsᶜ∗ b cs

    mapFreeVarsˢ : ℕ → (Sort → Sort)
    mapFreeVarsˢ b = λ where
      (set t) → set (mapFreeVars b t)
      (prop t) → prop (mapFreeVars b t)
      s → s

  mapVars : Term → Term
  mapVars = mapFreeVars 0

varsToUnknown : Type → Type
varsToUnknown′ : Args Type → Args Type

varsToUnknown (var _ _)  = unknown
varsToUnknown (def c xs) = def c (varsToUnknown′ xs)
varsToUnknown (con c xs) = con c (varsToUnknown′ xs)
varsToUnknown ty         = ty

varsToUnknown′ []              = []
varsToUnknown′ (arg i ty ∷ xs) = arg i (varsToUnknown ty) ∷ varsToUnknown′ xs

parameters : Definition → ℕ
parameters (data-type pars _) = pars
parameters _                  = 0

vArgs : Args A → List A
vArgs [] = []
vArgs (vArg x ∷ xs) = x ∷ vArgs xs
vArgs (_      ∷ xs) = vArgs xs

argInfo : Arg A → ArgInfo
argInfo (arg i _) = i

isVisible? : (a : Arg A) → Dec (visibility (argInfo a) ≡ visible)
isVisible? a = visibility (argInfo a) Vis.≟ visible

isInstance? : (a : Arg A) → Dec (visibility (argInfo a) ≡ instance′)
isInstance? a = visibility (argInfo a) Vis.≟ instance′

isHidden? : (a : Arg A) → Dec (visibility (argInfo a) ≡ hidden)
isHidden? a = visibility (argInfo a) Vis.≟ hidden

remove-iArgs : Args A → Args A
remove-iArgs [] = []
remove-iArgs (iArg x ∷ xs) = remove-iArgs xs
remove-iArgs (x      ∷ xs) = x ∷ remove-iArgs xs

hide : Arg A → Arg A
hide (vArg x) = hArg x
hide (hArg x) = hArg x
hide (iArg x) = iArg x
hide a        = a

∀indices⋯ : Args Type → Type → Type
∀indices⋯ []       ty = ty
∀indices⋯ (i ∷ is) ty = Π[ "_" ∶ hide i ] (∀indices⋯ is ty)

apply⋯ : Args Type → Name → Type
apply⋯ is n = def n $ remove-iArgs $
  map (λ{ (n , arg i _) → arg i (♯ (length is ∸ suc (toℕ n)))}) (zip (allFin $ length is) is)

-- ** records

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

toTelescope : List (Abs (Arg Type)) → Telescope
toTelescope = map (λ where (abs n x) → (n , x))

fromTelescope : Telescope → List (Abs (Arg Type))
fromTelescope = map (λ where (n , x) → (abs n x))
