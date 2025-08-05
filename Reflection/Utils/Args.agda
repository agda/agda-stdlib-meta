{-# OPTIONS --safe --without-K #-}
module Reflection.Utils.Args where

open import Meta.Prelude
open import Meta.Init

open import Data.List using (map; zip)
open import Data.Fin using (toℕ)
open import Relation.Nullary using (Dec)

open import Reflection.AST.Argument.Information
import Reflection.AST.Argument.Visibility as Vis

getVisibility : Arg A → Visibility
getVisibility (arg (arg-info v _) _) = v

unArgs : Args A → List A
unArgs = map unArg

args : Term → Args Term
args = λ where
  (var _ xs)  → xs
  (def _ xs)  → xs
  (con _ xs)  → xs
  _           → []

args′ : Term → List Term
args′ = unArgs ∘ args

vArgs : Args A → List A
vArgs = λ where
  []            → []
  (vArg x ∷ xs) → x ∷ vArgs xs
  (_      ∷ xs) → vArgs xs

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
hide = λ where
  (vArg x) → hArg x
  (hArg x) → hArg x
  (iArg x) → iArg x
  a        → a

∀indices⋯ : Args Type → Type → Type
∀indices⋯ []       ty = ty
∀indices⋯ (i ∷ is) ty = Π[ "_" ∶ hide i ] (∀indices⋯ is ty)

apply⋯ : Args Type → Name → Type
apply⋯ is n = def n $ remove-iArgs $
  map (λ{ (n , arg i _) → arg i (♯ (length is ∸ suc (toℕ n)))}) (zip (allFin $ length is) is)

-- Applying a list of arguments to a term of any shape.
apply∗ : Term → Args Term → Term
apply∗ f xs = case f of λ where
  (def n as)      → def n (as ++ xs)
  (con c as)      → con c (as ++ xs)
  (var x as)      → var x (as ++ xs)
  (pat-lam cs as) → pat-lam cs (as ++ xs)
  (meta x as)     → meta x (as ++ xs)
  f               → f
