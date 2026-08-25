{-# OPTIONS --safe --without-K #-}
module Reflection.Utils.Args where

open import Meta.Prelude
open import Meta.Init

open import Data.List using (map; zip; reverse; length)
open import Data.Fin using (toℕ)
open import Data.Vec.Base using (Vec; []; _∷_)
import Data.Vec.Base as Vec
import Data.Maybe as Maybe
open import Relation.Nullary using (Dec)

open import Reflection.AST.Argument.Information
import Reflection.AST.Argument.Visibility as Vis

takeFirst : ∀ {ℓ} {A : Set ℓ} (n : ℕ) → List A → Maybe (Vec A n)
takeFirst zero    _        = just []
takeFirst (suc _) []       = nothing
takeFirst (suc n) (x ∷ xs) = Maybe.map (x ∷_) (takeFirst n xs)

takeLast : ∀ {ℓ} {A : Set ℓ} (n : ℕ) → List A → Maybe (Vec A n)
takeLast n = Maybe.map Vec.reverse ∘ takeFirst n ∘ reverse

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

hArgs : Args A → List A
hArgs = λ where
  []            → []
  (hArg x ∷ xs) → x ∷ hArgs xs
  (_      ∷ xs) → hArgs xs

visibleCount : Args A → ℕ
visibleCount = length ∘ vArgs

-- Take the last `n` visible arguments of a `def`. Returns `nothing`
-- if the term isn't a `def` or has fewer than `n` visible
-- arguments. Hidden arguments and any leading visible arguments
-- beyond the last `n` are skipped.
getVisibleArgs : ∀ n → Term → Maybe (Vec Term n)
getVisibleArgs n (def _ xs) = Maybe.map Vec.reverse (takeFirst n (reverse (vArgs xs)))
getVisibleArgs _ _ = nothing

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
