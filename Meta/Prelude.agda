{-# OPTIONS --safe --without-K #-}

module Meta.Prelude where

-- ** stdlib re-exports
open import Level public
  renaming (_⊔_ to _⊔ˡ_; suc to sucˡ; zero to zeroˡ)
variable
  ℓ ℓ′ ℓ″ : Level
  A B C D : Set ℓ

open import Data.Bool public
  hiding (_≟_; _≤_; _≤?_; _<_; _<?_)
open import Data.Empty public
open import Data.List public
  hiding (align; alignWith; fromMaybe; map; zip; zipWith)
open import Data.Maybe public
  hiding (_>>=_; ap; align; alignWith; fromMaybe; map; zip; zipWith)
open import Data.Unit public
  hiding (_≟_)
open import Data.Sum public
  hiding (assocʳ; assocˡ; map; map₁; map₂; reduce; swap)
open import Data.Product public
  hiding (assocʳ; assocˡ; map; map₁; map₂; swap; zip; zipWith; _<*>_)
open import Data.Nat public
  hiding (_≟_; _≤_; _≤?_; _<_; _<?_; _≤ᵇ_; _≡ᵇ_)
open import Data.String public
  using (String; _<+>_)

open import Function public
open import Relation.Nullary public
  using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality public
  hiding (preorder; setoid; [_]; module ≡-Reasoning; decSetoid)

-- ** helper funs
lookupᵇ : (A → A → Bool) → List (A × B) → A → Maybe B
lookupᵇ f [] n = nothing
lookupᵇ f ((k , v) ∷ l) n = if f k n then just v else lookupᵇ f l n

zipWithIndex : (ℕ → A → B) → List A → List B
zipWithIndex f l = zipWith f (upTo $ length l) l
  where open import Data.Fin; open import Data.List

enumerate : List A → List (ℕ × A)
enumerate = zipWithIndex _,_

_⁉_ : List A → ℕ → Maybe A
_⁉_ = λ where
  []       _       → nothing
  (x ∷ _)  zero    → just x
  (_ ∷ xs) (suc n) → xs ⁉ n
