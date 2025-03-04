{-# OPTIONS --safe --without-K #-}
module Reflection.Utils.Substitute where

open import Meta.Prelude
open import Meta.Init

open import Data.Nat using (_≤ᵇ_)

-- ** substitution

-- ULF:
-- There aren't any nice substitution functions (that I can find) in the standard library
-- or stdlib-meta. This one is cheating and only works for closed terms at either never
-- gets applied, or where we can safely throw away the arguments (e.g. `unknown`).

Subst : Set → Set
Subst A = ℕ → Term → A → A

mutual
  substTerm : Subst Term
  substTerm x s = λ where
    (var y as) → case compare x y of λ where
      (less _ _)    → var (y ∸ 1) (substArgs x s as)
      (equal _)     → s  -- cheating and dropping the as!
      (greater _ _) → var y (substArgs x s as)
    (con c as)     → con c (substArgs x s as)
    (def f as)     → def f (substArgs x s as)
    (lam v t)      → lam v (substAbs x s t)
    (pat-lam _ _)  → unknown  -- ignoring for now
    (pi a b)       → pi (substArg x s a) (substAbs x s b)
    (agda-sort st) → agda-sort (substSort x s st)
    (lit l)        → lit l
    (meta m as)    → meta m (substArgs x s as)
    unknown        → unknown

  substArgs : Subst (Args Term)
  substArgs x s = λ where
    []       → []
    (a ∷ as) → substArg x s a ∷ substArgs x s as

  substArg  : Subst (Arg Term)
  substArg x s (arg i t) = arg i (substTerm x s t)

  substAbs  : Subst (Abs Term)
  substAbs x s (abs z t) = abs z (substTerm (ℕ.suc x) s t)

  substSort : Subst Sort
  substSort x s = λ where
    (set t)     → set (substTerm x s t)
    (lit n)     → lit n
    (prop t)    → prop (substTerm x s t)
    (propLit n) → propLit n
    (inf n)     → inf n
    unknown     → unknown

-- ** manipulating variables
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

mutual
  varsToUnknown : Type → Type
  varsToUnknown = λ where
    (var _ _)  → unknown
    (def c xs) → def c (varsToUnknown* xs)
    (con c xs) → con c (varsToUnknown* xs)
    ty         → ty

  varsToUnknown* : Args Type → Args Type
  varsToUnknown* = λ where
    []              → []
    (arg i ty ∷ xs) → arg i (varsToUnknown ty) ∷ varsToUnknown* xs

mapVariables : (ℕ → ℕ) → (Pattern → Pattern)
mapVariables f (Pattern.var n)      = Pattern.var (f n)
mapVariables f (Pattern.con c args) = Pattern.con c $ go args
  where
    go : List (Arg Pattern) → List (Arg Pattern)
    go [] = []
    go (arg i p ∷ l) = arg i (mapVariables f p) ∷ go l
mapVariables _ p                    = p
