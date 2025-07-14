{-# OPTIONS --safe --without-K #-}
{-# OPTIONS -v allTactics:100 #-}
module Tactic.Derive.TestTypes where

open import Data.Fin

open import Meta.Prelude
open import Meta.Init

data E0 : Set where

data E1 : Set where
  c1E1 : E1
  c2E1 : E1
  c3E1 : E1
  c4E1 : E1
  c5E1 : E1
  c6E1 : E1
  c7E1 : E1

data E2 {a} (A : Set a) : Set a where
  c1E2 : A → E2 A
  c2E2 : E2 A → E2 A

data E3 {a} (A : Set a) : Set a where
  c1E3 : List (E3 A) → Maybe (E3 A) → E3 A
  c2E3 : E3 A

data E4 : {n : ℕ} → Fin n → Set where
  c1E4 : ∀ {k} → E4 {suc k} zero
  c2E4 : ∀ {k} {l} → E4 {suc k} (suc l)

record R1 : Set where
  field f1R1 : E1
        f2R1 : E2 ℕ

record R2 {a} (A : Set a) : Set a where
  field f1R2 : E1
        f2R2 : E2 ℕ
        f3R2 : R1
        f4R2 : R1
        f5R2 : A
        f6R2 : A

record R20 : Set where
  field r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 : Bool

data M₁ : Set
data M₂ : Set
data M₁ where
  m₁ : M₁
  m₂→₁ : M₂ → M₁
data M₂ where
  m₂ : M₂
  m₁→₂ : M₁ → M₂

AllTestTypes : List Name
AllTestTypes = quote E0 ∷ quote E1 ∷ quote E2 ∷ quote E3 ∷ quote R1 ∷ quote R2 ∷ quote M₁ ∷ quote M₂ ∷ []

open import Data.Bool using (Bool) public
open import Data.Char using (Char) public
open import Data.Container using (Container) public
open import Data.Container using (Container) public
open import Data.Digit using (Digit) public
open import Data.Empty using (⊥) public
open import Data.Fin using (Fin) public
open import Data.Float using (Float) public
open import Data.Integer using (ℤ) public
open import Data.List using (List) public
open import Data.Maybe using (Maybe) public
open import Data.Nat using (ℕ) public
open import Data.Product using (Σ) public
open import Data.Rational using (ℚ) public
open import Data.Record using (Record) public
open import Data.Refinement using (Refinement) public
open import Data.Sign using (Sign) public
open import Data.String using (String) public
open import Data.Sum using (_⊎_) public
open import Data.These using (These) public
open import Data.Unit using (⊤) public
open import Data.Universe using (Universe) public
open import Data.Vec using (Vec) public
open import Data.W using (W) public
open import Data.Word64 using (Word64) public

stdlibTypes : List Name
stdlibTypes = quote Bool ∷ quote Container ∷ quote Fin ∷ quote ℤ ∷ quote List ∷ quote Maybe ∷ quote ℕ ∷ quote Σ ∷ quote ℚ ∷ quote Record ∷ quote Refinement ∷ quote Sign ∷ quote _⊎_ ∷ quote These ∷ quote ⊤ ∷ quote Universe ∷ quote Vec ∷ quote W ∷ []
