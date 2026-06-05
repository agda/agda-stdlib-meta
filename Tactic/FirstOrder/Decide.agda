{-# OPTIONS --safe --without-K #-}
--------------------------------------------------------------------------------
-- A fuel-free, provably-terminating G4ip proof search.
--
-- The fuel-bounded `Tactic.FirstOrder.Search.search` is complete only when the
-- fuel exceeds the proof-search depth. Here we remove the fuel by recursing on
-- a well-founded measure: Dyckhoff's termination argument, encoded as a single
-- natural number.
--
-- The trick: weight formulas with `w (A ⇒ B) = w A + w B` (no `+1`), and take
--   μ (Γ ⊢ G)  =  Σ_{A ∈ Γ} 3 ^ (w A)  +  3 ^ (w G).
-- Every G4ip rule replaces its principal formula (weight k) by at most two
-- formulas of weight < k, and `2 · 3^(k-1) < 3^k`, so μ strictly decreases on
-- every premise. Ordinary `<`-well-foundedness then justifies the recursion.
--
-- This module proves only termination; what it returns is still a `Γ ⊢ φ`
-- certificate (sound via `Core.soundness`). PART 1 below builds the measure and
-- the arithmetic; PART 2 (the search) consumes it.
--------------------------------------------------------------------------------

module Tactic.FirstOrder.Decide where

open import Data.List using (List; []; _∷_; foldr)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; just; nothing; map; _<∣>_)
open import Data.Nat
open import Data.Nat.Induction using (<-wellFounded)
open import Data.Nat.Properties
open import Data.Nat.Solver using (module +-*-Solver)
open import Function using (case_of_)
open import Induction.WellFounded using (Acc; acc)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; sym; trans; subst; subst₂)

open +-*-Solver

open import Tactic.FirstOrder.Core   hiding (solve)
open import Tactic.FirstOrder.Search using (find; search)

private
  variable
    n : ℕ

--------------------------------------------------------------------------------
-- PART 1 — the measure
--------------------------------------------------------------------------------

-- Dyckhoff weight: note the absent `+1` on implication.
w : Formula n → ℕ
w (atom _) = 1
w ⊤′       = 1
w ⊥′       = 1
w (A ∧′ B) = w A + w B + 1
w (A ∨′ B) = w A + w B + 1
w (A ⇒′ B) = w A + w B

f : Formula n → ℕ
f A = 3 ^ w A

Σf : List (Formula n) → ℕ
Σf Γ = foldr (λ A → f A +_) 0 Γ

μ : List (Formula n) → Formula n → ℕ
μ Γ G = Σf Γ + f G

--------------------------------------------------------------------------------
-- Deleting a hypothesis removes its weight from the sum.
--------------------------------------------------------------------------------

Σf-∖ : ∀ {X : Formula n} {Γ} (i : X ∈ Γ) → Σf Γ ≡ f X + Σf (Γ ∖ i)
Σf-∖ (here refl) = refl
Σf-∖ {X = X} (there {x = y} {xs = Γ} i) =
  trans (cong (f y +_) (Σf-∖ i))
  (trans (sym (+-assoc (f y) (f X) (Σf (Γ ∖ i))))
  (trans (cong (_+ Σf (Γ ∖ i)) (+-comm (f y) (f X)))
         (+-assoc (f X) (f y) (Σf (Γ ∖ i)))))

--------------------------------------------------------------------------------
-- Two arithmetic facts everything reduces to.
--------------------------------------------------------------------------------

1<3 : 1 < 3
1<3 = s≤s (s≤s z≤n)

-- strict monotonicity of 3 ^_
one< : ∀ {a b} → a < b → 3 ^ a < 3 ^ b
one< = ^-monoʳ-< 3 1<3

-- if both exponents are below c, the sum of the powers is below 3 ^ c
two< : ∀ {a b c} → a < c → b < c → 3 ^ a + 3 ^ b < 3 ^ c
two< {a} {b} {suc c} (s≤s a≤c) (s≤s b≤c) =
  ≤-<-trans
    (+-mono-≤ (^-monoʳ-≤ 3 a≤c) (^-monoʳ-≤ 3 b≤c))     -- 3^a + 3^b ≤ 3^c + 3^c
    (subst (3 ^ c + 3 ^ c <_) (eq c)                    -- 3^c + 3^c < 3 ^ suc c
           (m<m+n (3 ^ c + 3 ^ c) (m^n>0 3 c)))
  where
  -- (3^c + 3^c) + 3^c ≡ 3 * 3^c = 3 ^ suc c
  eq : ∀ c → 3 ^ c + 3 ^ c + 3 ^ c ≡ 3 ^ suc c
  eq c = trans (+-assoc (3 ^ c) (3 ^ c) (3 ^ c))
               (cong (3 ^ c +_) (cong (3 ^ c +_) (sym (+-identityʳ (3 ^ c)))))

--------------------------------------------------------------------------------
-- PART 2 — every G4ip rule strictly decreases μ
--------------------------------------------------------------------------------

private
  f>0 : ∀ (A : Formula n) → 0 < f A
  f>0 A = m^n>0 3 (w A)

  w>0 : ∀ (A : Formula n) → 0 < w A
  w>0 (atom _) = s≤s z≤n
  w>0 ⊤′       = s≤s z≤n
  w>0 ⊥′       = s≤s z≤n
  w>0 (A ∧′ B) = subst (0 <_) (+-comm 1 (w A + w B)) (s≤s z≤n)
  w>0 (A ∨′ B) = subst (0 <_) (+-comm 1 (w A + w B)) (s≤s z≤n)
  w>0 (A ⇒′ B) = <-≤-trans (w>0 A) (m≤m+n (w A) (w B))

  lt1 : ∀ a b → a < a + b + 1
  lt1 a b = ≤-<-trans (m≤m+n a b) (m<m+n (a + b) (s≤s z≤n))

  lt2 : ∀ a b → b < a + b + 1
  lt2 a b = ≤-<-trans (≤-trans (m≤m+n b a) (≤-reflexive (+-comm b a)))
                      (m<m+n (a + b) (s≤s z≤n))

  -- commutative-monoid rearrangements (discharged by the +-solver)
  eqR : ∀ a s b → (a + s) + b ≡ s + (a + b)
  eqR = solve 3 (λ a s b → (a :+ s) :+ b := s :+ (a :+ b)) refl

  eqShift : ∀ s x y → s + (x + y) ≡ (x + s) + y
  eqShift = solve 3 (λ s x y → s :+ (x :+ y) := (x :+ s) :+ y) refl

  eq∧⇒ : ∀ a b c → 1 + (a + (b + c)) ≡ (a + b + 1) + c
  eq∧⇒ = solve 3 (λ a b c → con 1 :+ (a :+ (b :+ c)) := (a :+ b :+ con 1) :+ c) refl

  ------------------------------------------------------------------------------
  -- generic glue
  ------------------------------------------------------------------------------

  decG : ∀ {Γ : List (Formula n)} {G G′} → f G′ < f G → μ Γ G′ < μ Γ G
  decG {Γ = Γ} lt = +-monoʳ-< (Σf Γ) lt

  decL0 : ∀ {Γ G} {X : Formula n} (i : X ∈ Γ) → μ (Γ ∖ i) G < μ Γ G
  decL0 {Γ = Γ} {G} {X} i =
    subst (λ z → μ (Γ ∖ i) G < z + f G) (sym (Σf-∖ i))
          (+-monoˡ-< (f G) (m<n+m (Σf (Γ ∖ i)) (f>0 X)))

  decL1 : ∀ {Γ G} {X Y : Formula n} (i : X ∈ Γ) → f Y < f X
        → μ (Y ∷ (Γ ∖ i)) G < μ Γ G
  decL1 {Γ = Γ} {G} {X} {Y} i core =
    subst (λ z → μ (Y ∷ (Γ ∖ i)) G < z + f G) (sym (Σf-∖ i))
          (+-monoˡ-< (f G) (+-monoˡ-< (Σf (Γ ∖ i)) core))

  decL2 : ∀ {Γ G} {X Y Z : Formula n} (i : X ∈ Γ) → f Y + f Z < f X
        → μ (Y ∷ Z ∷ (Γ ∖ i)) G < μ Γ G
  decL2 {Γ = Γ} {G} {X} {Y} {Z} i core =
    subst (λ z → μ (Y ∷ Z ∷ (Γ ∖ i)) G < z + f G) (sym (Σf-∖ i))
          (+-monoˡ-< (f G)
            (subst (_< f X + Σf (Γ ∖ i)) (+-assoc (f Y) (f Z) (Σf (Γ ∖ i)))
                   (+-monoˡ-< (Σf (Γ ∖ i)) core)))

  ------------------------------------------------------------------------------
  -- the per-rule decreases
  ------------------------------------------------------------------------------

  dec∨R₁ : ∀ {Γ : List (Formula n)} {A B} → μ Γ A < μ Γ (A ∨′ B)
  dec∨R₁ {Γ = Γ} {A} {B} = decG {Γ = Γ} {G = A ∨′ B} {G′ = A} (one< (lt1 (w A) (w B)))
  dec∨R₂ : ∀ {Γ : List (Formula n)} {A B} → μ Γ B < μ Γ (A ∨′ B)
  dec∨R₂ {Γ = Γ} {A} {B} = decG {Γ = Γ} {G = A ∨′ B} {G′ = B} (one< (lt2 (w A) (w B)))
  dec∧R₁ : ∀ {Γ : List (Formula n)} {A B} → μ Γ A < μ Γ (A ∧′ B)
  dec∧R₁ {Γ = Γ} {A} {B} = decG {Γ = Γ} {G = A ∧′ B} {G′ = A} (one< (lt1 (w A) (w B)))
  dec∧R₂ : ∀ {Γ : List (Formula n)} {A B} → μ Γ B < μ Γ (A ∧′ B)
  dec∧R₂ {Γ = Γ} {A} {B} = decG {Γ = Γ} {G = A ∧′ B} {G′ = B} (one< (lt2 (w A) (w B)))

  dec⊃R : ∀ {Γ : List (Formula n)} {A B} → μ (A ∷ Γ) B < μ Γ (A ⇒′ B)
  dec⊃R {Γ = Γ} {A} {B} =
    subst (_< μ Γ (A ⇒′ B)) (sym (eqR (f A) (Σf Γ) (f B)))
          (+-monoʳ-< (Σf Γ) (two< (m<m+n (w A) (w>0 B)) (m<n+m (w B) (w>0 A))))

  dec∧L : ∀ {Γ} (G : Formula n) {A B} (i : A ∧′ B ∈ Γ) → μ (A ∷ B ∷ (Γ ∖ i)) G < μ Γ G
  dec∧L G {A} {B} i = decL2 {G = G} {Y = A} {Z = B} i (two< (lt1 (w A) (w B)) (lt2 (w A) (w B)))

  dec∨L₁ : ∀ {Γ} (G : Formula n) {A B} (i : A ∨′ B ∈ Γ) → μ (A ∷ (Γ ∖ i)) G < μ Γ G
  dec∨L₁ G {A} {B} i = decL1 {G = G} {Y = A} i (one< (lt1 (w A) (w B)))
  dec∨L₂ : ∀ {Γ} (G : Formula n) {A B} (i : A ∨′ B ∈ Γ) → μ (B ∷ (Γ ∖ i)) G < μ Γ G
  dec∨L₂ G {A} {B} i = decL1 {G = G} {Y = B} i (one< (lt2 (w A) (w B)))

  dec⊃L⊤ : ∀ {Γ} (G : Formula n) {B} (i : ⊤′ ⇒′ B ∈ Γ) → μ (B ∷ (Γ ∖ i)) G < μ Γ G
  dec⊃L⊤ G {B} i = decL1 {G = G} {Y = B} i (one< (m<n+m (w B) {n = 1} (s≤s z≤n)))

  dec⊃Lat : ∀ {Γ} (G : Formula n) {k B} (i : atom k ⇒′ B ∈ Γ) → μ (B ∷ (Γ ∖ i)) G < μ Γ G
  dec⊃Lat G {B = B} i = decL1 {G = G} {Y = B} i (one< (m<n+m (w B) {n = 1} (s≤s z≤n)))

  dec⊃L⊥ : ∀ {Γ} (G : Formula n) {B} (i : ⊥′ ⇒′ B ∈ Γ) → μ (Γ ∖ i) G < μ Γ G
  dec⊃L⊥ G i = decL0 {G = G} i

  dec⊃L∧ : ∀ {Γ} (G : Formula n) {C D B} (i : (C ∧′ D) ⇒′ B ∈ Γ)
         → μ ((C ⇒′ (D ⇒′ B)) ∷ (Γ ∖ i)) G < μ Γ G
  dec⊃L∧ G {C} {D} {B} i = decL1 {G = G} {Y = C ⇒′ (D ⇒′ B)} i (one< (≤-reflexive (eq∧⇒ (w C) (w D) (w B))))

  dec⊃L∨ : ∀ {Γ} (G : Formula n) {C D B} (i : (C ∨′ D) ⇒′ B ∈ Γ)
         → μ ((C ⇒′ B) ∷ (D ⇒′ B) ∷ (Γ ∖ i)) G < μ Γ G
  dec⊃L∨ G {C} {D} {B} i =
    decL2 {G = G} {Y = C ⇒′ B} {Z = D ⇒′ B} i
          (two< (+-monoˡ-< (w B) (lt1 (w C) (w D)))
                (+-monoˡ-< (w B) (lt2 (w C) (w D))))

  dec⊃L⊃₂ : ∀ {Γ} (G : Formula n) {C D B} (i : (C ⇒′ D) ⇒′ B ∈ Γ) → μ (B ∷ (Γ ∖ i)) G < μ Γ G
  dec⊃L⊃₂ G {C} {D} {B} i =
    decL1 {G = G} {Y = B} i (one< (m<n+m (w B) (<-≤-trans (w>0 C) (m≤m+n (w C) (w D)))))

  dec⊃L⊃₁ : ∀ {Γ} (G : Formula n) {C D B} (i : (C ⇒′ D) ⇒′ B ∈ Γ)
          → μ ((D ⇒′ B) ∷ (Γ ∖ i)) (C ⇒′ D) < μ Γ G
  dec⊃L⊃₁ {Γ = Γ} G {C} {D} {B} i =
    subst (λ z → μ ((D ⇒′ B) ∷ (Γ ∖ i)) (C ⇒′ D) < z + f G) (sym (Σf-∖ i))
          (subst₂ _<_ (eqShift S (f (D ⇒′ B)) (f (C ⇒′ D)))
                      (eqShift S (f X) (f G))
                      (+-monoʳ-< S coreXG))
    where
    S = Σf (Γ ∖ i)
    X = (C ⇒′ D) ⇒′ B
    coreXG : f (D ⇒′ B) + f (C ⇒′ D) < f X + f G
    coreXG = <-≤-trans
      (two< (+-monoˡ-< (w B) (m<n+m (w D) (w>0 C)))
            (m<m+n (w C + w D) (w>0 B)))
      (m≤m+n (f X) (f G))

--------------------------------------------------------------------------------
-- PART 3 — the fuel-free search, by well-founded recursion on μ
--------------------------------------------------------------------------------

private
  Rec : ∀ {n} → List (Formula n) → Formula n → Set
  Rec Γ G = ∀ {y} → y < μ Γ G → Acc _<_ y

mutual
  searchA : ∀ {n} (Γ : List (Formula n)) (G : Formula n) → Acc _<_ (μ Γ G) → Maybe (Γ ⊢ G)
  searchA Γ G (acc rs) =
        rightA Γ G rs
    <∣> map ⊥L (find ⊥′ Γ)
    <∣> fromHypsA Γ G rs

  rightA : ∀ {n} (Γ : List (Formula n)) (G : Formula n) → Rec Γ G → Maybe (Γ ⊢ G)
  rightA Γ ⊤′       rs = just ⊤R
  rightA Γ (atom k) rs = map init (find (atom k) Γ)
  rightA Γ ⊥′       rs = nothing
  rightA Γ (A ⇒′ B) rs = map ⊃R (searchA (A ∷ Γ) B (rs (dec⊃R {Γ = Γ} {A} {B})))
  rightA Γ (A ∨′ B) rs =
        map ∨R₁ (searchA Γ A (rs (dec∨R₁ {Γ = Γ} {A} {B})))
    <∣> map ∨R₂ (searchA Γ B (rs (dec∨R₂ {Γ = Γ} {A} {B})))
  rightA Γ (A ∧′ B) rs = case searchA Γ A (rs (dec∧R₁ {Γ = Γ} {A} {B})) of λ where
    (just d) → map (∧R d) (searchA Γ B (rs (dec∧R₂ {Γ = Γ} {A} {B})))
    nothing  → nothing

  fromHypsA : ∀ {n} (Γ : List (Formula n)) (G : Formula n) → Rec Γ G → Maybe (Γ ⊢ G)
  fromHypsA {n} Γ G rs = go Γ (λ z → z)
    where
    go : (Δ : List (Formula n)) → (∀ {x} → x ∈ Δ → x ∈ Γ) → Maybe (Γ ⊢ G)
    go []      f = nothing
    go (χ ∷ Δ) f = tryHypA Γ G χ rs (f (here refl)) <∣> go Δ (λ z → f (there z))

  -- χ before rs/i so the shape match drives dispatch
  tryHypA : ∀ {n} (Γ : List (Formula n)) (G χ : Formula n) → Rec Γ G → χ ∈ Γ → Maybe (Γ ⊢ G)
  tryHypA Γ G (A ∧′ B) rs i = map (∧L i) (searchA (A ∷ B ∷ (Γ ∖ i)) G (rs (dec∧L G i)))
  tryHypA Γ G (A ∨′ B) rs i = case searchA (A ∷ (Γ ∖ i)) G (rs (dec∨L₁ G i)) of λ where
    (just d) → map (∨L i d) (searchA (B ∷ (Γ ∖ i)) G (rs (dec∨L₂ G i)))
    nothing  → nothing
  tryHypA Γ G (⊤′      ⇒′ B) rs i = map (⊃L⊤ i) (searchA (B ∷ (Γ ∖ i)) G (rs (dec⊃L⊤ G i)))
  tryHypA Γ G (⊥′      ⇒′ B) rs i = map (⊃L⊥ i) (searchA (Γ ∖ i) G (rs (dec⊃L⊥ G i)))
  tryHypA Γ G (atom k  ⇒′ B) rs i = case find (atom k) (Γ ∖ i) of λ where
    (just j) → map (⊃Lat i j) (searchA (B ∷ (Γ ∖ i)) G (rs (dec⊃Lat G i)))
    nothing  → nothing
  tryHypA Γ G ((C ∧′ D) ⇒′ B) rs i =
    map (⊃L∧ i) (searchA ((C ⇒′ (D ⇒′ B)) ∷ (Γ ∖ i)) G (rs (dec⊃L∧ G i)))
  tryHypA Γ G ((C ∨′ D) ⇒′ B) rs i =
    map (⊃L∨ i) (searchA ((C ⇒′ B) ∷ (D ⇒′ B) ∷ (Γ ∖ i)) G (rs (dec⊃L∨ G i)))
  tryHypA Γ G ((C ⇒′ D) ⇒′ B) rs i = case searchA ((D ⇒′ B) ∷ (Γ ∖ i)) (C ⇒′ D) (rs (dec⊃L⊃₁ G i)) of λ where
    (just d) → map (⊃L⊃ i d) (searchA (B ∷ (Γ ∖ i)) G (rs (dec⊃L⊃₂ G i)))
    nothing  → nothing
  tryHypA Γ G χ rs i = nothing

-- A total, fuel-free decision search for G4ip: terminates by well-founded
-- recursion on μ, and returns a checkable derivation when it succeeds.
decide : ∀ {n} (Γ : List (Formula n)) (G : Formula n) → Maybe (Γ ⊢ G)
decide Γ G = searchA Γ G (<-wellFounded (μ Γ G))

--------------------------------------------------------------------------------
-- Fuel-free *and* fast.
--
-- `decide` is fuel-free but pays at reduction time: recursing on
-- `Acc _<_ (μ Γ G)` forces Agda to reduce the accessibility proof, which costs
-- O(μ Γ G) — and μ is exponential. The fix is to feed the *same* measure to the
-- fast structural `search` as a fuel ceiling: a `ℕ` ceiling is O(1) per step and
-- the recursion only reaches the real (small) proof depth, never the ceiling.
-- The well-founded development above is what licenses this — it shows every rule
-- strictly decreases μ, so μ is always enough fuel.
--------------------------------------------------------------------------------

decideFast : ∀ {n} (Γ : List (Formula n)) (G : Formula n) → Maybe (Γ ⊢ G)
decideFast Γ G = search (μ Γ G) Γ G
