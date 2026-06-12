-- Standalone performance benchmark for the reflective simplifier
-- (`Tactic.Simp.Reflective`).  NOT imported by anything else.
--
-- Rule sets of three sizes and a fixed set of 5 goals of realistic
-- size; each goal is proved once per rule-set size, so per-call scaling
-- is measurable from `agda --profile=internal` (the `Typing.Reflection`
-- bucket is macro execution incl. the final unify).  A 6th goal `gAC`
-- exercises the permutative (ordered-rewriting) path at small scale.
--
-- Compile with a raised GHC heap cap, e.g.
--   agda +RTS -M11g -RTS Tactic/Simp/Reflective/Bench.agda
-- The 16 heavy `simp!` calls each retain a large generated proof term, so
-- the default heap is exhausted; ordinary single-call use does NOT need this.
-- Cold-cache wall time on the reference machine: ~168 s.
--
-- SIZING NOTE.  The original target sizes were ~5/~20/~50.  Measurement
-- (see reflective-simp-plan.md § Performance) showed the per-call cost
-- is dominated by *meta-level rule reprocessing* and grows steeply
-- super-linearly with the number of DISTINCT operators across the rule
-- set, because the shared sort/op tables are deduplicated by O(table)
-- α-equality scans.  In isolation a single 19-rule call already costs
-- ~21–28 s of macro time, and a single 50-rule call OOMs the
-- type-checker; a module containing many such calls cannot compile.
-- This module therefore uses sizes ~5 / ~8 / ~12, which compile and
-- still span the realistic rule mix (identities, zeroes, assoc,
-- distributivity, list map/length lemmas).  The full scaling curve up
-- to the 50-rule OOM cliff is recorded in reflective-simp-plan.md,
-- measured per-call in isolated modules.
--
-- DESIGN NOTE — no commutativity in the scaling sets.  `+-comm`/`*-comm`
-- are permutative (item 9) and, mixed with distributivity in a large
-- set, drive the object-level greedy search into a state explosion
-- (measured: a 17-rule arithmetic set with both comm rules OOMs while
-- the same set without comm completes).  Commutativity is exercised
-- separately at small scale in `gAC`.

{-# OPTIONS --safe #-}

module Tactic.Simp.Reflective.Bench where

open import Data.Nat
open import Data.Nat.Properties
open import Data.List using (List; []; _∷_; _++_; map; length)
open import Data.List.Properties using (++-identityʳ; length-map)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

open import Tactic.Defaults
open import Tactic.Simp.Reflective using (simp!)

----------------------------------------------------------------
-- Monomorphic wrappers: direct `≡`-bodied rules at concrete sorts.
----------------------------------------------------------------

private

  catIdʳ : (xs : List ℕ) → xs ++ [] ≡ xs
  catIdʳ = ++-identityʳ

  lenMapSuc : (l : List ℕ) → length (map suc l) ≡ length l
  lenMapSuc = length-map suc

----------------------------------------------------------------
-- Rule sets.  R5 ⊆ R8 ⊆ R12 so the same goals are provable against all
-- three.  Larger sets add non-matching noise (lemmas at other
-- operators) that the meta-level rule processing must still chew
-- through per call.
----------------------------------------------------------------

  R5 : List _
  R5 = quote +-identityʳ
     ∷ quote +-identityˡ
     ∷ quote *-identityʳ
     ∷ quote *-zeroʳ
     ∷ quote +-assoc
     ∷ []

  R8 : List _
  R8 = R5 ++
       ( quote *-identityˡ
       ∷ quote *-zeroˡ
       ∷ quote *-assoc
       ∷ [] )

  R12 : List _
  R12 = R8 ++
        ( quote *-distribʳ-+
        ∷ quote *-distribˡ-+
        ∷ quote catIdʳ
        ∷ quote lenMapSuc
        ∷ [] )

----------------------------------------------------------------
-- Goal 1: nested arithmetic, several rewrites.
----------------------------------------------------------------

  g1-R5  : ∀ {x y : ℕ} → (x + 0) + ((y * 1) + 0) ≡ x + y
  g1-R5  = simp! R5
  g1-R8  : ∀ {x y : ℕ} → (x + 0) + ((y * 1) + 0) ≡ x + y
  g1-R8  = simp! R8
  g1-R12 : ∀ {x y : ℕ} → (x + 0) + ((y * 1) + 0) ≡ x + y
  g1-R12 = simp! R12

----------------------------------------------------------------
-- Goal 2: list goal needing length/map (multi-step).
----------------------------------------------------------------

  g2-R5  : ∀ (l : List ℕ) → length (map suc l) + 0 ≡ length l
  g2-R5  = simp! (quote lenMapSuc ∷ quote +-identityʳ ∷ [])  -- R5/R8 lack list lemma
  g2-R8  : ∀ (l : List ℕ) → length (map suc l) + 0 ≡ length l
  g2-R8  = simp! (R8 ++ (quote lenMapSuc ∷ []))
  g2-R12 : ∀ (l : List ℕ) → length (map suc l) + 0 ≡ length l
  g2-R12 = simp! R12

----------------------------------------------------------------
-- Goal 3: multi-sorted (List ℕ and ℕ).
----------------------------------------------------------------

  g3-R5  : ∀ (l : List ℕ) → length (map suc (l ++ [])) ≡ length l
  g3-R5  = simp! (quote lenMapSuc ∷ quote catIdʳ ∷ [])
  g3-R8  : ∀ (l : List ℕ) → length (map suc (l ++ [])) ≡ length l
  g3-R8  = simp! (R8 ++ (quote lenMapSuc ∷ quote catIdʳ ∷ []))
  g3-R12 : ∀ (l : List ℕ) → length (map suc (l ++ [])) ≡ length l
  g3-R12 = simp! R12

----------------------------------------------------------------
-- Goal 4: polymorphic instantiation (raw ++-identityʳ on List ℕ).
----------------------------------------------------------------

  g4-R5  : ∀ (xs ys : List ℕ) → (xs ++ []) ++ ys ≡ xs ++ ys
  g4-R5  = simp! (quote ++-identityʳ ∷ [])
  g4-R8  : ∀ (xs ys : List ℕ) → (xs ++ []) ++ ys ≡ xs ++ ys
  g4-R8  = simp! (R8 ++ (quote ++-identityʳ ∷ []))
  g4-R12 : ∀ (xs ys : List ℕ) → (xs ++ []) ++ ys ≡ xs ++ ys
  g4-R12 = simp! (R12 ++ (quote ++-identityʳ ∷ []))

----------------------------------------------------------------
-- Goal 5: deeper arithmetic chain (assoc + identities, 5–6 steps).
----------------------------------------------------------------

  g5-R5  : ∀ {a b c d : ℕ} → (((a + 0) + b) + (c * 1)) + (d + 0) ≡ a + (b + (c + d))
  g5-R5  = simp! R5
  g5-R8  : ∀ {a b c d : ℕ} → (((a + 0) + b) + (c * 1)) + (d + 0) ≡ a + (b + (c + d))
  g5-R8  = simp! R8
  g5-R12 : ∀ {a b c d : ℕ} → (((a + 0) + b) + (c * 1)) + (d + 0) ≡ a + (b + (c + d))
  g5-R12 = simp! R12

----------------------------------------------------------------
-- AC stress (small scale): commutativity via the permutative gate.
----------------------------------------------------------------

  -- The AC trio (assoc + comm + left-comm) canonicalises both sides;
  -- comm alone cannot (cf. `torder₂` in the main test file).
  +-lcomm : ∀ x y z → x + (y + z) ≡ y + (x + z)
  +-lcomm x y z =
    trans (sym (+-assoc x y z)) (trans (cong (_+ z) (+-comm x y)) (+-assoc y x z))

  gAC : ∀ {a b c : ℕ} → (c + b) + a ≡ a + (b + c)
  gAC = simp! (quote +-assoc ∷ quote +-comm ∷ quote +-lcomm ∷ [])
