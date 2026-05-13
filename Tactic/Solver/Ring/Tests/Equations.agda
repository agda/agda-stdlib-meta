{-# OPTIONS --safe --without-K #-}

module Tactic.Solver.Ring.Tests.Equations where

open import Algebra using (CommutativeSemiring)
open import Relation.Binary using (Setoid)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Tactic.Solver.Ring using (solve-≈ ; module Solver)

------------------------------------------------------------------------
-- Limitations
--
-- 1. `solve-≈` currently only speaks the language of semirings, so
-- there's no negation.
--
-- 2. `solve-≈` is not going to help solving any metavariables. When
-- it is applied in any context where at least one side of the goal
-- contains an unresolved metavariable that only this solve call can
-- determine, the macro emits a friendly type error. Note: this might
-- be fixable, by making the solver aware of metas & letting it solve
-- them. This seems very tricky and not worth it - just add a type
-- annotation.
------------------------------------------------------------------------

module ReadableErrorMessages {c ℓ} (R : CommutativeSemiring c ℓ) where
  open CommutativeSemiring R

  -- meta-left : ∀ {a} → (∀ {c} → a ≈ c * a → a ≈ 0#) → a ≈ 0#
  -- meta-left f = f (solve-≈ R)

  -- meta-right : ∀ {a} → (∀ {c} → c * a ≈ a → a ≈ 0#) → a ≈ 0#
  -- meta-right f = f (solve-≈ R)

  -- meta-both : ∀ {a} → (∀ {c d} → c * a ≈ d * a → a ≈ 0#) → a ≈ 0#
  -- meta-both f = f (solve-≈ R)

  -- meta-wrapped : (f : Carrier → Carrier) → ∀ {a} → (∀ {c} → a ≈ f c * a → a ≈ 0#) → a ≈ 0#
  -- meta-wrapped _ f = f (solve-≈ R)

module SucAtom where
  open import Data.Nat using (_+_; _*_; suc)
  open import Data.Nat.Properties using (+-*-commutativeSemiring)

  suc[n]-1+n : ∀ n → suc n ≡ 1 + n
  suc[n]-1+n = solve-≈ +-*-commutativeSemiring

  suc-suc : ∀ n → suc (suc n) ≡ 2 + n
  suc-suc = solve-≈ +-*-commutativeSemiring

  suc-distrib : ∀ n m → suc (n + m) ≡ suc n + m
  suc-distrib = solve-≈ +-*-commutativeSemiring

  suc-times : ∀ n → 2 * suc n ≡ 2 + 2 * n
  suc-times = solve-≈ +-*-commutativeSemiring

module BundleOnConcreteℤ where
  open import Data.Integer using (+_)
  open import Data.Integer.Properties using (+-*-commutativeSemiring)
  open CommutativeSemiring +-*-commutativeSemiring

  assoc* : ∀ a b c → ((a * b) * c) ≈ (a * (b * c))
  assoc* = solve-≈ +-*-commutativeSemiring

  comm+ : ∀ a b → (a + b) ≈ (b + a)
  comm+ = solve-≈ +-*-commutativeSemiring

  rearrange : ∀ a b c d → ((a + b) * (c + d)) ≈ (((a * c) + (a * d)) + ((b * c) + (b * d)))
  rearrange = solve-≈ +-*-commutativeSemiring

  -- `+_` works with literals and variables
  lit-zero+one : (+ 1) ≈ (+ 0) + (+ 1)
  lit-zero+one = solve-≈ +-*-commutativeSemiring

  lit-one*one : (+ 1) ≈ (+ 1) * (+ 1)
  lit-one*one = solve-≈ +-*-commutativeSemiring

  lit-two : (+ 2) ≈ (+ 1) + (+ 1)
  lit-two = solve-≈ +-*-commutativeSemiring

  comm+' : ∀ a b → (a + (+ b)) ≈ ((+ b) + a)
  comm+' = solve-≈ +-*-commutativeSemiring

  -- README `Tactic.RingSolver` lemmas on concrete ℤ.
  readme-lemma₁ : ∀ x y → (x + y) + (+ 3) ≈ (((+ 2) + y) + x) + (+ 1)
  readme-lemma₁ x y = solve-≈ +-*-commutativeSemiring

  readme-lemma₂ : ∀ x → (x * (+ 2)) + (+ 1) ≈ (x + (+ 1)) + x
  readme-lemma₂ x = solve-≈ +-*-commutativeSemiring

  readme-lemma₆ : ∀ x y → x + y * (+ 1) + (+ 3) ≈ (+ 2) + y + x + (+ 1)
  readme-lemma₆ x y = solve-≈ +-*-commutativeSemiring

------------------------------------------------------------------------
-- Concrete ℕ via `+-*-commutativeSemiring`.

module TestsℕConcrete where
  open import Data.Nat using (ℕ; _+_; _*_)
  open import Data.Nat.Properties using (+-*-commutativeSemiring)
  open CommutativeSemiring +-*-commutativeSemiring using (_≈_)

  comm+ : ∀ a b → (a + b) ≈ (b + a)
  comm+ = solve-≈ +-*-commutativeSemiring

  comm+-≈ : ∀ a b → (a + b) ≈ (b + a)
  comm+-≈ a b = solve-≈ +-*-commutativeSemiring

  comm* : ∀ a b → (a * b) ≈ (b * a)
  comm* = solve-≈ +-*-commutativeSemiring

  comm*-≈ : ∀ a b → (a * b) ≈ (b * a)
  comm*-≈ a b = solve-≈ +-*-commutativeSemiring

  assoc+ : ∀ a b c → ((a + b) + c) ≈ (a + (b + c))
  assoc+ = solve-≈ +-*-commutativeSemiring

  assoc+-≈ : ∀ a b c → ((a + b) + c) ≈ (a + (b + c))
  assoc+-≈ a b c = solve-≈ +-*-commutativeSemiring

  assoc* : ∀ a b c → ((a * b) * c) ≈ (a * (b * c))
  assoc* = solve-≈ +-*-commutativeSemiring

  assoc*-≈ : ∀ a b c → ((a * b) * c) ≈ (a * (b * c))
  assoc*-≈ a b c = solve-≈ +-*-commutativeSemiring

  distrib-test : ∀ a b c → (a * (b + c)) ≈ ((a * b) + (a * c))
  distrib-test = solve-≈ +-*-commutativeSemiring

  distrib-test-≈ : ∀ a b c → (a * (b + c)) ≈ ((a * b) + (a * c))
  distrib-test-≈ a b c = solve-≈ +-*-commutativeSemiring

  rearrange3 : ∀ a b c → (a + (b + c)) ≈ (b + (a + c))
  rearrange3 = solve-≈ +-*-commutativeSemiring

  rearrange3-≈ : ∀ a b c → (a + (b + c)) ≈ (b + (a + c))
  rearrange3-≈ a b c = solve-≈ +-*-commutativeSemiring

  rearrange4 : ∀ a b c d → (((a + b) + c) + d) ≈ (((d + c) + b) + a)
  rearrange4 = solve-≈ +-*-commutativeSemiring

  rearrange4-≈ : ∀ a b c d → (((a + b) + c) + d) ≈ (((d + c) + b) + a)
  rearrange4-≈ a b c d = solve-≈ +-*-commutativeSemiring

  expand2 : ∀ a b c d → ((a + b) * (c + d)) ≈ (((a * c) + (a * d)) + ((b * c) + (b * d)))
  expand2 = solve-≈ +-*-commutativeSemiring

  expand2-≈ : ∀ a b c d → ((a + b) * (c + d)) ≈ (((a * c) + (a * d)) + ((b * c) + (b * d)))
  expand2-≈ a b c d = solve-≈ +-*-commutativeSemiring

  twisted : ∀ a b c → ((a * b) + (b * c)) ≈ (b * (a + c))
  twisted = solve-≈ +-*-commutativeSemiring

  twisted-≈ : ∀ a b c → ((a * b) + (b * c)) ≈ (b * (a + c))
  twisted-≈ a b c = solve-≈ +-*-commutativeSemiring

  bigComm : ∀ a b c d e → ((((a + b) + c) + d) + e) ≈ ((((e + d) + c) + b) + a)
  bigComm = solve-≈ +-*-commutativeSemiring

  bigComm-≈ : ∀ a b c d e → ((((a + b) + c) + d) + e) ≈ ((((e + d) + c) + b) + a)
  bigComm-≈ a b c d e = solve-≈ +-*-commutativeSemiring

  nat-lit-1 : ∀ a → (1 + a) ≈ (a + 1)
  nat-lit-1 = solve-≈ +-*-commutativeSemiring

  nat-lit-1-≈ : ∀ a → (1 + a) ≈ (a + 1)
  nat-lit-1-≈ a = solve-≈ +-*-commutativeSemiring

  nat-lit-2 : ∀ a → (2 + a) ≈ (a + 2)
  nat-lit-2 = solve-≈ +-*-commutativeSemiring

  nat-lit-2-≈ : ∀ a → (2 + a) ≈ (a + 2)
  nat-lit-2-≈ a = solve-≈ +-*-commutativeSemiring

  nat-lit-3 : ∀ a → ((3 * a) + a) ≈ ((1 + 3) * a)
  nat-lit-3 = solve-≈ +-*-commutativeSemiring

  nat-lit-3-≈ : ∀ a → ((3 * a) + a) ≈ ((1 + 3) * a)
  nat-lit-3-≈ a = solve-≈ +-*-commutativeSemiring

  binomial : ∀ a → ((a + 1) * (a + 1)) ≈ (((a * a) + (2 * a)) + 1)
  binomial = solve-≈ +-*-commutativeSemiring

  binomial-≈ : ∀ a → ((a + 1) * (a + 1)) ≈ (((a * a) + (2 * a)) + 1)
  binomial-≈ a = solve-≈ +-*-commutativeSemiring

  affine : ∀ a b → ((2 * a) + (3 * b)) ≈ ((b + a) + ((b + a) + b))
  affine = solve-≈ +-*-commutativeSemiring

  affine-≈ : ∀ a b → ((2 * a) + (3 * b)) ≈ ((b + a) + ((b + a) + b))
  affine-≈ a b = solve-≈ +-*-commutativeSemiring

  -- ℕ's bundle `_≈_` IS propositional `_≡_`, so the macro discharges
  -- both forms.
  prop-eq : ∀ a b → (a + b) ≡ (b + a)
  prop-eq = solve-≈ +-*-commutativeSemiring

  prop-eq-≈ : ∀ a b → (a + b) ≡ (b + a)
  prop-eq-≈ a b = solve-≈ +-*-commutativeSemiring

  -- Concrete ℕ version of `(m*n)*(o*p) ≈ (m*o)*(n*p)`
  -- (`Data.Nat.Properties.[m*n]*[o*p]≡[m*o]*[n*p]`, proved by hand in
  -- stdlib).
  interchange* : ∀ m n o p → (m * n) * (o * p) ≈ (m * o) * (n * p)
  interchange* m n o p = solve-≈ +-*-commutativeSemiring

  -- Homomorphism patterns from `Data.Nat.Binary.Properties` (proofs
  -- that originally called `Data.Nat.Solver`).
  homo+-0even : ∀ m n → 2 * (2 + (m + n)) ≈ 2 * (1 + m) + 2 * (1 + n)
  homo+-0even m n = solve-≈ +-*-commutativeSemiring

  homo+-1odd : ∀ m n → 1 + (2 * (1 + (m + n))) ≈ 2 * (1 + m) + (1 + (2 * n))
  homo+-1odd m n = solve-≈ +-*-commutativeSemiring

  homo+-2even : ∀ m n → 1 + (1 + (2 * (m + n))) ≈ (1 + (2 * m)) + (1 + (2 * n))
  homo+-2even m n = solve-≈ +-*-commutativeSemiring

  homo*-evenodd : ∀ m n → 2 * (2 * (1 + (m + (n + m * n)))) ≈ (2 * (1 + m)) * (2 * (1 + n))
  homo*-evenodd m n = solve-≈ +-*-commutativeSemiring

  homo*-evenoddm : ∀ m n → 2 * ((1 + m) + (n * (2 * (1 + m)))) ≈ (2 * (1 + m)) * (1 + 2 * n)
  homo*-evenoddm m n = solve-≈ +-*-commutativeSemiring

  -- Literal-rich ℕ rearrangements from `Data.Integer.Properties.NatLemmas`
  -- (used by `*-distribʳ-+`'s case analysis).
  natlemma-assoc₁ : ∀ m n o → (2 + n + o) * (1 + m) ≈ (1 + n) * (1 + m) + (1 + o) * (1 + m)
  natlemma-assoc₁ m n o = solve-≈ +-*-commutativeSemiring

  natlemma-assoc₂ : ∀ m n o → (1 + n + (1 + o)) * (1 + m) ≈ (1 + n) * (1 + m) + (1 + o) * (1 + m)
  natlemma-assoc₂ m n o = solve-≈ +-*-commutativeSemiring

  natlemma-assoc₃ : ∀ m n o → m + (n + (1 + o)) * (1 + m) ≈ (1 + n) * (1 + m) + (m + o * (1 + m))
  natlemma-assoc₃ m n o = solve-≈ +-*-commutativeSemiring

  natlemma-inner-assoc : ∀ m n o →
      o + (n + m * (1 + n)) * (1 + o)
    ≈ o + n * (1 + o) + m * (1 + (o + n * (1 + o)))
  natlemma-inner-assoc m n o = solve-≈ +-*-commutativeSemiring

  -- README `Tactic.RingSolver` `NaturalExamples.lemma₁`.
  readme-lemma₁ : ∀ x y → x + y * 1 + 3 ≈ 2 + 1 + y + x
  readme-lemma₁ x y = solve-≈ +-*-commutativeSemiring

  -- README skew-heap tree-size invariant.
  tree-merge : ∀ a b c d → 1 + (1 + c + d + b) + a ≈ 1 + a + b + (1 + c + d)
  tree-merge a b c d = solve-≈ +-*-commutativeSemiring

------------------------------------------------------------------------
-- Concrete ℤ.

module TestsℤConcrete where
  open import Data.Integer using (ℤ; _+_; _*_; -_; _-_)
  open import Data.Integer.Properties using (+-*-commutativeSemiring)
  open CommutativeSemiring +-*-commutativeSemiring using (_≈_)

  comm+ : ∀ a b → (a + b) ≈ (b + a)
  comm+ = solve-≈ +-*-commutativeSemiring

  comm+-≈ : ∀ a b → (a + b) ≈ (b + a)
  comm+-≈ a b = solve-≈ +-*-commutativeSemiring

  assoc* : ∀ a b c → ((a * b) * c) ≈ (a * (b * c))
  assoc* = solve-≈ +-*-commutativeSemiring

  assoc*-≈ : ∀ a b c → ((a * b) * c) ≈ (a * (b * c))
  assoc*-≈ a b c = solve-≈ +-*-commutativeSemiring

  -- Negation / subtraction aren't in `CommutativeSemiring`'s
  -- vocabulary, so `_-_` and `-_` get atomised whole, breaking the
  -- proof.
  --
  -- neg-comm : ∀ a b → (- (a + b)) ≈ ((- a) + (- b))
  -- neg-comm = solve-≈ +-*-commutativeSemiring

  -- 4-variable rearrangements over ℤ.
  fourway-* : ∀ a b c d → (a * b) * (c * d) ≈ (a * c) * (b * d)
  fourway-* a b c d = solve-≈ +-*-commutativeSemiring

  fourway-+ : ∀ a b c d → (a + b) + (c + d) ≈ (a + c) + (b + d)
  fourway-+ a b c d = solve-≈ +-*-commutativeSemiring

  distribˡ : ∀ a b c → a * (b + c) ≈ a * b + a * c
  distribˡ a b c = solve-≈ +-*-commutativeSemiring

  -- 6-variable ℤ rearrangements from `Data.Rational.Unnormalised.Properties`
  -- (`+-cong`, `+-assoc-↥`, `*-distribˡ-+`-related lemmas).
  ratunnorm-+-cong : ∀ ↥x ↧x ↧y ↥u ↧u ↧v →
    (↥x * ↧u + ↥u * ↧x) * (↧y * ↧v) ≈ ↥x * ↧y * (↧u * ↧v) + ↥u * ↧v * (↧x * ↧y)
  ratunnorm-+-cong ↥x ↧x ↧y ↥u ↧u ↧v = solve-≈ +-*-commutativeSemiring

  ratunnorm-+-assoc : ∀ ↥p ↧p ↥q ↧q ↥r ↧r →
    (↥p * ↧q + ↥q * ↧p) * ↧r + ↥r * (↧p * ↧q) ≈ ↥p * (↧q * ↧r) + (↥q * ↧r + ↥r * ↧q) * ↧p
  ratunnorm-+-assoc ↥p ↧p ↥q ↧q ↥r ↧r = solve-≈ +-*-commutativeSemiring

  ratunnorm-distrib : ∀ ↥p ↧p ↥q d e f →
      (↥p * (↥q * f + e * d)) * (↧p * d * (↧p * f))
    ≈ (↥p * ↥q * (↧p * f) + ↥p * e * (↧p * d)) * (↧p * (d * f))
  ratunnorm-distrib ↥p ↧p ↥q d e f = solve-≈ +-*-commutativeSemiring

  -- 8-variable stress test on ℤ.
  big8 : ∀ a b c d e f g h →
      ((a + b) + (c + d)) * ((e + f) + (g + h))
    ≈ (((((a * e) + (a * f)) + ((a * g) + (a * h))) +
        (((b * e) + (b * f)) + ((b * g) + (b * h)))) +
       ((((c * e) + (c * f)) + ((c * g) + (c * h))) +
        (((d * e) + (d * f)) + ((d * g) + (d * h)))))
  big8 a b c d e f g h = solve-≈ +-*-commutativeSemiring

------------------------------------------------------------------------
-- Abstract parameterised `CommutativeSemiring`.

module TestsAbstractCSR {c ℓ} (R : CommutativeSemiring c ℓ) where
  open CommutativeSemiring R
  private module Eq = Setoid setoid

  -- Repeated occurrences of the same variable
  refl₁ : ∀ a → (a + a) ≈ (a + a)
  refl₁ = solve-≈ R

  refl₁-≈ : ∀ a → (a + a) ≈ (a + a)
  refl₁-≈ a = solve-≈ R

  comm+ : ∀ a b → (a + b) ≈ (b + a)
  comm+ = solve-≈ R

  comm+-≈ : ∀ a b → (a + b) ≈ (b + a)
  comm+-≈ a b = solve-≈ R

  comm* : ∀ a b → (a * b) ≈ (b * a)
  comm* = solve-≈ R

  comm*-≈ : ∀ a b → (a * b) ≈ (b * a)
  comm*-≈ a b = solve-≈ R

  assoc+ : ∀ a b c → ((a + b) + c) ≈ (a + (b + c))
  assoc+ = solve-≈ R

  assoc+-≈ : ∀ a b c → ((a + b) + c) ≈ (a + (b + c))
  assoc+-≈ a b c = solve-≈ R

  assoc* : ∀ a b c → ((a * b) * c) ≈ (a * (b * c))
  assoc* = solve-≈ R

  assoc*-≈ : ∀ a b c → ((a * b) * c) ≈ (a * (b * c))
  assoc*-≈ a b c = solve-≈ R

  distrib-test : ∀ a b c → (a * (b + c)) ≈ ((a * b) + (a * c))
  distrib-test = solve-≈ R

  distrib-test-≈ : ∀ a b c → (a * (b + c)) ≈ ((a * b) + (a * c))
  distrib-test-≈ a b c = solve-≈ R

  swap-mid : ∀ a b c → (a + (b + c)) ≈ (b + (a + c))
  swap-mid = solve-≈ R

  swap-mid-≈ : ∀ a b c → (a + (b + c)) ≈ (b + (a + c))
  swap-mid-≈ a b c = solve-≈ R

  deep+ : ∀ a b c d → ((a + b) + (c + d)) ≈ ((a + c) + (b + d))
  deep+ = solve-≈ R

  deep+-≈ : ∀ a b c d → ((a + b) + (c + d)) ≈ ((a + c) + (b + d))
  deep+-≈ a b c d = solve-≈ R

  deep* : ∀ a b c d → ((a * b) * (c * d)) ≈ ((a * c) * (b * d))
  deep* = solve-≈ R

  deep*-≈ : ∀ a b c d → ((a * b) * (c * d)) ≈ ((a * c) * (b * d))
  deep*-≈ a b c d = solve-≈ R

  square : ∀ a b → ((a + b) * (a + b)) ≈ (((a * a) + (a * b)) + ((b * a) + (b * b)))
  square = solve-≈ R

  square-≈ : ∀ a b → ((a + b) * (a + b)) ≈ (((a * a) + (a * b)) + ((b * a) + (b * b)))
  square-≈ a b = solve-≈ R

  big-expand : ∀ a b c d → ((a + b) * (c + d)) ≈ (((a * c) + (a * d)) + ((b * c) + (b * d)))
  big-expand = solve-≈ R

  big-expand-≈ : ∀ a b c d → ((a + b) * (c + d)) ≈ (((a * c) + (a * d)) + ((b * c) + (b * d)))
  big-expand-≈ a b c d = solve-≈ R

  -- The shape used in `Expectation.weight-sum-+`'s rearrangement.
  weight-sum-style : ∀ pω fω gω wsf wsg →
       (((pω * (fω + gω)) + (wsf + wsg)))
     ≈ ((((pω * fω) + wsf) + ((pω * gω) + wsg)))
  weight-sum-style = solve-≈ R

  weight-sum-style-≈ : ∀ pω fω gω wsf wsg →
       (((pω * (fω + gω)) + (wsf + wsg)))
     ≈ ((((pω * fω) + wsf) + ((pω * gω) + wsg)))
  weight-sum-style-≈ pω fω gω wsf wsg = solve-≈ R

  trans-congˡ : ∀ a b c → a + (b + c) ≈ (a + c) + b
  trans-congˡ a b c = Eq.trans
    (+-congˡ (+-comm b c))
    (solve-≈ R)

  six-vars : ∀ a b c d e f →
      ((((a + b) + c) + d) + (e + f))
    ≈ (((((f + e) + d) + c) + b) + a)
  six-vars = solve-≈ R

  six-vars-≈ : ∀ a b c d e f →
      ((((a + b) + c) + d) + (e + f))
    ≈ (((((f + e) + d) + c) + b) + a)
  six-vars-≈ a b c d e f = solve-≈ R

  seven-vars : ∀ a b c d e f g →
      ((a * (b + c)) * ((d + e) * (f + g)))
    ≈ ((((a * b) + (a * c)) * ((d * f) + (d * g))) + (((a * b) + (a * c)) * ((e * f) + (e * g))))
  seven-vars = solve-≈ R

  seven-vars-≈ : ∀ a b c d e f g →
      ((a * (b + c)) * ((d + e) * (f + g)))
    ≈ ((((a * b) + (a * c)) * ((d * f) + (d * g))) + (((a * b) + (a * c)) * ((e * f) + (e * g))))
  seven-vars-≈ a b c d e f g = solve-≈ R

  -- 9-term distributive expansion: (a+b+c)*(d+e+f).
  distrib-3-3 : ∀ a b c d e f →
    (a + b + c) * (d + e + f) ≈
    ((a * d + a * e) + a * f) +
    (((b * d + b * e) + b * f) +
     ((c * d + c * e) + c * f))
  distrib-3-3 a b c d e f = solve-≈ R

  -- Sum of squares with cross term (binomial expansion shape).
  sum-square : ∀ a b → (a + b) * (a + b) ≈ a * a + (1# + 1#) * (a * b) + b * b
  sum-square a b = solve-≈ R

  -- From `Data.Integer.Properties.suc-*` (after factoring through CSR):
  -- `sucℤ i * j ≡ j + i * j`, i.e. `(1# + i) * j ≈ j + i * j`.
  suc-* : ∀ i j → (1# + i) * j ≈ j + i * j
  suc-* i j = solve-≈ R

  -- Chain compression from `Algebra.Properties.Semiring.Exp`:
  -- `y * ((x * A) * B) ≈ x * (y * (A * B))`.
  exp-rearrange : ∀ x y A B → y * ((x * A) * B) ≈ x * (y * (A * B))
  exp-rearrange x y A B = solve-≈ R

  -- Representative permutation laws from
  -- `Algebra.Properties.CommutativeSemigroup` (read `_∙_` as `_+_`).
  perm-yxz : ∀ x y z → x + (y + z) ≈ y + (x + z)
  perm-yxz x y z = solve-≈ R

  perm-zyx : ∀ x y z → (x + y) + z ≈ (z + y) + x
  perm-zyx x y z = solve-≈ R

  -- Same shape against `_*_`.
  perm-yxz-* : ∀ x y z → x * (y * z) ≈ y * (x * z)
  perm-yxz-* x y z = solve-≈ R

  -- Semimedial and Jordan-style identities.
  semimedialˡ : ∀ x y z → (x + x) + (y + z) ≈ (x + y) + (x + z)
  semimedialˡ x y z = solve-≈ R

  jordan : ∀ x y → (x + y) + (x + x) ≈ x + (y + (x + x))
  jordan x y = solve-≈ R

------------------------------------------------------------------------
-- Constants and literal-coefficient identities.

module Constants {c ℓ} (R : CommutativeSemiring c ℓ) where
  open CommutativeSemiring R

  one-mul : ∀ a → (1# * a) ≈ a
  one-mul = solve-≈ R

  one-mul-≈ : ∀ a → (1# * a) ≈ a
  one-mul-≈ a = solve-≈ R

  one-mul' : ∀ a → (a * 1#) ≈ a
  one-mul' = solve-≈ R

  one-mul'-≈ : ∀ a → (a * 1#) ≈ a
  one-mul'-≈ a = solve-≈ R

  zero-add : ∀ a → (0# + a) ≈ a
  zero-add = solve-≈ R

  zero-add-≈ : ∀ a → (0# + a) ≈ a
  zero-add-≈ a = solve-≈ R

  zero-add' : ∀ a → (0# + (a + 0#)) ≈ a
  zero-add' = solve-≈ R

  zero-add'-≈ : ∀ a → (0# + (a + 0#)) ≈ a
  zero-add'-≈ a = solve-≈ R

  nat-coeff : ∀ a → (a + a) ≈ ((1# + 1#) * a)
  nat-coeff = solve-≈ R

  nat-coeff-≈ : ∀ a → (a + a) ≈ ((1# + 1#) * a)
  nat-coeff-≈ a = solve-≈ R

  three-mul : ∀ a → ((a + a) + a) ≈ (((1# + 1#) + 1#) * a)
  three-mul = solve-≈ R

  three-mul-≈ : ∀ a → ((a + a) + a) ≈ (((1# + 1#) + 1#) * a)
  three-mul-≈ a = solve-≈ R

  expand-square-of-sum-of-ones : ∀ a → ((1# + 1#) * (a + a)) ≈ ((a + a) + (a + a))
  expand-square-of-sum-of-ones = solve-≈ R

  expand-square-of-sum-of-ones-≈ : ∀ a → ((1# + 1#) * (a + a)) ≈ ((a + a) + (a + a))
  expand-square-of-sum-of-ones-≈ a = solve-≈ R

  zero-mul : ∀ a → (0# * a) ≈ 0#
  zero-mul = solve-≈ R

  zero-mul-≈ : ∀ a → (0# * a) ≈ 0#
  zero-mul-≈ a = solve-≈ R

  zero-mul' : ∀ a → (a * 0#) ≈ 0#
  zero-mul' = solve-≈ R

  zero-mul'-≈ : ∀ a → (a * 0#) ≈ 0#
  zero-mul'-≈ a = solve-≈ R

  zero+xy : ∀ x y → 0# + x * y ≈ x * y
  zero+xy x y = solve-≈ R

  with-extra-≈ : (k : Carrier) → ∀ a → ((k * a) + a) ≈ ((k + 1#) * a)
  with-extra-≈ k a = solve-≈ R

------------------------------------------------------------------------
-- Tests with free function-typed atoms.  The function variables
-- have to be introduced as patterns (since neither macro abstracts
-- over Carrier-typed function values, and `solve-≈` needs them in
-- scope to collect their applications as atoms); the Carrier-typed
-- `a` stays under the goal's pi-binder.

module FunctionAtoms {c ℓ} (R : CommutativeSemiring c ℓ) where
  open CommutativeSemiring R

  fn-atoms : (f g : Carrier → Carrier) (a : Carrier)
           → ((f a) + (g a)) ≈ ((g a) + (f a))
  fn-atoms f g = solve-≈ R

  -- Composite atoms aren't peered into; `f (g a)` is one atom.
  nested : (f g : Carrier → Carrier) (a : Carrier)
         → ((f (g a)) + a) ≈ (a + (f (g a)))
  nested f g = solve-≈ R

  mixed-with-const : (a : Carrier) → (1# * a) + a ≈ (1# + 1#) * a
  mixed-with-const a = solve-≈ R

  larger : (a b c d e : Carrier)
         → ((a * (b + c)) + (d + e))
         ≈ (((a * b) + d) + ((a * c) + e))
  larger a b c d e = solve-≈ R

  -- Inline use within an `≈⟨ … ⟩` reasoning chain.
  module InContext (k : Carrier) where
    open import Relation.Binary.Reasoning.Setoid setoid
    reasoning : (a b : Carrier) → (k * (a + b)) ≈ ((k * a) + (k * b))
    reasoning a b = begin
      k * (a + b)         ≈⟨ solve-≈ R ⟩
      (k * a) + (k * b)   ∎

  -- Composite atoms are atomised whole, so a goal that rearranges
  -- their *internals* sees them as distinct variables and fails:
  --
  -- opaque-internal : (f : Carrier → Carrier) (a b : Carrier)
  --                 → (f (a + b)) ≈ (f (b + a))
  -- opaque-internal f a b = solve-≈ R

------------------------------------------------------------------------
-- Stress test.

module StressTest {c ℓ} (R : CommutativeSemiring c ℓ) where
  open CommutativeSemiring R

  big8 : ∀ a b c d e f g h →
      (((a + b) * (c + d)) + ((e + f) * (g + h)))
    ≈ (((c + d) * (a + b)) + ((g + h) * (e + f)))
  big8 = solve-≈ R

  big8-≈ : ∀ a b c d e f g h →
      (((a + b) * (c + d)) + ((e + f) * (g + h)))
    ≈ (((c + d) * (a + b)) + ((g + h) * (e + f)))
  big8-≈ a b c d e f g h = solve-≈ R

  expand8 : ∀ a b c d e f g h →
      (((a + b) + (c + d)) * ((e + f) + (g + h)))
    ≈ (((((a * e) + (a * f)) + ((a * g) + (a * h))) +
        (((b * e) + (b * f)) + ((b * g) + (b * h)))) +
       ((((c * e) + (c * f)) + ((c * g) + (c * h))) +
        (((d * e) + (d * f)) + ((d * g) + (d * h)))))
  expand8 = solve-≈ R

  expand8-≈ : ∀ a b c d e f g h →
      (((a + b) + (c + d)) * ((e + f) + (g + h)))
    ≈ (((((a * e) + (a * f)) + ((a * g) + (a * h))) +
        (((b * e) + (b * f)) + ((b * g) + (b * h)))) +
       ((((c * e) + (c * f)) + ((c * g) + (c * h))) +
        (((d * e) + (d * f)) + ((d * g) + (d * h)))))
  expand8-≈ a b c d e f g h = solve-≈ R
