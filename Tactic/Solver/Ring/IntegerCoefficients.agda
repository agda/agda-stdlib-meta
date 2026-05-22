------------------------------------------------------------------------
-- Instantiates `Algebra.Solver.Ring` for a `CommutativeRing` using
-- ℤ as the coefficient ring — the CR analogue of stdlib's
-- `Algebra.Solver.Ring.NaturalCoefficients`. The target ACR is
-- `fromCommutativeRing R` (real negation), so the polynomial AST's
-- `:-_` and `_:-_` carry through to genuine ring negation.

{-# OPTIONS --without-K --safe #-}

open import Algebra using (CommutativeRing)

module Tactic.Solver.Ring.IntegerCoefficients
  {c ℓ} (R : CommutativeRing c ℓ) where

open import Algebra.Bundles using (RawRing)
open import Algebra.Solver.Ring.AlmostCommutativeRing
  using (AlmostCommutativeRing; fromCommutativeRing ; _-Raw-AlmostCommutative⟶_)
open import Data.Fin.Base using (Fin)
open import Data.Integer.Base as ℤ using (ℤ; +_; -[1+_]; _⊖_; _◃_)
open import Data.Integer.Properties as ℤP
  using ([1+m]⊖[1+n]≡m⊖n; +◃n≡+n; _≟_)
open import Data.Maybe.Base using (Maybe; nothing; just)
open import Data.Nat.Base as ℕ using (ℕ; zero; suc)
import Data.Nat.Properties as ℕP
import Data.Sign.Base as Sign
open import Function.Base using (case_of_)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)
open import Relation.Nullary using (yes; no)

open CommutativeRing R
-- The TC-optimised `_×_` (= `_×′_`) is essential: its `1 ×′ x = x`
-- special case makes the polynomial-AST `con 1` evaluate to `1#`
-- (and `con 0` to `0#`). The basic `_×_` from
-- `Algebra.Properties.Monoid.Mult` reduces `1 × x` to `x + 0#`,
-- which gives the solver's emitted proofs the wrong shape.
open import Algebra.Properties.Semiring.Mult.TCOptimised semiring
  using (_×_; ×-homo-+; ×1-homo-*)
open import Algebra.Properties.Monoid.Mult.TCOptimised +-monoid
  using (1+×)
open import Algebra.Properties.Ring ring as RingProps
  using (-‿involutive; -0#≈0#; -‿+-comm; -‿distribˡ-*; -‿distribʳ-*)
open import Relation.Binary.Reasoning.Setoid setoid

R-acr : AlmostCommutativeRing c ℓ
R-acr = fromCommutativeRing R

------------------------------------------------------------------------
-- Integer scalar multiplication on the ring.

infixl 7 _×ᶻ_

_×ᶻ_ : ℤ → Carrier → Carrier
(+ n)       ×ᶻ x = n × x
(-[1+ n ])  ×ᶻ x = - (suc n × x)

ℤ-rawRing : RawRing _ _
ℤ-rawRing = record
  { Carrier = ℤ
  ; _≈_     = _≡_
  ; _+_     = ℤ._+_
  ; _*_     = ℤ._*_
  ; -_      = ℤ.-_
  ; 0#      = + 0
  ; 1#      = + 1
  }

⟦_⟧ : ℤ → Carrier
⟦ z ⟧ = z ×ᶻ 1#

------------------------------------------------------------------------
-- The five homomorphism conditions.

0-homo : ⟦ + 0 ⟧ ≈ 0#
0-homo = refl

-- `1 ×′ x = x` definitionally (TCOptimised).
1-homo : ⟦ + 1 ⟧ ≈ 1#
1-homo = refl

-‿homo : ∀ z → ⟦ ℤ.- z ⟧ ≈ - ⟦ z ⟧
-‿homo (+ zero)    = sym -0#≈0#
-‿homo (+ suc n)   = refl                 -- ℤ.-(+ suc n) = -[1+ n]
-‿homo (-[1+ n ])  = sym (-‿involutive _) -- ℤ.-(-[1+ n]) = + suc n

private
  -- Cancels a shared leading `a` on the addition side.
  cancel-prefix : ∀ a b c → (a + b) + - (a + c) ≈ b + - c
  cancel-prefix a b c = begin
    (a + b) + - (a + c)        ≈⟨ +-congˡ (sym (-‿+-comm a c)) ⟩
    (a + b) + (- a + - c)      ≈⟨ +-assoc a b (- a + - c) ⟩
    a + (b + (- a + - c))      ≈⟨ +-congˡ (sym (+-assoc b (- a) (- c))) ⟩
    a + ((b + - a) + - c)      ≈⟨ +-congˡ (+-congʳ (+-comm b (- a))) ⟩
    a + ((- a + b) + - c)      ≈⟨ +-congˡ (+-assoc (- a) b (- c)) ⟩
    a + (- a + (b + - c))      ≈⟨ sym (+-assoc a (- a) (b + - c)) ⟩
    (a + - a) + (b + - c)      ≈⟨ +-congʳ (-‿inverseʳ a) ⟩
    0# + (b + - c)             ≈⟨ +-identityˡ (b + - c) ⟩
    b + - c                    ∎

-- The asymmetric ℕ-subtraction `_⊖_` is what ℤ's addition uses
-- internally for mixed-sign cases.
⊖-lemma : ∀ m n → (m ⊖ n) ×ᶻ 1# ≈ m × 1# + - (n × 1#)
⊖-lemma zero    zero    = begin
  0#                  ≈⟨ sym (+-identityʳ _) ⟩
  0# + 0#             ≈⟨ +-congˡ (sym -0#≈0#) ⟩
  0# + - 0#           ∎
⊖-lemma (suc m) zero    = begin
  suc m × 1#          ≈⟨ sym (+-identityʳ _) ⟩
  suc m × 1# + 0#     ≈⟨ +-congˡ (sym -0#≈0#) ⟩
  suc m × 1# + - 0#   ∎
⊖-lemma zero    (suc n) = begin
  -(suc n × 1#)              ≈⟨ sym (+-identityˡ _) ⟩
  0# + -(suc n × 1#)         ∎
⊖-lemma (suc m) (suc n) = begin
  -- `suc m ⊖ suc n ≡ m ⊖ n`, but `_⊖_` is defined via `_<ᵇ_`/`_∸_`
  -- and so the equation isn't definitional — we use the stdlib
  -- propositional lemma here.
  (suc m ⊖ suc n) ×ᶻ 1#                ≡⟨ ≡.cong (_×ᶻ 1#) ([1+m]⊖[1+n]≡m⊖n m n) ⟩
  (m ⊖ n) ×ᶻ 1#                         ≈⟨ ⊖-lemma m n ⟩
  m × 1# + - (n × 1#)                   ≈⟨ sym (cancel-prefix 1# (m × 1#) (n × 1#)) ⟩
  (1# + m × 1#) + - (1# + n × 1#)       ≈⟨ sym (+-cong (1+× m 1#) (-‿cong (1+× n 1#))) ⟩
  suc m × 1# + - (suc n × 1#)           ∎

+-homo : ∀ a b → ⟦ a ℤ.+ b ⟧ ≈ ⟦ a ⟧ + ⟦ b ⟧
+-homo (+ m)      (+ n)      = ×-homo-+ 1# m n
+-homo (+ m)      (-[1+ n ]) = ⊖-lemma m (suc n)
+-homo (-[1+ m ]) (+ n)      = begin
  (n ⊖ suc m) ×ᶻ 1#                       ≈⟨ ⊖-lemma n (suc m) ⟩
  n × 1# + - (suc m × 1#)                 ≈⟨ +-comm _ _ ⟩
  - (suc m × 1#) + n × 1#                 ∎
+-homo (-[1+ m ]) (-[1+ n ]) = begin
  -[1+ suc (m ℕ.+ n) ] ×ᶻ 1#              ≡⟨⟩
  - (suc (suc (m ℕ.+ n)) × 1#)            ≡⟨ ≡.cong (λ k → - (k × 1#))
                                                      (≡.cong suc (≡.sym (ℕP.+-suc m n))) ⟩
  - ((suc m ℕ.+ suc n) × 1#)              ≈⟨ -‿cong (×-homo-+ 1# (suc m) (suc n)) ⟩
  - (suc m × 1# + suc n × 1#)             ≈⟨ sym (-‿+-comm (suc m × 1#) (suc n × 1#)) ⟩
  - (suc m × 1#) + - (suc n × 1#)         ∎

private
  -- `ℤ._*_` is defined uniformly via signs (not pattern-matched on
  -- ℤ constructors), so these lemmas project the four sign-case
  -- normalisations we need.

  -- `Sign.- ◃ k ≡ ℤ.- (+ k)`.
  -◃≡-+ : ∀ k → Sign.- ◃ k ≡ ℤ.- (+ k)
  -◃≡-+ zero    = ≡.refl
  -◃≡-+ (suc _) = ≡.refl

  pos*pos : ∀ m n → (+ m) ℤ.* (+ n) ≡ + (m ℕ.* n)
  pos*pos m n = +◃n≡+n (m ℕ.* n)

  pos*neg : ∀ m n → (+ m) ℤ.* (-[1+ n ]) ≡ ℤ.- (+ (m ℕ.* suc n))
  pos*neg m n = -◃≡-+ (m ℕ.* suc n)

  neg*pos : ∀ m n → (-[1+ m ]) ℤ.* (+ n) ≡ ℤ.- (+ (suc m ℕ.* n))
  neg*pos m n = -◃≡-+ (suc m ℕ.* n)

  neg*neg : ∀ m n → (-[1+ m ]) ℤ.* (-[1+ n ]) ≡ + (suc m ℕ.* suc n)
  neg*neg m n = +◃n≡+n (suc m ℕ.* suc n)

*-homo : ∀ a b → ⟦ a ℤ.* b ⟧ ≈ ⟦ a ⟧ * ⟦ b ⟧
*-homo (+ m)      (+ n)      = begin
  ⟦ (+ m) ℤ.* (+ n) ⟧             ≡⟨ ≡.cong ⟦_⟧ (pos*pos m n) ⟩
  ⟦ + (m ℕ.* n) ⟧                 ≡⟨⟩
  (m ℕ.* n) × 1#                  ≈⟨ ×1-homo-* m n ⟩
  (m × 1#) * (n × 1#)             ∎
*-homo (+ m)      (-[1+ n ]) = begin
  ⟦ (+ m) ℤ.* (-[1+ n ]) ⟧        ≡⟨ ≡.cong ⟦_⟧ (pos*neg m n) ⟩
  ⟦ ℤ.- (+ (m ℕ.* suc n)) ⟧       ≈⟨ -‿homo (+ (m ℕ.* suc n)) ⟩
  - ⟦ + (m ℕ.* suc n) ⟧           ≡⟨⟩
  - ((m ℕ.* suc n) × 1#)          ≈⟨ -‿cong (×1-homo-* m (suc n)) ⟩
  - ((m × 1#) * (suc n × 1#))     ≈⟨ -‿distribʳ-* (m × 1#) (suc n × 1#) ⟩
  (m × 1#) * - (suc n × 1#)       ∎
*-homo (-[1+ m ]) (+ n)      = begin
  ⟦ (-[1+ m ]) ℤ.* (+ n) ⟧        ≡⟨ ≡.cong ⟦_⟧ (neg*pos m n) ⟩
  ⟦ ℤ.- (+ (suc m ℕ.* n)) ⟧       ≈⟨ -‿homo (+ (suc m ℕ.* n)) ⟩
  - ⟦ + (suc m ℕ.* n) ⟧           ≡⟨⟩
  - ((suc m ℕ.* n) × 1#)          ≈⟨ -‿cong (×1-homo-* (suc m) n) ⟩
  - ((suc m × 1#) * (n × 1#))     ≈⟨ -‿distribˡ-* (suc m × 1#) (n × 1#) ⟩
  - (suc m × 1#) * (n × 1#)       ∎
*-homo (-[1+ m ]) (-[1+ n ]) = begin
  ⟦ (-[1+ m ]) ℤ.* (-[1+ n ]) ⟧        ≡⟨ ≡.cong ⟦_⟧ (neg*neg m n) ⟩
  ⟦ + (suc m ℕ.* suc n) ⟧              ≡⟨⟩
  (suc m ℕ.* suc n) × 1#               ≈⟨ ×1-homo-* (suc m) (suc n) ⟩
  (suc m × 1#) * (suc n × 1#)          ≈⟨ sym (-‿involutive _) ⟩
  - (- ((suc m × 1#) * (suc n × 1#)))  ≈⟨ -‿cong (-‿distribˡ-* (suc m × 1#) (suc n × 1#)) ⟩
  - (- (suc m × 1#) * (suc n × 1#))    ≈⟨ -‿distribʳ-* (- (suc m × 1#)) (suc n × 1#) ⟩
  - (suc m × 1#) * - (suc n × 1#)      ∎

morphism : ℤ-rawRing -Raw-AlmostCommutative⟶ R-acr
morphism = record
  { ⟦_⟧    = ⟦_⟧
  ; +-homo = +-homo
  ; *-homo = *-homo
  ; -‿homo = -‿homo
  ; 0-homo = 0-homo
  ; 1-homo = 1-homo
  }

-- A non-trivial `dec` is essential: without it the underlying solver
-- can't fold `1 *_` / `0 +_` during Horner normalisation, and even
-- `1# * a ≈ a` fails. ℤ equality is decidable, so we can always
-- return `just` on equal coefficients.
dec : ∀ m n → Maybe (m ×ᶻ 1# ≈ n ×ᶻ 1#)
dec m n = case m ≟ n of λ where
  (yes m≡n) → just (reflexive (≡.cong (_×ᶻ 1#) m≡n))
  (no  _)   → nothing

-- `hiding (⟦_⟧)`: `Algebra.Solver.Ring` re-exports the morphism's
-- `⟦_⟧`, which would shadow our own.
open import Algebra.Solver.Ring ℤ-rawRing R-acr morphism dec public
  hiding (⟦_⟧)

------------------------------------------------------------------------
-- Top-level aliases so the macro can reflect `con`, `var`, `:-_` by
-- name (they're constructors nested inside `Algebra.Solver.Ring`'s
-- four-parameter module otherwise). The `def`-shaped `_:+_`, `_:*_`,
-- `_:-_`, `_:=_` don't need aliases.

conP : ∀ {n} → ℤ → Polynomial n
conP = con

varP : ∀ {n} → Fin n → Polynomial n
varP = var

negP : ∀ {n} → Polynomial n → Polynomial n
negP = :-_
