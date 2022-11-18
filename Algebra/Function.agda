{-# OPTIONS --safe --without-K #-}

open import Level
open import Algebra
open import Data.Product

module Algebra.Function where

  module _ {a b c} (A : Set a) (B : BooleanAlgebra b c) where
    module B = BooleanAlgebra B

    Carrier : Set (a ⊔ b)
    Carrier = A → B.Carrier

    _≈_ : Carrier → Carrier → Set (a ⊔ c)
    _≈_ f g = ∀ a → f a B.≈ g a

    _∨_ : Carrier → Carrier → Carrier
    _∨_ f g a = f a B.∨ g a

    _∧_ : Carrier → Carrier → Carrier
    _∧_ f g a = f a B.∧ g a

    ¬_ : Carrier → Carrier
    ¬_ f a = B.¬ f a

    ⊤ : Carrier
    ⊤ a = B.⊤

    ⊥ : Carrier
    ⊥ a = B.⊥

    open import Function.Equality
    open import Relation.Binary using (Setoid)
    import Relation.Binary.Indexed.Heterogeneous.Construct.Trivial
      as Trivial

    open IsLattice
    isLattice' : IsLattice _≈_ _∨_ _∧_
    isLattice' = record
      { isEquivalence = Setoid.isEquivalence (≡-setoid A (Trivial.indexedSetoid B.setoid))
      ; ∨-comm = λ f g a → B.isLattice .∨-comm (f a) (g a)
      ; ∨-assoc = λ x y z a → B.isLattice .∨-assoc (x a) (y a) (z a)
      ; ∨-cong = λ eq₁ eq₂ a → B.isLattice .∨-cong (eq₁ a) (eq₂ a)
      ; ∧-comm = λ f g a → B.isLattice .∧-comm (f a) (g a)
      ; ∧-assoc = λ x y z a → B.isLattice .∧-assoc (x a) (y a) (z a)
      ; ∧-cong = λ eq₁ eq₂ a → B.isLattice .∧-cong (eq₁ a) (eq₂ a)
      ; absorptive =
        (λ x y a → B.isLattice .absorptive .proj₁ (x a) (y a)) ,
        (λ x y a → B.isLattice .absorptive .proj₂ (x a) (y a))
      }

    open IsDistributiveLattice
    isDistributiveLattice' : IsDistributiveLattice _≈_ _∨_ _∧_
    isDistributiveLattice' .isLattice = isLattice'
    isDistributiveLattice' .∨-distribʳ-∧ = λ x y z a → B.isDistributiveLattice .∨-distribʳ-∧ (x a) (y a) (z a)

    open IsBooleanAlgebra
    isBooleanAlgebra : IsBooleanAlgebra _≈_ _∨_ _∧_ ¬_ ⊤ ⊥
    isBooleanAlgebra .isDistributiveLattice = isDistributiveLattice'
    isBooleanAlgebra .∨-complementʳ = λ f a → B.isBooleanAlgebra .∨-complementʳ (f a)
    isBooleanAlgebra .∧-complementʳ = λ f a → B.isBooleanAlgebra .∧-complementʳ (f a)
    isBooleanAlgebra .¬-cong = λ f a → B.isBooleanAlgebra .¬-cong (f a)

    hom : BooleanAlgebra _ _
    hom = record
            { Carrier = Carrier
            ; _≈_ = _≈_
            ; _∨_ = _∨_
            ; _∧_ = _∧_
            ; ¬_ = ¬_
            ; ⊤ = ⊤
            ; ⊥ = ⊥
            ; isBooleanAlgebra = isBooleanAlgebra
            }
