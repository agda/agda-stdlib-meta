{-# OPTIONS --safe --without-K #-}
-- {-# OPTIONS -v tactic.rewrite:100 #-}
module Tactic.Rewrite where

open import Meta.Prelude hiding (_^_)

open import Data.List.Membership.DecPropositional using (_∈?_)
open import Data.Product using (map₂)
open import Relation.Nullary.Decidable using (⌊_⌋)

open import Reflection hiding (_>>=_; _>>_; _≟_)
open import Reflection.QuotedDefinitions
open import Reflection.Syntax
open import Reflection.Tactic
open import Reflection.Utils.Debug; open Debug ("tactic.rewrite" , 100)

open import Class.DecEq
open import Class.Functor
open import Class.Monad
open import Class.Semigroup
open import Class.Show

viewEq : Term → TC (Term × Term)
viewEq eq = do
  x ``≡ y ← inferType eq
    where _ → error "Can only write with equalities `x ≡ y`."
  return (x , y)

module _ (apply⁇ : ℕ → Bool) where

  getFocus : Term → Term → Term
  getFocus x = `λ "◆" ⇒_ ∘ proj₂ ∘ go 0 0
    where
      go : ℕ → ℕ → Term → Bool × Term
      go k n t =
        if (x == t) then
          true , (if apply⁇ k then (var n []) else x)
        else case t of λ where
          (con c as) → map₂ (con c) (goArgs k as)
          (def s as) → let b , as′ = goArgs k as
                      in b , def s as′
          (lam v (abs s a)) →
            let b , a′ = go k (suc n) a
            in b , lam v (abs s a′)
          (pat-lam cs as) →
            let b , cs′  = goCs k cs
                k′       = if b then suc k else k
                b′ , as′ = goArgs k′ as
            in  b ∨ b′ , pat-lam cs′ as′
          (pi (arg i a) (abs s P)) →
            let b , a′  = go k n a
                k′      = if b then suc k else k
                b′ , P′ = go k′ (suc n) P
            in (b ∨ b′) , pi (arg i a′) (abs s P′)
          _ → false , t
        where
          goArgs : ℕ → Args Term → Bool × Args Term
          goArgs _ []       = false , []
          goArgs k (arg i a ∷ as) =
            let b , a′   = go k n a
                k′       = if b then suc k else k
                b′ , as′ = goArgs k′ as
            in b ∨ b′ , arg i a′ ∷ as′

          goTel : ℕ → Telescope → Bool × Telescope
          goTel _ []       = false , []
          goTel k ((s , arg i t) ∷ ts) =
            let b , t′   = go k n t
                k′       = if b then suc k else k
                b′ , ts′ = goTel k′ ts
            in b ∨ b′ , (s , arg i t′) ∷ ts′

          mutual
            goP : ℕ → Pattern → Bool × Pattern
            goP k = λ where
              (con c ps) → map₂ (con c) (goPs k ps)
              (dot t) → map₂ dot $ go k n t
              p → false , p

            goPs : ℕ → Args Pattern → Bool × Args Pattern
            goPs _ []       = false , []
            goPs k (arg i p ∷ ps) =
              let b , p′   = goP k p
                  k′       = if b then suc k else k
                  b′ , ps′ = goPs k′ ps
              in b ∨ b′ , arg i p′ ∷ ps′

          goC : ℕ → Clause → Bool × Clause
          goC k = λ where
            (clause tel ps t) →
              let b , tel′  = goTel k tel
                  k′        = if b then suc k else k
                  b′ , ps′  = goPs k′ ps
                  k″        = if b′ then suc k′ else k′
                  b″ , t′   = go k″ n t
              in b ∨ b′ ∨ b″ , clause tel′ ps′ t′
            (absurd-clause tel ps) →
              let b , tel′  = goTel k tel
                  k′        = if b then suc k else k
                  b′ , ps′  = goPs k′ ps
              in b ∨ b′ , absurd-clause tel′ ps′

          goCs : ℕ → List Clause → Bool × List Clause
          goCs _ []       = false , []
          goCs k (c ∷ cs) =
            let b , c′   = goC k c
                k′       = if b then suc k else k
                b′ , cs′ = goCs k′ cs
            in b ∨ b′ , c′ ∷ cs′

  `subst `subst˘ : Type → Term → Term → Term → Term
  `subst  ty x eq t = quote subst ∙⟦ getFocus x ty ∣ eq ∣ t ⟧
  `subst˘ ty x eq t = `subst ty x (quote sym ∙⟦ eq ⟧) t

  rw : (Term → Term → Term → Term) → Term → A → Tactic
  rw {A = A} sub eq `t hole = do
    t ← quoteTC (A ∋ `t)
    x , y ← viewEq eq
    print $ "Rewriting: " ◇ show x ◇ " ≡ " ◇ show y
          ◇ "\n\t in:" ◇ show t
    let t′ = sub x eq t
    print $ " ⇒⇒⇒ " ◇ show t′
    unify hole t′

  rwAt : A → Term → Tactic
  rwAt {A = A} `t eq hole = do
    ty ← quoteTC A
    rw (`subst ty) eq `t hole

  rwBy : Term → A → Tactic
  rwBy eq `t hole = do
    ty ← inferType hole
    rw (`subst˘ ty) eq `t hole

∗ : ℕ → Bool
∗ = const true

macro
  ⟪_⟫_≈:_ = rwBy
  ⟪_⟫_:≈_ = rwAt
  _≈:_    = rwBy ∗
  _:≈_    = rwAt ∗


-- ** n-ary commands
private
  _^_ : Set ℓ → ℕ → Set ℓ
  A ^ 0     = A
  A ^ suc n = A × (A ^ n)

  ⟦_⟧ : ∀ {n : ℕ} → ℕ ^ n → List ℕ
  ⟦_⟧ {n = zero}  x        = [ x ]
  ⟦_⟧ {n = suc n} (x , xs) = x ∷ ⟦ xs ⟧

  open import Class.DecEq

  _∈ᵇ_ : ℕ → List ℕ → Bool
  x ∈ᵇ xs = ⌊ _∈?_ _≟_ x xs ⌋

macro
  ⟪[_]⟫_≈:_ : ∀ {n} → ℕ ^ n → Term → A → Tactic
  ⟪[ is ]⟫ eq ≈: t = rwBy (_∈ᵇ ⟦_⟧ is) eq t

  ⟪[_]⟫_:≈_ : ∀ {n} → ℕ ^ n → A → Term → Tactic
  ⟪[ is ]⟫ t :≈ eq = rwAt (_∈ᵇ ⟦_⟧ is) t eq
