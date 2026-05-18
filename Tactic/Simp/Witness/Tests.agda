-- Examples for the `Tactic.Simp.Witness` proof-witness algebra.
--
-- Three key examples, all proved without macros or reflection:
--
--   key-example  : (n + 0) + 0 ≡ n            -- hand-built chain
--   key-example₂ : (l ++ []) ++ [] ≡ l        -- greedy-discovered, single-sorted
--   key-example₃ : length (map f l) ≡ length l -- greedy-discovered, multi-sorted

{-# OPTIONS --safe #-}

module Tactic.Simp.Witness.Tests where

open import Data.List as L            using (List; []; _∷_; _++_)
open import Data.List.Properties      using (++-identityʳ; length-map)
open import Data.Nat                  using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties       using (+-identityʳ)
open import Data.Product              using (_,_; Σ; proj₂)
open import Data.Unit                 using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Tactic.Simp.Witness

private variable
  A B : Set

private

  ----------------------------------------------------------------
  -- key-example: (n + 0) + 0 ≡ n  (hand-built chain over `_+_`)
  ----------------------------------------------------------------

  data EqAtom : ℕ → ℕ → Set where
    +-idʳ : (m : ℕ) → EqAtom (m + 0) m

  interpret : ∀ {a b} → EqAtom a b → a ≡ b
  interpret (+-idʳ m) = +-identityʳ m

  keyChain : ∀ {n} → Chain EqAtom ((n + 0) + 0) n
  keyChain {n} = rule (+-idʳ (n + 0)) ∙ rule (+-idʳ n)

  key-example : ∀ {n} → (n + 0) + 0 ≡ n
  key-example = reify interpret keyChain

  ----------------------------------------------------------------
  -- key-example₂: (l ++ []) ++ [] ≡ l  (greedy-discovered chain
  --                                     over a single-sorted L-sig)
  ----------------------------------------------------------------

  data ListOp : List ⊤ → ⊤ → Set where
    NIL : ListOp [] tt
    CAT : ListOp (tt ∷ tt ∷ []) tt

  L-sig : Signature
  L-sig = record { Sort = ⊤ ; Op = ListOp }

  ⟨[]⟩ : Expr L-sig tt
  ⟨[]⟩ = apply NIL ε

  infixr 6 _⊞_
  _⊞_ : Expr L-sig tt → Expr L-sig tt → Expr L-sig tt
  e₁ ⊞ e₂ = apply CAT (e₁ ◂ e₂ ◂ ε)

  ----------------------------------------------------------------
  -- key-example₃: length (map f l) ≡ length l  (multi-sorted)
  --
  -- Three sorts coexist: `list-A`, `list-B`, `nat`.  `map-f`
  -- crosses from `list-A` to `list-B`; `length-A` and `length-B`
  -- are distinct operations even though both produce `nat`.
  ----------------------------------------------------------------

  data MSort : Set where
    list-A list-B nat : MSort

  data MOp : List MSort → MSort → Set where
    length-A : MOp (list-A ∷ []) nat
    length-B : MOp (list-B ∷ []) nat
    map-f    : MOp (list-A ∷ []) list-B

  M-sig : Signature
  M-sig = record { Sort = MSort ; Op = MOp }

  -- All instance-level definitions live inside `module _ {A : Set}`
  -- to pin the universe level to `Set₀`.
  module _ {A : Set} where

    ⟦_⟧L : Expr L-sig tt → (ℕ → List A) → List A
    ⟦ var x                    ⟧L ρ = ρ x
    ⟦ apply NIL ε              ⟧L _ = []
    ⟦ apply CAT (e₁ ◂ e₂ ◂ ε)  ⟧L ρ = ⟦ e₁ ⟧L ρ ++ ⟦ e₂ ⟧L ρ

    data ListAtom : List A → List A → Set where
      ++-idʳᴬ : (xs : List A) → ListAtom (xs ++ []) xs

    interpretL : {xs ys : List A} → ListAtom xs ys → xs ≡ ys
    interpretL (++-idʳᴬ xs) = ++-identityʳ xs

    greedyL : (ρ : ℕ → List A) → ℕ → (e : Expr L-sig tt)
            → Σ (Expr L-sig tt) λ e′
              → Chain ListAtom (⟦ e ⟧L ρ) (⟦ e′ ⟧L ρ)
    greedyL ρ 0       e                                     = e , rfl
    greedyL ρ (suc n) (apply CAT (e ◂ apply NIL ε ◂ ε))     =
      let (e′ , rest) = greedyL ρ n e
      in  e′ , rule (++-idʳᴬ (⟦ e ⟧L ρ)) ∙ rest
    greedyL ρ (suc n) e                                     = e , rfl

    discovered₂ : {l : List A} → Chain ListAtom ((l ++ []) ++ []) l
    discovered₂ {l = l} =
      proj₂ (greedyL (λ _ → l) 10 ((var 0 ⊞ ⟨[]⟩) ⊞ ⟨[]⟩))

    key-example₂ : {l : List A} → (l ++ []) ++ [] ≡ l
    key-example₂ = reify interpretL discovered₂

    module _ {B : Set} (f : A → B) where

      interpSort : MSort → Set
      interpSort list-A = List A
      interpSort list-B = List B
      interpSort nat    = ℕ

      Env : Set
      Env = (s : MSort) → ℕ → interpSort s

      ⟦_⟧M : ∀ {s} → Expr M-sig s → Env → interpSort s
      ⟦ var {s = s} x          ⟧M ρ = ρ s x
      ⟦ apply length-A (e ◂ ε) ⟧M ρ = L.length (⟦ e ⟧M ρ)
      ⟦ apply length-B (e ◂ ε) ⟧M ρ = L.length (⟦ e ⟧M ρ)
      ⟦ apply map-f    (e ◂ ε) ⟧M ρ = L.map f (⟦ e ⟧M ρ)

      data MAtom : ℕ → ℕ → Set where
        length-map-atom
          : (l : List A) → MAtom (L.length (L.map f l)) (L.length l)

      interpretM : ∀ {a b} → MAtom a b → a ≡ b
      interpretM (length-map-atom l) = length-map f l

      greedyM : (ρ : Env) → ℕ → (e : Expr M-sig nat)
              → Σ (Expr M-sig nat) λ e′
                → Chain MAtom (⟦ e ⟧M ρ) (⟦ e′ ⟧M ρ)
      greedyM ρ 0       e                                           = e , rfl
      greedyM ρ (suc n) (apply length-B (apply map-f (e ◂ ε) ◂ ε)) =
        apply length-A (e ◂ ε) , rule (length-map-atom (⟦ e ⟧M ρ))
      greedyM ρ (suc n) e                                           = e , rfl

      discovered₃ : {l : List A}
                  → Chain MAtom (L.length (L.map f l)) (L.length l)
      discovered₃ {l = l} =
        proj₂ (greedyM env 10 (apply length-B (apply map-f (var 0 ◂ ε) ◂ ε)))
        where
          env : (s : MSort) → ℕ → interpSort s
          env list-A _ = l
          env list-B _ = []
          env nat    _ = 0

    key-example₃ : {l : List A} {f : A → B}
                 → L.length (L.map f l) ≡ L.length l
    key-example₃ {l = l} {f = f} =
      reify (interpretM f) (discovered₃ f {l = l})
