-- Examples for the `Tactic.Simp.Witness` proof-witness algebra.
--
-- Three key examples, all proved without macros or reflection:
--
--   key-example  : (n + 0) + 0 ≡ n            -- single-sorted, ℕ-sig
--   key-example₂ : (l ++ []) ++ [] ≡ l        -- single-sorted, L-sig
--   key-example₃ : length (map f l) ≡ length l -- multi-sorted, M-sig
--
-- All three use the same generic `greedy` from the core module; each
-- one supplies only its own signature, evaluator, atom set, and
-- one-step matcher.

{-# OPTIONS --safe #-}

module Tactic.Simp.Witness.Tests where

open import Data.List as L            using (List; []; _∷_; _++_)
open import Data.List.Properties      using (++-identityʳ; length-map)
open import Data.Maybe                using (Maybe; just; nothing)
open import Data.Nat                  using (ℕ; _+_)
open import Data.Nat.Properties       using (+-identityʳ)
open import Data.Product              using (_,_; Σ; proj₂)
open import Data.Unit                 using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Tactic.Simp.Witness

private variable
  A B : Set

private

  ----------------------------------------------------------------
  -- key-example: (n + 0) + 0 ≡ n  (via SimpSetup + runSimp)
  ----------------------------------------------------------------

  data NatOp : List ⊤ → ⊤ → Set where
    ZERO : NatOp [] tt
    ADD  : NatOp (tt ∷ tt ∷ []) tt

  ℕ-sig : Signature
  ℕ-sig = record { Sort = ⊤ ; Op = NatOp }

  ⟦_⟧ℕ : Expr ℕ-sig tt → (ℕ → ℕ) → ℕ
  ⟦ var x                    ⟧ℕ ρ = ρ x
  ⟦ apply ZERO ε             ⟧ℕ _ = 0
  ⟦ apply ADD  (e₁ ◂ e₂ ◂ ε) ⟧ℕ ρ = ⟦ e₁ ⟧ℕ ρ + ⟦ e₂ ⟧ℕ ρ

  data EqAtom : ℕ → ℕ → Set where
    +-idʳ : (m : ℕ) → EqAtom (m + 0) m

  interpret : ∀ {a b} → EqAtom a b → a ≡ b
  interpret (+-idʳ m) = +-identityʳ m

  matchℕ : Matcher ℕ-sig tt ⟦_⟧ℕ EqAtom
  matchℕ ρ (apply ADD (e ◂ apply ZERO ε ◂ ε)) =
    just (e , rule (+-idʳ (⟦ e ⟧ℕ ρ)))
  matchℕ _ _ = nothing

  ℕ-setup : SimpSetup
  ℕ-setup = record
    { eval      = ⟦_⟧ℕ
    ; interpret = interpret
    ; match     = matchℕ
    }

  ⟨0⟩ : Expr ℕ-sig tt
  ⟨0⟩ = apply ZERO ε

  infixl 6 _⊕_
  _⊕_ : Expr ℕ-sig tt → Expr ℕ-sig tt → Expr ℕ-sig tt
  e₁ ⊕ e₂ = apply ADD (e₁ ◂ e₂ ◂ ε)

  key-example : ∀ {n} → (n + 0) + 0 ≡ n
  key-example {n} =
    proj₂ (runSimp ℕ-setup (λ _ → n) 10 ((var 0 ⊕ ⟨0⟩) ⊕ ⟨0⟩))

  ----------------------------------------------------------------
  -- key-example₂: (l ++ []) ++ [] ≡ l  (generic greedy)
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
  -- key-example₃: length (map f l) ≡ length l  (multi-sorted,
  -- with parametric polymorphism)
  --
  -- A small "type-variable" alphabet `MTVar` indexes a *single*
  -- polymorphic `list` sort.  The `length` operation is polymorphic
  -- over `τ : MTVar`; `map-f` is the one operation that fixes a
  -- specific source/target type pair.
  ----------------------------------------------------------------

  data MTVar : Set where
    α β : MTVar

  data MSort : Set where
    list : MTVar → MSort
    nat  : MSort

  data MOp : List MSort → MSort → Set where
    length : ∀ {τ} → MOp (list τ ∷ []) nat
    map-f  :         MOp (list α ∷ []) (list β)

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

    matchL : Matcher L-sig tt ⟦_⟧L ListAtom
    matchL ρ (apply CAT (e ◂ apply NIL ε ◂ ε)) =
      just (e , rule (++-idʳᴬ (⟦ e ⟧L ρ)))
    matchL _ _ = nothing

    L-setup : SimpSetup
    L-setup = record
      { eval      = ⟦_⟧L
      ; interpret = interpretL
      ; match     = matchL
      }

    key-example₂ : {l : List A} → (l ++ []) ++ [] ≡ l
    key-example₂ {l = l} =
      proj₂ (runSimp L-setup (λ _ → l) 10 ((var 0 ⊞ ⟨[]⟩) ⊞ ⟨[]⟩))

    module _ {B : Set} (f : A → B) where

      -- The type-variable environment: `α ↦ A`, `β ↦ B`.
      interpTVar : MTVar → Set
      interpTVar α = A
      interpTVar β = B

      interpSort : MSort → Set
      interpSort (list τ) = List (interpTVar τ)
      interpSort nat      = ℕ

      Env : Set
      Env = (s : MSort) → ℕ → interpSort s

      ⟦_⟧M : ∀ {s} → Expr M-sig s → Env → interpSort s
      ⟦ var {s = s} x        ⟧M ρ = ρ s x
      ⟦ apply length (e ◂ ε) ⟧M ρ = L.length (⟦ e ⟧M ρ)
      ⟦ apply map-f  (e ◂ ε) ⟧M ρ = L.map f (⟦ e ⟧M ρ)

      data MAtom : ℕ → ℕ → Set where
        length-map-atom
          : (l : List A) → MAtom (L.length (L.map f l)) (L.length l)

      interpretM : ∀ {a b} → MAtom a b → a ≡ b
      interpretM (length-map-atom l) = length-map f l

      matchM : Matcher M-sig nat (⟦_⟧M {s = nat}) MAtom
      matchM ρ (apply length (apply map-f (e ◂ ε) ◂ ε)) =
        just (apply length (e ◂ ε) , rule (length-map-atom (⟦ e ⟧M ρ)))
      matchM _ _ = nothing

      M-setup : SimpSetup
      M-setup = record
        { eval      = ⟦_⟧M {s = nat}
        ; interpret = interpretM
        ; match     = matchM
        }

    key-example₃ : {l : List A} {f : A → B}
                 → L.length (L.map f l) ≡ L.length l
    key-example₃ {l = l} {f = f} =
      proj₂ (runSimp (M-setup f) env 10
                     (apply length (apply map-f (var 0 ◂ ε) ◂ ε)))
      where
        env : (s : MSort) → ℕ → interpSort f s
        env (list α) _ = l
        env (list β) _ = []
        env nat      _ = 0
