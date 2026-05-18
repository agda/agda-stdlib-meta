-- A standalone, abstract algebra of equality / relation proof witnesses.
--
-- This module defines the free groupoid-like 2-category over a set of
-- atoms.  The four generators are:
--
--     rfl   : identity 2-cell
--     trns  : sequential composition
--     invs  : inversion
--     rule  : embed an atomic 2-cell
--
-- The algebra is parameterised by a single type `A` — the type of
-- atomic witnesses.  Congruence descent is *not* a primitive; it is
-- encoded externally by relabelling atoms via `map`, e.g. by extending
-- a "position path" component.  This keeps the algebra minimal and
-- makes its universal property (the `fold` below) clean to state.
--
-- Nothing in this file references Agda's reflection types (Term, Name)
-- or uses the `macro` keyword.  All examples are constructed and
-- verified at the algebraic level by Agda's definitional equality.

{-# OPTIONS --safe #-}

module Tactic.Simp.Witness where

open import Data.Bool                using (Bool; true; false)
open import Data.List as L                using (List; []; _∷_; _++_)
open import Data.List.Properties     using (++-identityʳ; length-map)
open import Data.Nat                 using (ℕ; zero; suc; _+_; _*_)
open import Data.Nat.Properties
  using (+-identityʳ; +-identityˡ; *-identityʳ; *-identityˡ)
open import Data.Product             using (_×_; _,_; Σ; proj₂)
open import Data.Unit                using (⊤; tt)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; trans; sym)

private variable
  A B C : Set

----------------------------------------------------------------
-- 1. The free 2-category over a set of atoms
----------------------------------------------------------------

data Witness (A : Set) : Set where
  rfl  : Witness A
  trns : Witness A → Witness A → Witness A
  invs : Witness A → Witness A
  rule : A → Witness A

----------------------------------------------------------------
-- 2. Observation
----------------------------------------------------------------

isRfl : Witness A → Bool
isRfl rfl = true
isRfl _   = false

----------------------------------------------------------------
-- 3. Smart constructors
--
-- The smart versions collapse trivial cases (refl-elision, double-
-- inversion) at construction time.  These are the operations a search
-- frontend would actually use; the raw constructors are reserved for
-- pattern matching and for the universal property below.
----------------------------------------------------------------

-- Smart transitivity: refl on either side disappears.
infixr 5 _⨾_
_⨾_ : Witness A → Witness A → Witness A
rfl ⨾ w   = w
w   ⨾ rfl = w
w₁  ⨾ w₂  = trns w₁ w₂

-- Smart inversion: refl stays refl, double-inversion collapses.
[sym] : Witness A → Witness A
[sym] rfl      = rfl
[sym] (invs w) = w
[sym] w        = invs w

----------------------------------------------------------------
-- 4. Functoriality (atom relabelling)
--
-- `map f` is the homomorphism Witness A → Witness B over a function
-- f : A → B.  In a frontend, descending into argument i of a function
-- application would be `map (atom-shift i)` for an appropriate
-- atom-shift that records the path inside the atom.
----------------------------------------------------------------

map : (A → B) → Witness A → Witness B
map f rfl        = rfl
map f (trns x y) = trns (map f x) (map f y)
map f (invs x)   = invs (map f x)
map f (rule a)   = rule (f a)

----------------------------------------------------------------
-- 5. Universal property: fold into any 2-cell-shaped algebra
----------------------------------------------------------------

record Algebra (A X : Set) : Set where
  field
    rflᴬ  : X
    trnsᴬ : X → X → X
    invsᴬ : X → X
    ruleᴬ : A → X

fold : Algebra A B → Witness A → B
fold alg rfl        = Algebra.rflᴬ alg
fold alg (trns x y) = Algebra.trnsᴬ alg (fold alg x) (fold alg y)
fold alg (invs x)   = Algebra.invsᴬ alg (fold alg x)
fold alg (rule a)   = Algebra.ruleᴬ alg a

----------------------------------------------------------------
-- 6. Algebraic identities, verified by definitional equality
----------------------------------------------------------------

-- Smart trans: unit laws.
⨾-rfl-l : (w : Witness A) → rfl ⨾ w ≡ w
⨾-rfl-l _ = refl

⨾-rfl-r : (w : Witness A) → w ⨾ rfl ≡ w
⨾-rfl-r rfl        = refl
⨾-rfl-r (trns _ _) = refl
⨾-rfl-r (invs _)   = refl
⨾-rfl-r (rule _)   = refl

-- Smart sym: handling of rfl and double-invs.
[sym]-rfl : [sym] {A = A} rfl ≡ rfl
[sym]-rfl = refl

[sym]-invs : (w : Witness A) → [sym] (invs w) ≡ w
[sym]-invs _ = refl

-- map is functorial: preserves identity.
map-id : (w : Witness A) → map (λ x → x) w ≡ w
map-id rfl        = refl
map-id (trns x y) = cong₂ trns (map-id x) (map-id y)
map-id (invs x)   = cong  invs (map-id x)
map-id (rule _)   = refl

-- map is functorial: preserves composition.
map-∘ : (g : B → C) (f : A → B) (w : Witness A)
      → map (λ x → g (f x)) w ≡ map g (map f w)
map-∘ _ _ rfl        = refl
map-∘ g f (trns x y) = cong₂ trns (map-∘ g f x) (map-∘ g f y)
map-∘ g f (invs x)   = cong  invs (map-∘ g f x)
map-∘ _ _ (rule _)   = refl

----------------------------------------------------------------
-- 7. Concrete examples
--
-- Each example below is a closed term that Agda evaluates and verifies
-- against an expected normal form, with no macros and no reflection.
----------------------------------------------------------------

private

  -- A toy atom type: each atom names a hypothetical rule.
  data Demo : Set where
    +-id-r : Demo    -- represents the lemma  n + 0 = n
    *-id-r : Demo    -- represents the lemma  n * 1 = n

  -- Compose two rule applications.
  ex₁ : Witness Demo
  ex₁ = rule +-id-r ⨾ rule *-id-r

  -- Smart-trans elides rfl's:  rfl ⨾ w ⨾ rfl  reduces to  w.
  ex₂ : Witness Demo
  ex₂ = rfl ⨾ rule +-id-r ⨾ rfl

  ex₂-eq : ex₂ ≡ rule +-id-r
  ex₂-eq = refl

  -- Smart sym collapses double-inversion.
  ex₃ : Witness Demo
  ex₃ = [sym] (invs (rule +-id-r))

  ex₃-eq : ex₃ ≡ rule +-id-r
  ex₃-eq = refl

  -- map relabels atoms (one possible use:  cong descent via path-shift).
  swap : Demo → Demo
  swap +-id-r = *-id-r
  swap *-id-r = +-id-r

  ex₄ : map swap ex₁ ≡ trns (rule *-id-r) (rule +-id-r)
  ex₄ = refl

  -- Atoms can be path-augmented to encode cong descent abstractly.
  -- `descend i` shifts every atom's path by prepending `i`.
  PathAtom : Set
  PathAtom = Demo × List ℕ

  descend : ℕ → Witness PathAtom → Witness PathAtom
  descend i = map λ where (r , p) → (r , i ∷ p)

  ex₅ : Witness PathAtom
  ex₅ = rule (+-id-r , []) ⨾ rule (*-id-r , [])

  -- Descending the whole witness into position 0 prepends 0 to each path.
  ex₅-descend
    : descend 0 ex₅ ≡ trns (rule (+-id-r , 0 ∷ []))
                            (rule (*-id-r , 0 ∷ []))
  ex₅-descend = refl

  -- fold into ℕ: count atoms in a witness.
  countAlg : Algebra Demo ℕ
  countAlg = record
    { rflᴬ  = 0
    ; trnsᴬ = _+_
    ; invsᴬ = λ x → x
    ; ruleᴬ = λ _ → 1
    }

  ex₆-count : fold countAlg ex₁ ≡ 2
  ex₆-count = refl

  ex₇ : Witness Demo
  ex₇ = invs (rule +-id-r) ⨾ rule *-id-r ⨾ invs (invs (rule +-id-r))

  ex₇-count : fold countAlg ex₇ ≡ 3
  ex₇-count = refl

----------------------------------------------------------------
-- 8. Typed witnesses with dependent endpoints
--
-- The non-dependent algebra above cannot produce a typed `_≡_` proof
-- directly: `_≡_` is heterogeneous in its endpoints, but `Algebra A X`
-- has a uniform carrier `X : Set`.  The dependent companion `Chain R a
-- b` indexes the witness by its source and target so that endpoints
-- propagate through composition.
--
-- The four constructors of `Chain` mirror those of `Witness`; the
-- smart `_∙_`, `[inv]`, and `mapChain` are the typed analogues of
-- `_⨾_`, `[sym]`, and `map`.  `reify` is the dependent fold.
----------------------------------------------------------------

data Chain {S : Set} (R : S → S → Set) : S → S → Set where
  rfl  : ∀ {a}     → Chain R a a
  trns : ∀ {a b c} → Chain R a b → Chain R b c → Chain R a c
  invs : ∀ {a b}   → Chain R a b → Chain R b a
  rule : ∀ {a b}   → R a b → Chain R a b

-- Smart trans on chains (typed analogue of `_⨾_` on Witness).
infixr 5 _∙_
_∙_ : ∀ {S} {R : S → S → Set} {a b c : S}
    → Chain R a b → Chain R b c → Chain R a c
rfl ∙ w   = w
w   ∙ rfl = w
w₁  ∙ w₂  = trns w₁ w₂

-- Smart inversion on chains (typed analogue of `[sym]` on Witness).
[inv] : ∀ {S} {R : S → S → Set} {a b : S} → Chain R a b → Chain R b a
[inv] rfl      = rfl
[inv] (invs w) = w
[inv] w        = invs w

-- Functorial action: lift a chain through a function on the index set.
-- This is the typed analogue of `map` on Witness.  Cong descent is
-- exactly this: a function `f` on indices together with an atom lift
-- `R a b → R′ (f a) (f b)`.
mapChain : ∀ {S T : Set} {R : S → S → Set} {R′ : T → T → Set}
         → (f : S → T)
         → (∀ {a b} → R a b → R′ (f a) (f b))
         → ∀ {a b}
         → Chain R a b
         → Chain R′ (f a) (f b)
mapChain f φ rfl        = rfl
mapChain f φ (trns x y) = trns (mapChain f φ x) (mapChain f φ y)
mapChain f φ (invs x)   = invs (mapChain f φ x)
mapChain f φ (rule a)   = rule (φ a)

-- Reification: a dependent fold from `Chain` to `_≡_`.  Given an
-- atom-interpretation, fold a chain into a typed equality proof.
reify : ∀ {S} {R : S → S → Set} {a b : S}
      → (∀ {x y} → R x y → x ≡ y)
      → Chain R a b
      → a ≡ b
reify _ rfl        = refl
reify f (trns x y) = trans (reify f x) (reify f y)
reify f (invs x)   = sym (reify f x)
reify f (rule a)   = f a

-- Smart trans, unit laws.
∙-rfl-l : ∀ {S} {R : S → S → Set} {a b : S} (w : Chain R a b)
       → rfl ∙ w ≡ w
∙-rfl-l _ = refl

∙-rfl-r : ∀ {S} {R : S → S → Set} {a b : S} (w : Chain R a b)
       → w ∙ rfl ≡ w
∙-rfl-r rfl        = refl
∙-rfl-r (trns _ _) = refl
∙-rfl-r (invs _)   = refl
∙-rfl-r (rule _)   = refl

----------------------------------------------------------------
-- 9. Generic, multi-sorted expression language
--
-- To support multi-sorted setups (where terms of different "kinds"
-- coexist — e.g. `ℕ` and `List A` and `List B` in the same chain) the
-- symbolic expression language is parameterised by a *many-sorted*
-- signature.  A signature specifies a set of sorts, a set of operation
-- symbols, and for each symbol an input-sort list (its domain) and an
-- output sort.  Single-sorted setups are the special case `Sort = ⊤`.
----------------------------------------------------------------

-- Heterogeneous, sort-indexed argument vector.  In a single-sorted
-- setup the indices are all `tt`; in a multi-sorted setup each
-- position has its own required sort.
data Args {S : Set} (E : S → Set) : List S → Set where
  ε   : Args E []
  _◂_ : ∀ {s ss} → E s → Args E ss → Args E (s ∷ ss)
infixr 5 _◂_

-- A many-sorted algebraic signature.  Each operation symbol carries
-- both its input sorts (a `List Sort`) and its output sort in its
-- type, so `Op Σ args s` is the set of operations with input profile
-- `args` and codomain `s`.  This avoids a non-injective `codom`
-- function and lets dependent pattern matching on `Expr Σ s` proceed
-- cleanly even when multiple operations share the same codomain.
record Signature : Set₁ where
  field
    Sort : Set
    Op   : List Sort → Sort → Set
open Signature public

-- The generic expression language: sort-indexed variables and
-- operation applications.  `Expr Σ s` is a term of sort `s`.
data Expr (Σ : Signature) : Sort Σ → Set where
  var   : ∀ {s} → ℕ → Expr Σ s
  apply : ∀ {args s} → Op Σ args s → Args (Expr Σ) args → Expr Σ s

----------------------------------------------------------------
-- 10. Reasoning chains and greedy discovery
--
-- Three example signatures share the generic `Expr` and the same
-- `Chain` / `reify` machinery from §8:
--
--   §10a. `ℕ-sig` — single-sorted (`Sort = ⊤`):  every term is a `ℕ`.
--   §10b. `L-sig` — single-sorted:               every term is a `List A`.
--   §10c. `M-sig` — multi-sorted:                `List A`, `List B`, `ℕ`
--                                                coexist in one chain.
----------------------------------------------------------------

private

  ----------------------------------------------------------------
  -- 10a. Reasoning over `ℕ`  (single-sorted, `Sort = ⊤`)
  ----------------------------------------------------------------

  -- `NatOp args s` is the set of ℕ-operations with arity-profile
  -- `args` and codomain `s`; here `s` is always `tt` (single-sorted).
  data NatOp : List ⊤ → ⊤ → Set where
    ZERO ONE : NatOp [] tt
    SUC      : NatOp (tt ∷ []) tt
    ADD MUL  : NatOp (tt ∷ tt ∷ []) tt

  ℕ-sig : Signature
  ℕ-sig = record { Sort = ⊤ ; Op = NatOp }

  -- Derived constants and operators.
  ⟨0⟩ : Expr ℕ-sig tt
  ⟨0⟩ = apply ZERO ε

  ⟨1⟩ : Expr ℕ-sig tt
  ⟨1⟩ = apply ONE ε

  ⟨suc⟩ : Expr ℕ-sig tt → Expr ℕ-sig tt
  ⟨suc⟩ e = apply SUC (e ◂ ε)

  infixl 6 _⊕_
  infixl 7 _⊗_

  _⊕_ : Expr ℕ-sig tt → Expr ℕ-sig tt → Expr ℕ-sig tt
  e₁ ⊕ e₂ = apply ADD (e₁ ◂ e₂ ◂ ε)

  _⊗_ : Expr ℕ-sig tt → Expr ℕ-sig tt → Expr ℕ-sig tt
  e₁ ⊗ e₂ = apply MUL (e₁ ◂ e₂ ◂ ε)

  -- Evaluator for `Expr ℕ-sig tt`.
  ⟦_⟧ : Expr ℕ-sig tt → (ℕ → ℕ) → ℕ
  ⟦ var x                    ⟧ ρ = ρ x
  ⟦ apply ZERO ε             ⟧ _ = 0
  ⟦ apply ONE  ε             ⟧ _ = 1
  ⟦ apply SUC  (e ◂ ε)       ⟧ ρ = suc (⟦ e ⟧ ρ)
  ⟦ apply ADD  (e₁ ◂ e₂ ◂ ε) ⟧ ρ = ⟦ e₁ ⟧ ρ + ⟦ e₂ ⟧ ρ
  ⟦ apply MUL  (e₁ ◂ e₂ ◂ ε) ⟧ ρ = ⟦ e₁ ⟧ ρ * ⟦ e₂ ⟧ ρ

  -- Atom set for ℕ.
  data EqAtom : ℕ → ℕ → Set where
    +-idʳ : (m : ℕ)   → EqAtom (m + 0) m
    +-idˡ : (m : ℕ)   → EqAtom (0 + m) m
    *-idʳ : (m : ℕ)   → EqAtom (m * 1) m
    *-idˡ : (m : ℕ)   → EqAtom (1 * m) m
    inSuc : ∀ {a b} → EqAtom a b → EqAtom (suc a) (suc b)

  interpret : ∀ {a b} → EqAtom a b → a ≡ b
  interpret (+-idʳ m) = +-identityʳ m
  interpret (+-idˡ m) = +-identityˡ m
  interpret (*-idʳ m) = *-identityʳ m
  interpret (*-idˡ m) = *-identityˡ m
  interpret (inSuc a) = cong suc (interpret a)

  -- Hand-built chains.
  keyChain : ∀ {n} → Chain EqAtom ((n + 0) + 0) n
  keyChain {n} = rule (+-idʳ (n + 0)) ∙ rule (+-idʳ n)

  key-example : ∀ {n} → (n + 0) + 0 ≡ n
  key-example = reify interpret keyChain

  longer-example : ∀ {n} → ((n + 0) + 0) + 0 ≡ n
  longer-example {n} =
    reify interpret
      ( rule (+-idʳ ((n + 0) + 0))
      ∙ rule (+-idʳ (n + 0))
      ∙ rule (+-idʳ n))

  mixed-example : ∀ {n} → (0 + n) + 0 ≡ n
  mixed-example {n} =
    reify interpret (rule (+-idʳ (0 + n)) ∙ rule (+-idˡ n))

  multi-example : ∀ {n} → (n + 0) * 1 ≡ n
  multi-example {n} =
    reify interpret (rule (*-idʳ (n + 0)) ∙ rule (+-idʳ n))

  reverse-example : ∀ {n} → n ≡ n + 0
  reverse-example {n} = reify interpret ([inv] (rule (+-idʳ n)))

  detour-example : ∀ {n} → n + 0 ≡ 0 + n
  detour-example {n} =
    reify interpret (rule (+-idʳ n) ∙ [inv] (rule (+-idˡ n)))

  cong-example : ∀ {n} → suc (n + 0) ≡ suc n
  cong-example {n} = reify interpret (rule (inSuc (+-idʳ n)))

  via-functor : ∀ {n} → suc ((n + 0) + 0) ≡ suc n
  via-functor = reify interpret (mapChain suc inSuc keyChain)

  loop-example : ∀ {n} → n + 0 ≡ n + 0
  loop-example {n} =
    reify interpret (rule (+-idʳ n) ∙ [inv] (rule (+-idʳ n)))

  -- Greedy discovery over `Expr ℕ-sig tt`.
  greedy : (ρ : ℕ → ℕ) → ℕ → (e : Expr ℕ-sig tt)
         → Σ (Expr ℕ-sig tt) λ e′ → Chain EqAtom (⟦ e ⟧ ρ) (⟦ e′ ⟧ ρ)
  greedy ρ 0       e                                       = e , rfl
  greedy ρ (suc n) (apply ADD (e ◂ apply ZERO ε ◂ ε))      =
    let (e′ , rest) = greedy ρ n e
    in  e′ , rule (+-idʳ (⟦ e ⟧ ρ)) ∙ rest
  greedy ρ (suc n) (apply ADD (apply ZERO ε ◂ e ◂ ε))      =
    let (e′ , rest) = greedy ρ n e
    in  e′ , rule (+-idˡ (⟦ e ⟧ ρ)) ∙ rest
  greedy ρ (suc n) (apply MUL (e ◂ apply ONE  ε ◂ ε))      =
    let (e′ , rest) = greedy ρ n e
    in  e′ , rule (*-idʳ (⟦ e ⟧ ρ)) ∙ rest
  greedy ρ (suc n) (apply MUL (apply ONE  ε ◂ e ◂ ε))      =
    let (e′ , rest) = greedy ρ n e
    in  e′ , rule (*-idˡ (⟦ e ⟧ ρ)) ∙ rest
  greedy ρ (suc n) (apply SUC (e ◂ ε))                     =
    let (e′ , rest) = greedy ρ n e
    in  apply SUC (e′ ◂ ε) , mapChain suc inSuc rest
  greedy ρ (suc n) e                                       = e , rfl

  discovered : ∀ {n} → Chain EqAtom ((n + 0) + 0) n
  discovered {n} = proj₂ (greedy (λ _ → n) 10 ((var 0 ⊕ ⟨0⟩) ⊕ ⟨0⟩))

  discovered-matches-key : ∀ {n} → discovered {n} ≡ keyChain {n}
  discovered-matches-key = refl

  discovered-example : ∀ {n} → (n + 0) + 0 ≡ n
  discovered-example = reify interpret discovered

  discovered-longer : ∀ {n} → ((n + 0) + 0) + 0 ≡ n
  discovered-longer {n} =
    reify interpret
      (proj₂ (greedy (λ _ → n) 10 (((var 0 ⊕ ⟨0⟩) ⊕ ⟨0⟩) ⊕ ⟨0⟩)))

  discovered-multi : ∀ {n} → (n + 0) * 1 ≡ n
  discovered-multi {n} =
    reify interpret
      (proj₂ (greedy (λ _ → n) 10 ((var 0 ⊕ ⟨0⟩) ⊗ ⟨1⟩)))

  discovered-cong : ∀ {n} → suc ((n + 0) + 0) ≡ suc n
  discovered-cong {n} =
    reify interpret
      (proj₂ (greedy (λ _ → n) 10 (⟨suc⟩ ((var 0 ⊕ ⟨0⟩) ⊕ ⟨0⟩))))

  ----------------------------------------------------------------
  -- 10b. Reasoning over `List A`  (single-sorted, `Sort = ⊤`)
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
  -- 10c. Multi-sorted signature for the `length-map` example.
  --
  -- Three sorts coexist:  list-A, list-B, nat.  `map-f` crosses
  -- from `list-A` to `list-B`; `length-A` and `length-B` are
  -- distinct operations from those sorts back to `nat`.
  -- This is the signature; its interpretation depends on a
  -- specific `f : A → B` and so lives inside a parameterised
  -- module below.
  ----------------------------------------------------------------

  data MSort : Set where
    list-A list-B nat : MSort

  -- Each operation carries its arity profile *and* its codomain in
  -- its type.  Pattern matching `apply o args` against `Expr M-sig
  -- nat` then only succeeds for `o : MOp _ nat`, i.e. `length-A` or
  -- `length-B` — no codom-inversion required.
  data MOp : List MSort → MSort → Set where
    length-A : MOp (list-A ∷ []) nat
    length-B : MOp (list-B ∷ []) nat
    map-f    : MOp (list-A ∷ []) list-B

  M-sig : Signature
  M-sig = record { Sort = MSort ; Op = MOp }

  -- All instance-level definitions (those that mention an actual
  -- element type) live inside `module _ {A : Set}`.  This pins the
  -- universe level to `Set₀` and keeps `A` from being threaded
  -- through every signature.
  module _ {A : Set} where

    ⟦_⟧L : Expr L-sig tt → (ℕ → List A) → List A
    ⟦ var x                    ⟧L ρ = ρ x
    ⟦ apply NIL ε              ⟧L _ = []
    ⟦ apply CAT (e₁ ◂ e₂ ◂ ε)  ⟧L ρ = ⟦ e₁ ⟧L ρ ++ ⟦ e₂ ⟧L ρ

    data ListAtom : List A → List A → Set where
      ++-idʳᴬ : (xs : List A) → ListAtom (xs ++ []) xs

    interpretL : {xs ys : List A} → ListAtom xs ys → xs ≡ ys
    interpretL (++-idʳᴬ xs) = ++-identityʳ xs

    -- Hand-built chain solving the user's `key-example₂`.
    keyChain₂ : {l : List A} → Chain ListAtom ((l ++ []) ++ []) l
    keyChain₂ {l = l} = rule (++-idʳᴬ (l ++ [])) ∙ rule (++-idʳᴬ l)

    -- Greedy discovery over `Expr L-sig tt`.
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

    discovered₂-matches-key₂
      : {l : List A} → discovered₂ {l = l} ≡ keyChain₂ {l = l}
    discovered₂-matches-key₂ = refl

    key-example₂ : {l : List A} → (l ++ []) ++ [] ≡ l
    key-example₂ = reify interpretL discovered₂

    ----------------------------------------------------------------
    -- Inner module: multi-sorted reasoning depends on a specific
    -- `f : A → B`, so its interpretation, atom set, and greedy live
    -- in a `module _ {B} (f : A → B)` block.
    ----------------------------------------------------------------

    module _ {B : Set} (f : A → B) where

      interpSort : MSort → Set
      interpSort list-A = List A
      interpSort list-B = List B
      interpSort nat    = ℕ

      Env : Set
      Env = (s : MSort) → ℕ → interpSort s

      -- Sort-indexed evaluator.  `var {s = s} x` captures the implicit
      -- sort so we can dispatch the environment per sort.
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

      keyChain₃ : {l : List A}
                → Chain MAtom (L.length (L.map f l)) (L.length l)
      keyChain₃ {l = l} = rule (length-map-atom l)

      -- Greedy over `Expr M-sig nat`.  Only one pattern fires:
      -- `length (map f _)` rewrites to `length _`.  Dependent
      -- pattern matching works directly now that `MOp` carries the
      -- codomain in its type.
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

      discovered₃-matches-key₃
        : {l : List A} → discovered₃ {l = l} ≡ keyChain₃ {l = l}
      discovered₃-matches-key₃ = refl

    -- The user-supplied target.  `f` is per-function implicit; the
    -- proof delegates into the `(f)` module above.
    key-example₃ : {l : List A} {f : A → B}
                 → L.length (L.map f l) ≡ L.length l
    key-example₃ {l = l} {f = f} =
      reify (interpretM f) (discovered₃ f {l = l})
