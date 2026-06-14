-- Extensive test suite and edge-case catalogue for the reflective
-- simplifier (`simp!` / `simpD!` / `simpH!` / `simpRel!`).
--
-- Sections:
--   A. goal shapes          B. rule shapes
--   C. polymorphic rules    D. ordered rewriting
--   E. local hypotheses     F. dictionaries
--   G. relation goals       H. universe levels
--   I. longer rewrites
--
-- Tests that document known limitations are kept commented out, each
-- with the observed behaviour and the reason.

{-# OPTIONS --safe #-}

module Tactic.Simp.Reflective.Tests where

open import Data.Bool using (Bool; true; false; if_then_else_; _∧_)
open import Data.Bool.Properties using (∧-comm)
open import Data.List using (List; []; _∷_; _++_; map; length; reverse)
open import Data.List.Properties
  using (++-identityʳ; map-id; reverse-involutive; length-map)
open import Data.List.Relation.Binary.Permutation.Propositional
  using (_↭_; ↭-refl; ↭-trans)
import Data.List.Relation.Binary.Permutation.Propositional.Properties as ↭Prop
import Algebra.Bundles as AlgB
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _⊔_; _⊓_; _≤_; _≥_; _<_)
open import Data.Nat.Properties
  using ( +-identityʳ; +-identityˡ; *-identityʳ; *-zeroʳ; +-assoc; +-comm
        ; n∸n≡0; ⊔-comm; ≤-refl; ≤-trans; n≤1+n; m≤n⇒m⊓n≡m)
open import Data.Vec using (Vec)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Function using (id; _∘_)
open import Relation.Binary.PropositionalEquality
-- side-condition decidability instances for conditional rules (Section K):
-- brings `_≤_`'s `Class.Decidable._⁇` instance into scope.
open import Class.Decidable

open import Tactic.Defaults
open import Tactic.Simp.Reflective

private variable
  x y : ℕ

----------------------------------------------------------------
-- A. Goal shapes
----------------------------------------------------------------

-- trivial goals at assorted sorts (no rules)
gA₁ : ∀ {b : Bool} → b ≡ b
gA₁ = simp! []

gA₂ : ∀ {f : ℕ → ℕ} → f ≡ f          -- function-typed goal sort
gA₂ = simp! []

gA₃ : tt ≡ tt
gA₃ = simp! []

-- already-normal goal with rules present (nothing to do)
gA₄ : ∀ {x y : ℕ} → x + y ≡ x + y
gA₄ = simp! (quote +-identityʳ ∷ [])

-- numeral literals
gA₅ : 5 + 0 ≡ 5
gA₅ = simp! (quote +-identityʳ ∷ [])

gA₆ : ∀ {x : ℕ} → (3 + x) + 0 ≡ 3 + x
gA₆ = simp! (quote +-identityʳ ∷ [])

-- goal under an instance binder
gA₇ : ∀ ⦃ x : ℕ ⦄ → x + 0 ≡ x
gA₇ = simp! (quote +-identityʳ ∷ [])

-- record projections as operations
gA₈ : ∀ (p : ℕ × ℕ) → proj₁ p + 0 ≡ proj₁ p
gA₈ p = simp! (quote +-identityʳ ∷ [])

-- projection applied to a constructor (definitional redex left alone)
gA₉ : ∀ (a b : ℕ) → proj₁ (a , b) + 0 ≡ proj₁ (a , b)
gA₉ a b = simp! (quote +-identityʳ ∷ [])

-- rewriting inside an if_then_else_ branch
gA₁₀ : ∀ (b : Bool) (x : ℕ) → (if b then x + 0 else x) ≡ (if b then x else x)
gA₁₀ b x = simp! (quote +-identityʳ ∷ [])

-- a lambda subterm is a stable opaque atom
gA₁₁ : ∀ (l : List ℕ) → map (λ n → n + 1) (l ++ []) ≡ map (λ n → n + 1) l
gA₁₁ l = simp! (quote ++-identityʳ ∷ [])

-- a partial application decomposes as a function-sorted operation
gA₁₂ : ∀ (x : ℕ) (l : List ℕ) → map (x +_) (l ++ []) ≡ map (x +_) l
gA₁₂ x l = simp! (quote ++-identityʳ ∷ [])

-- several rules, several positions, one call
gA₁₃ : ∀ {a b c : ℕ} →
       ((a + 0) * 1 + (0 + b)) + (c * 1 + 0) ≡ (a + b) + c
gA₁₃ = simp! (quote +-identityʳ ∷ quote +-identityˡ ∷ quote *-identityʳ ∷ [])

-- `zero` written as a constructor vs the literal in the rule's type
gA₁₄ : ∀ {x : ℕ} → x + zero ≡ x
gA₁₄ = simp! (quote +-identityʳ ∷ [])

-- definitionally-true goal the engine cannot see syntactically
-- (closed by the refl fallback on the failure path)
gA₁₅ : 2 + 3 ≡ 5
gA₁₅ = simp! []

-- rewriting first, then a definitional remainder: the engine rewrites
-- away the `+ 0`, and the fallback closes the residual
-- `suc (suc x) ≡ 2 + x` definitionally
gA₁₆ : ∀ {x : ℕ} → suc (suc x) + 0 ≡ 2 + x
gA₁₆ = simp! (quote +-identityʳ ∷ [])

-- both a rewrite and a definitional step on a separate stuck subterm
gA₁₇ : ∀ {x : ℕ} → (x + 0) + (2 + 3) ≡ x + 5
gA₁₇ = simp! (quote +-identityʳ ∷ [])

----------------------------------------------------------------
-- B. Rule shapes
----------------------------------------------------------------

-- ground rule about a 0-ary definition
const5 : ℕ
const5 = 5

c5-eq : const5 ≡ 5
c5-eq = refl

gB₁ : const5 + 0 ≡ 5
gB₁ = simp! (quote c5-eq ∷ quote +-identityʳ ∷ [])

-- hidden pattern binder
hid-idʳ : ∀ {n : ℕ} → n + 0 ≡ n
hid-idʳ {n} = +-identityʳ n

gB₂ : ∀ {x : ℕ} → x + 0 ≡ x
gB₂ = simp! (quote hid-idʳ ∷ [])

-- instance pattern binder
inst-idʳ : ∀ ⦃ n : ℕ ⦄ → n + 0 ≡ n
inst-idʳ ⦃ n ⦄ = +-identityʳ n

gB₃ : ∀ {x : ℕ} → x + 0 ≡ x
gB₃ = simp! (quote inst-idʳ ∷ [])

-- non-linear lhs (n occurs twice; binding consistency checked)
gB₄ : ∀ (x : ℕ) → (x + 1) ∸ (x + 1) ≡ 0
gB₄ x = simp! (quote n∸n≡0 ∷ [])

-- duplicate rule entries are harmless
gB₅ : ∀ {x : ℕ} → x + 0 ≡ x
gB₅ = simp! (quote +-identityʳ ∷ quote +-identityʳ ∷ [])

-- ≗-stated rule (map-id : map id ≗ id), composed with an id-unfolding
-- rule whose instantiation (at List ℕ) is only discoverable from
-- map-id's rhs-instance — exercises ≗ unfolding AND candidate enrichment
id-def : ∀ {a} {A : Set a} (x : A) → id x ≡ x
id-def x = refl

gB₆ : ∀ (l : List ℕ) → map id (l ++ []) ≡ l
gB₆ l = simp! (quote map-id ∷ quote ++-identityʳ ∷ quote id-def ∷ [])

-- LIMITATION (documented): a rule whose rhs mentions a variable absent
-- from the lhs leaves an unresolvable pattern variable in the rewritten
-- expression; the call fails cleanly ("failed to close the goal").
--   zero-absorb : ∀ x y → x * 0 ≡ 0 * y
--   gB₇ : ∀ {x : ℕ} → x * 0 ≡ 0 * 3
--   gB₇ = simp! (quote zero-absorb ∷ [])

-- LIMITATION (documented): an expanding rule (reversed identity,
-- `∀ n → n ≡ n + 0`) has a bare-variable lhs that matches everything;
-- rewriting expands until fuel runs out, then fails cleanly with
-- "(normal form with N nodes omitted — diverging rule set?)".
-- (Amusingly, a SYMMETRIC goal like `x ≡ x` still closes with such a
-- rule: both sides expand to the same 100-step form.)  Expanding rule
-- sets are the user's responsibility, as in Lean/Isabelle.
--   idʳ-rev : ∀ (n : ℕ) → n ≡ n + 0
--   gB₈ : ∀ {x : ℕ} → x + 0 ≡ x
--   gB₈ = simp! (quote idʳ-rev ∷ [])

----------------------------------------------------------------
-- C. Polymorphic rules
----------------------------------------------------------------

-- nested type instantiation (A := List ℕ)
gC₁ : ∀ (ll : List (List ℕ)) → ll ++ [] ≡ ll
gC₁ ll = simp! (quote ++-identityʳ ∷ [])

-- two instantiations of the same rule in one goal
gC₂ : ∀ (l : List ℕ) (ll : List (List ℕ)) →
      length (ll ++ []) + length (l ++ []) ≡ length ll + length l
gC₂ l ll = simp! (quote ++-identityʳ ∷ [])

-- two polymorphic rules chained
gC₃ : ∀ (l : List ℕ) → reverse (reverse (l ++ [])) ≡ l
gC₃ l = simp! (quote reverse-involutive ∷ quote ++-identityʳ ∷ [])

-- Set-valued element type (the goal lives in Set₁)
gC₄ : ∀ (l : List Set) → l ++ [] ≡ l
gC₄ l = simp! (quote ++-identityʳ ∷ [])

----------------------------------------------------------------
-- D. Ordered rewriting
----------------------------------------------------------------

-- commutativity at other types
gD₁ : ∀ (a b : Bool) → a ∧ b ≡ b ∧ a
gD₁ a b = simp! (quote ∧-comm ∷ [])

gD₂ : ∀ (a b : ℕ) → a ⊔ b ≡ b ⊔ a
gD₂ a b = simp! (quote ⊔-comm ∷ [])

-- commutativity interacting with an ordinary rule
gD₃ : ∀ {x y : ℕ} → (x + 0) + y ≡ y + x
gD₃ = simp! (quote +-comm ∷ quote +-identityʳ ∷ [])

----------------------------------------------------------------
-- E. Local hypotheses
----------------------------------------------------------------

-- hypothesis that is an application (a projection)
gE₁ : ∀ {x : ℕ} (p : (x ≡ 0) × ⊤) → x + x ≡ 0
gE₁ p = simpH! (quote +-identityʳ ∷ []) (proj₁ p ∷ [])

-- several hypotheses at once: NB hypotheses with different statements
-- must be passed as a (heterogeneous) pair — a list literal would have
-- to elaborate at a single element type, since macro Term-arguments
-- are elaborated like quoteTerm
gE₂ : ∀ {x y : ℕ} → x ≡ 5 → y ≡ 5 → x + 0 ≡ y
gE₂ hx hy = simpH! (quote +-identityʳ ∷ []) (hx , hy)

-- hypothesis bound as a module parameter
module HypModule (h : ∀ (n : ℕ) → n + 0 ≡ n) where

  gE₃ : ∀ {x : ℕ} → x + 0 ≡ x
  gE₃ = simpH! [] (h ∷ [])

-- a homogeneous list literal also works when the statements coincide
gE₄ : ∀ {x : ℕ} (h₁ h₂ : x ≡ 5) → x + x ≡ 5 + 5
gE₄ h₁ h₂ = simpH! [] (h₁ ∷ h₂ ∷ [])

-- LIMITATION (documented): `simpH!` cannot rewrite WITH a hypothesis
-- whose statement is polymorphic (parameter binders are rejected with
-- a clear error; use a monomorphic copy).

----------------------------------------------------------------
-- F. Dictionaries
----------------------------------------------------------------

data EmptyDict : Set where

gF₁ : ∀ {x : ℕ} → x ≡ x
gF₁ = simpD! EmptyDict

data ListDict : Set where

instance
  ld₁ : Simp ListDict
  ld₁ = mkSimp (quote ++-identityʳ)

-- polymorphic rule through a dictionary
gF₂ : ∀ (l : List ℕ) → l ++ [] ≡ l
gF₂ l = simpD! ListDict

----------------------------------------------------------------
-- G. Relation goals (non-equality relations)
----------------------------------------------------------------

≤-info : RelInfo
≤-info = mkRelInfo (quote ≤-trans) (quote ≤-refl)

↭-info : RelInfo
↭-info = mkRelInfo (quote ↭-trans) (quote ↭-refl)

-- rewriting under a cons inside a permutation goal
gG₁ : ∀ (x : ℕ) (xs : List ℕ) → x ∷ (xs ++ []) ↭ x ∷ xs
gG₁ x xs = simpRel! (quote ++-identityʳ ∷ []) [] ↭-info

-- both sides ≡-normalise, then two ~-steps
gG₂ : ∀ {n : ℕ} → n + 0 ≤ 2 + (n + 0)
gG₂ = simpRel! (quote +-identityʳ ∷ []) (quote n≤1+n ∷ []) ≤-info

-- refl-close after lhs-only normalisation
gG₃ : ∀ {n : ℕ} → n + 0 ≤ n
gG₃ = simpRel! (quote +-identityʳ ∷ []) [] ≤-info

-- rhs-side-only normalisation
gG₄ : ∀ {n : ℕ} → n ≤ n + 0
gG₄ = simpRel! (quote +-identityʳ ∷ []) [] ≤-info

-- mixed binders, two ≡-rules
gG₅ : ∀ (m : ℕ) {n : ℕ} → (m + 0) + (0 + n) ≤ m + n
gG₅ m = simpRel! (quote +-identityˡ ∷ quote +-identityʳ ∷ []) [] ≤-info

-- three chained ~-steps
gG₆ : ∀ {n : ℕ} → n + 0 ≤ 3 + n
gG₆ = simpRel! (quote +-identityʳ ∷ []) (quote n≤1+n ∷ []) ≤-info

-- literals
gG₇ : 5 + 0 ≤ 5
gG₇ = simpRel! (quote +-identityʳ ∷ []) [] ≤-info

-- definitional gap closed by the reflexivity emission's unification
gG₈ : 2 + 3 ≤ 5
gG₈ = simpRel! [] [] ≤-info

-- alias relations: whnf of the goal unfolds them to their ≤ core
gG₉ : ∀ {n : ℕ} → n ≥ n + 0
gG₉ = simpRel! (quote +-identityʳ ∷ []) [] ≤-info

gG₁₀ : ∀ {n : ℕ} → n + 0 < 1 + n
gG₁₀ = simpRel! (quote +-identityʳ ∷ []) [] ≤-info

-- deeper rewriting inside a permutation goal (two conses above)
gG₁₁ : ∀ (x y : ℕ) (xs : List ℕ) → x ∷ y ∷ (xs ++ []) ↭ x ∷ y ∷ xs
gG₁₁ x y xs = simpRel! (quote ++-identityʳ ∷ []) [] ↭-info

-- ≡-normalisation, then a polymorphic ~-rule (++-comm) instantiated
-- by the match-all-binders chaining
gG₁₂ : ∀ (xs ys : List ℕ) → (xs ++ []) ++ ys ↭ ys ++ xs
gG₁₂ xs ys = simpRel! (quote ++-identityʳ ∷ []) (quote ↭Prop.++-comm ∷ []) ↭-info

-- ordered rewriting (permutative +-comm) inside a relation goal
gG₁₃ : ∀ {x y : ℕ} → x + y ≤ (y + x) + 0
gG₁₃ = simpRel! (quote +-comm ∷ quote +-identityʳ ∷ []) [] ≤-info

-- LIMITATION (documented, root cause established 2026-06-12): relations
-- DEFINED as functions (e.g. `_⊆_` = ∀ {x} → x ∈ xs → x ∈ ys) are not
-- supported.  `inferType` on the goal hole returns the relation ALREADY
-- UNFOLDED to its Π-definition, so the goal is seen as a binder to
-- strip (descending into the membership arrow).  There is no way to
-- recover the folded `_⊆_` from the hole type, and blocking that
-- relation's reduction during `inferType` (via `dontReduce`) breaks
-- `inferType`'s own elaboration (de Bruijn / level errors) on other
-- goals.  A fix needs a different mechanism (a wrapper relation, or an
-- as-written goal type from elsewhere).
--   gG₁₄ : ∀ (xs : List ℕ) → xs ++ [] ⊆ xs
--   gG₁₄ xs = simpRel! (quote ++-identityʳ ∷ []) []
--                      (mkRelInfo (quote ⊆-trans) (quote ⊆-refl))

-- simpRelD!: ≡-rule and ~-rule lists from instance dictionaries.
data BagEqRules  : Set where    -- ≡-rules
data BagRelRules : Set where    -- ~-rules
data NoRules     : Set where    -- empty dictionary

instance
  ber₁ : Simp BagEqRules
  ber₁ = mkSimp (quote ++-identityʳ)
  brr₁ : Simp BagRelRules
  brr₁ = mkSimp (quote ↭Prop.++-comm)

-- Option C through dictionaries (≡-normalise the LHS, ↭-refl closes)
gGD₁ : ∀ (xs ys : List ℕ) → (xs ++ []) ++ ys ↭ xs ++ ys
gGD₁ xs ys = simpRelD! BagEqRules NoRules ↭-info

-- Option B through dictionaries (a single ++-comm ~-step; no ≡-rules)
gGD₂ : ∀ (xs ys : List ℕ) → xs ++ ys ↭ ys ++ xs
gGD₂ xs ys = simpRelD! NoRules BagRelRules ↭-info

-- simpRelH!: a local ≡-hypothesis feeds the ≡-engine of a relation goal.
-- `n + 0 ≤ m` with `h : n ≡ m`: engine rewrites n+0→n (++... +-identityʳ)
-- then n→m (via h), leaving `m ≤ m`, closed by ≤-refl.
gGH₁ : ∀ {n m : ℕ} → n ≡ m → n + 0 ≤ m
gGH₁ {n} {m} h = simpRelH! (quote +-identityʳ ∷ []) [] (h ∷ []) ≤-info

-- two ≡-hypotheses (heterogeneous → passed as a pair) on a ≤ goal
gGH₂ : ∀ {a b c : ℕ} → a ≡ b → c ≡ b → a + c ≤ b + b
gGH₂ ha hc = simpRelH! [] [] (ha , hc) ≤-info

-- Mixed universe levels in a relation goal: carrier ℕ (level 0) with a
-- `List A` subterm (level a).  The lower sort is Lift-ed and the proof
-- lower-wrapped back to the bare carrier.
gGL₁ : ∀ {a} {A : Set a} (xs : List A) → length (xs ++ []) ≤ length xs
gGL₁ xs = simpRel! (quote ++-identityʳ ∷ []) [] ≤-info

-- both sides need normalisation, still mixed-level
gGL₂ : ∀ {a} {A : Set a} (xs : List A) → length (xs ++ []) ≤ length (xs ++ [])
gGL₂ xs = simpRel! (quote ++-identityʳ ∷ []) [] ≤-info

-- Abstract bundle relations: `simpRel!` over an arbitrary `Monoid M`'s
-- `_≈_`, with `_∙_`/`ε` recognised as bundle operations (their leading
-- bundle argument `M` is dropped during reification, so `M` — at a
-- higher universe level than the carrier — never becomes a sort).
module MonoidTests {c ℓ} (M : AlgB.Monoid c ℓ) where
  open AlgB.Monoid M renaming (refl to ≈refl; trans to ≈trans)

  private
    ∙-idʳ : ∀ x → x ∙ ε ≈ x
    ∙-idʳ = identityʳ
    ∙-idˡ : ∀ x → ε ∙ x ≈ x
    ∙-idˡ = identityˡ
    ∙-assoc : ∀ x y z → (x ∙ y) ∙ z ≈ x ∙ (y ∙ z)
    ∙-assoc = assoc
    ≈refl′ : ∀ {x} → x ≈ x
    ≈refl′ = ≈refl
    ≈trans′ : ∀ {x y z} → x ≈ y → y ≈ z → x ≈ z
    ≈trans′ = ≈trans

  M-info : RelInfo
  M-info = mkRelInfo (quote ≈trans′) (quote ≈refl′)

  -- single ≈-step
  tMon₁ : ∀ x → x ∙ ε ≈ x
  tMon₁ x = simpRel! [] (quote ∙-idʳ ∷ []) M-info

  -- two nested identity steps
  tMon₂ : ∀ x → (x ∙ ε) ∙ ε ≈ x
  tMon₂ x = simpRel! [] (quote ∙-idʳ ∷ []) M-info

  -- both identities
  tMon₃ : ∀ x → ε ∙ (x ∙ ε) ≈ x
  tMon₃ x = simpRel! [] (quote ∙-idʳ ∷ quote ∙-idˡ ∷ []) M-info

  -- associativity + identity (mirrors old Tactic.Simp testMonoid₄)
  tMon₄ : ∀ x y z → ((x ∙ y) ∙ z) ∙ ε ≈ x ∙ (y ∙ z)
  tMon₄ x y z = simpRel! [] (quote ∙-idʳ ∷ quote ∙-assoc ∷ []) M-info

----------------------------------------------------------------
-- H. Universe levels
----------------------------------------------------------------

-- three distinct levels in one goal (join a ⊔ b, ℕ lifted)
gH₁ : ∀ {a b} {A : Set a} {B : Set b} (xs : List A) (ys : List B) →
      length (xs ++ []) + length (ys ++ []) ≡ length xs + length ys
gH₁ xs ys = simp! (quote ++-identityʳ ∷ [])

-- a dependently-indexed sort (Vec ℕ n, with n free in the sort)
gH₂ : ∀ {n : ℕ} (v : Vec ℕ n) → v ≡ v
gH₂ v = simp! []

----------------------------------------------------------------
-- I. Longer rewrites
----------------------------------------------------------------

-- a ten-step chain through one rule
gI₁ : ∀ {x : ℕ} → x + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 ≡ x
gI₁ = simp! (quote +-identityʳ ∷ [])

-- eta-expanded function atoms: Agda eta-contracts `λ x → suc x` to
-- `suc` in the reflected goal, so a rule stated with the bare function
-- still matches
lenMapSuc : (l : List ℕ) → length (map suc l) ≡ length l
lenMapSuc l = simp! (quote length-map ∷ [])

gI₂ : ∀ (l : List ℕ) → length (map (λ x → suc x) l) ≡ length l
gI₂ l = simp! (quote lenMapSuc ∷ [])

----------------------------------------------------------------
-- J. `simp?` diagnostics
--
-- `simp?` reports (via a type error) which of the supplied rules
-- actually fired, as a ready-to-paste `simp!` call.  Being a fatal
-- diagnostic it cannot itself appear in a green definition, so each
-- entry pairs the verified `simp?` output (as a comment) with the
-- `simp!` call it suggests — checked live below, proving the suggestion
-- is correct and minimal.
----------------------------------------------------------------

-- Subset fires.  `simp? (quote +-identityʳ ∷ quote *-identityʳ ∷
-- quote *-zeroʳ ∷ quote +-identityˡ ∷ [])` on this goal reports:
--   simp! (*-identityʳ ∷ +-identityˡ ∷ [])
-- (note: original user order preserved; +-identityʳ and *-zeroʳ dropped)
gJ₁ : ∀ {x y : ℕ} → (x * 1) + (0 + y) ≡ x + y
gJ₁ = simp! (quote *-identityʳ ∷ quote +-identityˡ ∷ [])

-- All fire.  `simp? (quote *-identityʳ ∷ quote +-identityˡ ∷ [])`
-- reports:  simp! (*-identityʳ ∷ +-identityˡ ∷ [])
gJ₂ : ∀ {x y : ℕ} → (x * 1) + (0 + y) ≡ x + y
gJ₂ = simp! (quote *-identityʳ ∷ quote +-identityˡ ∷ [])

-- Polymorphic rule expanding to several engine rules is reported once
-- by its SOURCE name.  `simp? (quote +-identityʳ ∷ quote ++-identityʳ
-- ∷ [])` on this goal reports:  simp! (++-identityʳ ∷ [])
gJ₃ : ∀ (xs : List ℕ) → length (map suc (xs ++ [])) ≡ length (map suc xs)
gJ₃ xs = simp! (quote ++-identityʳ ∷ [])

-- No rules fire (definitional goal).  `simp? (quote +-identityʳ ∷ [])`
-- reports:  "no rules fired — the goal is closed definitionally; use
-- `simp! []`."
gJ₄ : ∀ {x : ℕ} → x ≡ x
gJ₄ = simp! []

-- LIMITATION (documented): conditional rules (hypothesis arrows in the
-- rule type) are not supported; `stripAndReduce` treats the hypothesis
-- as a pattern binder and the rule is rejected or never fires.  This
-- is roadmap item 11.

-- ERROR PATHS (documented, each verified by hand):
--   * non-equality goal:        simp! on `⊤`        → "goal is not a propositional equality"
--   * non-relation goal:        simpRel! on `x ≡ y` → works (≡ is a binary relation, falls
--                               through getRelSides); on `⊤` → "goal is not a binary relation"
--   * unprovable goal:          "failed to close the goal" + both normal forms
--   * diverging rule set:       same, with "(normal form with N nodes omitted)"
--   * polymorphic rule with no instantiation candidates:
--                               "could not instantiate polymorphic rule from the goal"

----------------------------------------------------------------
-- K. Conditional rules
----------------------------------------------------------------
-- A rule may carry side conditions as trailing premises.  simp!
-- instantiates its value binders from goal candidates and discharges
-- each premise: first BY ASSUMPTION (a context variable of exactly the
-- premise type), then BY DECISION (`prove`: resolve a
-- `Class.Decidable._⁇` instance and force the decision to `yes`).  A
-- *raw* propositional premise (e.g. `m ≤ n`) therefore needs no
-- `T`-wrapper.

-- K.1 ground (by decision).  condition holds (3 ≤ 5): fires.
-- `m≤n⇒m⊓n≡m : m ≤ n → m ⊓ n ≡ m` is the *unmodified* stdlib lemma —
-- its `m ≤ n` premise is decided automatically (`_≤_` over ℕ has a
-- `Class.Decidable._⁇` instance), with no boolean wrapper.
ck₁ : 3 ⊓ 5 ≡ 3
ck₁ = simp! (quote m≤n⇒m⊓n≡m ∷ [])

-- conditional rule chained with an ordinary one
ck₂ : (3 ⊓ 5) + 0 ≡ 3
ck₂ = simp! (quote m≤n⇒m⊓n≡m ∷ quote +-identityʳ ∷ [])

-- K.2 symbolic (by assumption).  `m`/`n` are abstract, so the premise
-- `m ≤ n` is NOT decidable; it is discharged from the goal's own `m ≤ n`
-- binder.  The emitted engine rule is still var-free (its operands `m`,
-- `n` are atoms), so its soundness obligation stays unconditional.
sk₁ : ∀ {m n : ℕ} → m ≤ n → (m ⊓ n) ≡ m
sk₁ _ = simp! (quote m≤n⇒m⊓n≡m ∷ [])

-- symbolic conditional chained with an ordinary rule
sk₂ : ∀ {m n : ℕ} → m ≤ n → (m ⊓ n) + 0 ≡ m
sk₂ _ = simp! (quote m≤n⇒m⊓n≡m ∷ quote +-identityʳ ∷ [])

-- A premise with neither a usable assumption nor a `_⁇` instance does
-- not fire, and the rule fires only on operands present in the goal
-- (the condition is dispatched at macro time).  A false ground condition
-- or an abstract premise with no assumption fails cleanly, e.g.
--   bad₁ : 5 ⊓ 3 ≡ 5
--   bad₁ = simp! (quote m≤n⇒m⊓n≡m ∷ [])         -- 5 ≤ 3 false → "failed to close"
--   bad₂ : ∀ {m n : ℕ} → (m ⊓ n) ≡ m
--   bad₂ = simp! (quote m≤n⇒m⊓n≡m ∷ [])         -- no m ≤ n in scope → "failed to close"
