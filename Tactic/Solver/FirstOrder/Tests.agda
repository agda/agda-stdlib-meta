{-# OPTIONS --without-K --safe #-}
--------------------------------------------------------------------------------
-- Capabilities and limitations of the `firstorder` solver.
--
-- PART 1 (capabilities): 44 goals proved automatically by the `firstorder`
-- macro — propositional reasoning over →, ×, ⊎, ¬, ⊤, ⊥ (complete for
-- intuitionistic propositional logic), universal-quantifier prefixes, and
-- ambient hypotheses (local variables of propositional type). Every atom carries
-- its own universe level, so the goals below are stated level-polymorphically
-- and freely mix levels (with `⊤`/`⊥` staying the genuine `Set₀` units). The
-- search runs inside Agda's evaluator during type-checking, so a green module
-- means every goal was discharged.
--
-- PART 2 (limitations): negative tests. A *failing* macro call is a hard type
-- error and cannot live in a compiling file, so instead we assert at the value
-- level that the search returns `nothing` — a machine-checked demonstration that
-- the solver cannot prove these. The limitations that manifest only at the
-- reflection level (classical reasoning, quantifier instantiation, the `A → ⊤`
-- meta quirk) are shown as commented macro calls at the bottom.
--------------------------------------------------------------------------------

module Tactic.Solver.FirstOrder.Tests where

open import Data.Product using (_×_)
open import Data.Sum       using (_⊎_)
open import Data.Unit      using (⊤)
open import Data.Empty     using (⊥)
open import Level          using (Level)
open import Relation.Nullary using (¬_)

open import Tactic.Solver.FirstOrder

--------------------------------------------------------------------------------
-- PART 1 — Capabilities
--------------------------------------------------------------------------------

module _ {a b c d : Level} {A : Set a} {B : Set b} {C : Set c} {D : Set d} where

  -- Implication (the {S,K,I} combinators and friends)
  I-comb : A → A
  I-comb = firstorder

  K-comb : A → B → A
  K-comb = firstorder

  S-comb : (A → B → C) → (A → B) → A → C
  S-comb = firstorder

  compose : (A → B) → (B → C) → A → C
  compose = firstorder

  compose3 : (A → B) → (B → C) → (C → D) → A → D
  compose3 = firstorder

  -- Conjunction
  ∧-fst : A × B → A
  ∧-fst = firstorder

  ∧-snd : A × B → B
  ∧-snd = firstorder

  ∧-intro : A → B → A × B
  ∧-intro = firstorder

  ∧-comm : A × B → B × A
  ∧-comm = firstorder

  ∧-assoc-lr : (A × B) × C → A × (B × C)
  ∧-assoc-lr = firstorder

  ∧-assoc-rl : A × (B × C) → (A × B) × C
  ∧-assoc-rl = firstorder

  -- Disjunction
  ∨-inl : A → A ⊎ B
  ∨-inl = firstorder

  ∨-inr : B → A ⊎ B
  ∨-inr = firstorder

  ∨-comm : A ⊎ B → B ⊎ A
  ∨-comm = firstorder

  ∨-elim : (A → C) → (B → C) → A ⊎ B → C
  ∨-elim = firstorder

  ∨-idem : A ⊎ A → A
  ∨-idem = firstorder

  -- Interaction
  distrib : A × (B ⊎ C) → (A × B) ⊎ (A × C)
  distrib = firstorder

  distrib-rev : (A × B) ⊎ (A × C) → A × (B ⊎ C)
  distrib-rev = firstorder

  curry′ : (A × B → C) → A → B → C
  curry′ = firstorder

  uncurry′ : (A → B → C) → A × B → C
  uncurry′ = firstorder

  split : (A ⊎ B → C) → (A → C) × (B → C)
  split = firstorder

  -- Units and absurdity
  triv : ⊤
  triv = firstorder

  -- `A → ⊤` as a whole RHS would leave the domain as an unsolved meta
  -- (see Limitation 4); introducing the argument first sidesteps it.
  to-⊤ : A → ⊤
  to-⊤ _ = firstorder

  ex-falso : ⊥ → A
  ex-falso = firstorder

  -- Negation: `¬_` is recognised as `_→ ⊥`, so it can be written either way.
  dni⊥ : A → ((A → ⊥) → ⊥)   -- with an explicit ⊥
  dni⊥ = firstorder

  dni : A → ¬ ¬ A            -- with ¬ (double-negation introduction)
  dni = firstorder

  contra : (A → B) → ¬ B → ¬ A
  contra = firstorder

  tne : ¬ ¬ ¬ A → ¬ A        -- triple negation collapses to one
  tne = firstorder

  de-morgan : ¬ (A ⊎ B) → ¬ A
  de-morgan = firstorder

  -- Harder intuitionistic tautologies. These need G4ip's contraction-free
  -- implication-left rules; the earlier naive search could not find them.
  dn-lem : ¬ ¬ (A ⊎ ¬ A)              -- double-negation of excluded middle
  dn-lem = firstorder

  no-contra : ¬ (A × ¬ A)
  no-contra = firstorder

  dm-full : ¬ (A ⊎ B) → (¬ A × ¬ B)   -- both halves of one De Morgan law
  dm-full = firstorder

  nested : ((A → B) → C) → B → C
  nested = firstorder

  -- Explicit fuel control
  I-comb′ : A → A
  I-comb′ = firstorderN 4

-- Universal quantifiers at the goal prefix are stripped and re-introduced, so
-- the bound variable can be a proposition or an individual (as long as no
-- quantifier *instantiation* is needed — see Limitation 3).
module _ where

  ∀-id : ∀ {ℓ} (X : Set ℓ) → X → X
  ∀-id = firstorder

  ∀-const : ∀ {ℓ₁ ℓ₂} (X : Set ℓ₁) (Y : Set ℓ₂) → X → Y → X
  ∀-const = firstorder

  ∀-dup : ∀ {ℓ} (X : Set ℓ) → X → X × X
  ∀-dup = firstorder

  -- a genuine ∀ over individuals: the bound `x` appears only inside atoms
  ∀-pred : ∀ {ℓ} {D : Set ℓ} {P : D → Set ℓ} → (x : D) → P x → P x
  ∀-pred = firstorder

-- Ambient hypotheses: local variables of propositional type are used as
-- assumptions, not just the goal's own structure. (Type variables like A B C —
-- whose type is itself a universe `Set _` — are atoms, not hypotheses, so the
-- regression goals above still hold.)
module _ {a b c : Level} {A : Set a} {B : Set b} {C : Set c} where

  -- a pattern-introduced argument becomes a usable hypothesis
  use-hyp : (h : A) → A
  use-hyp h = firstorder

  modus : A → (A → B) → B
  modus a f = firstorder

  chain-hyp : A → (A → B) → (B → C) → C
  chain-hyp a f g = firstorder

  case-hyp : A ⊎ B → (A → C) → (B → C) → C
  case-hyp s f g = firstorder

  contra-hyp : A → ¬ A → C
  contra-hyp a na = firstorder

-- a hypothesis that is a *module parameter* (never part of the goal type)
module _ {a b : Level} {A : Set a} {B : Set b} (f : A → B) where
  apply-param : A → B
  apply-param a = firstorder

--------------------------------------------------------------------------------
-- PART 2 — Limitations (negative tests, verified at the value level)
--------------------------------------------------------------------------------

module Limitations where
  open import Data.Fin   using (zero; suc)
  open import Data.List  using ([])
  open import Data.Maybe using (nothing; from-just)
  open import Relation.Binary.PropositionalEquality using (_≡_; refl)

  open import Tactic.FirstOrder.Core   using (Formula; atom; ⊤′; ⊥′; _∧′_; _∨′_; _⇒′_; _⊢_)
  open import Tactic.FirstOrder.Search using (search)

  ------------------------------------------------------------------------------
  -- Limitation 1: the logic is INTUITIONISTIC, not classical.
  --
  -- The following are classically valid but have no intuitionistic proof. Since
  -- G4ip is complete for IPL, exhausting the (finite) search space returns
  -- `nothing` definitively — no amount of fuel would help.
  ------------------------------------------------------------------------------

  p q : Formula 2
  p = atom zero
  q = atom (suc zero)

  r : Formula 1
  r = atom zero

  -- Peirce's law:  ((P → Q) → P) → P
  peirce : Formula 2
  peirce = ((p ⇒′ q) ⇒′ p) ⇒′ p

  _ : search 20 [] peirce ≡ nothing
  _ = refl

  -- Excluded middle:  P ∨ ¬P
  excluded-middle : Formula 1
  excluded-middle = r ∨′ (r ⇒′ ⊥′)

  _ : search 20 [] excluded-middle ≡ nothing
  _ = refl

  -- Double-negation elimination:  ¬¬P → P
  dne : Formula 1
  dne = ((r ⇒′ ⊥′) ⇒′ ⊥′) ⇒′ r

  _ : search 20 [] dne ≡ nothing
  _ = refl

  ------------------------------------------------------------------------------
  -- Limitation 2: the `search` primitive is FUEL-BOUNDED — but `firstorder` is
  -- NOT subject to it.
  --
  -- `firstorder` uses the fuel-free decider `decideFast`, whose ceiling is the
  -- proven termination measure `μ`, so it is complete for intuitionistic
  -- propositional logic. The fuel cap below is a property only of the lower-level
  -- `search` primitive (and of `firstorderN`, which exposes it): a goal whose
  -- search depth exceeds the given fuel fails. `A → A` needs ≥ 2 steps (⊃R, init).
  ------------------------------------------------------------------------------

  identity : Formula 1
  identity = atom zero ⇒′ atom zero

  -- fuel 1 is not enough → no proof found
  _ : search 1 [] identity ≡ nothing
  _ = refl

  -- fuel 2 is enough → `found` extracts the derivation (type-checks iff `just`)
  _ : [] ⊢ identity
  _ = from-just (search 2 [] identity)

  ------------------------------------------------------------------------------
  -- Limitation 3: the solver is PURELY PROPOSITIONAL and SYNTACTIC.
  --
  -- Any subterm not built from ×, ⊎, →, ¬, ⊤, ⊥ is an opaque atom, and distinct
  -- atoms are logically independent. So there is no way to prove an implication
  -- between two unrelated atoms — and in particular a universally quantified
  -- hypothesis (an opaque atom) cannot be *instantiated*: `(∀ x → P x) → P a`
  -- is out of reach (see the commented `instM` below).
  ------------------------------------------------------------------------------

  _ : search 20 [] (p ⇒′ q) ≡ nothing
  _ = refl

--------------------------------------------------------------------------------
-- Further limitations, shown as commented macro calls: a failing macro is a hard
-- type error and cannot sit in a compiling file, so uncomment any line to
-- observe the failure it documents.
--------------------------------------------------------------------------------

-- module CommentedFailures {A B : Set} {D : Set} {P : D → Set} {a : D} where
--
--   -- Limitation 1 (classical), via the macro: Peirce's law.
--   peirceM : ((A → B) → A) → A
--   peirceM = firstorder
--
--   -- Limitation 3: quantifiers can only be *stripped* from the goal prefix
--   -- (see `∀-id`, `∀-pred` above), never *instantiated*. A universally
--   -- quantified hypothesis is an opaque atom, so it cannot be applied to a
--   -- witness: `(∀ x → P x) → P a` is out of reach (`∀ x → P x` and `P a` are
--   -- two unrelated atoms).
--   instM : ((x : D) → P x) → P a
--   instM = firstorder
--
--   -- Limitation 4: when the macro is the *whole* RHS of a function-typed goal
--   -- whose codomain ignores the domain, Agda hands the macro a goal with an
--   -- unsolvable metavariable domain. This is an elaboration quirk the macro
--   -- cannot fix, but it is *detected*: the line below fails with a clear error
--   -- pointing at the workaround — introduce the argument(s) first, as `to-⊤`
--   -- above does with `to-⊤ _ = firstorder`.
--   to-⊤M : A → ⊤
--   to-⊤M = firstorder

--------------------------------------------------------------------------------
-- PART 3 — engine-level unit tests
--
-- The macro tests above exercise the whole pipeline; here we test the
-- components directly, at the value level: the G4ip calculus + `solve`, and
-- the three search entry points `search` / `decide` / `decideFast`.
--------------------------------------------------------------------------------

module Engine where
  open import Data.Fin    using (Fin; zero; suc)
  open import Data.List   using ([])
  open import Data.List.Relation.Unary.Any using (here)
  open import Data.Maybe  using (nothing; from-just)
  open import Relation.Binary.PropositionalEquality using (_≡_; refl)

  open import Level using (0ℓ)
  open import Tactic.FirstOrder.Core
  open import Tactic.FirstOrder.Search using (search)
  open import Tactic.FirstOrder.Decide using (decide; decideFast)

  A B : Formula 2
  A = atom zero
  B = atom (suc zero)

  peirce : Formula 2
  peirce = ((A ⇒′ B) ⇒′ A) ⇒′ A

  -- a hand-built G4ip derivation interprets via `solve`, and its soundness
  -- payload is exactly the identity function it should be.
  ⊢-id : ∀ {ρ : Fin 2 → Set} → ⟦ A ⇒′ A ⟧ (λ _ → 0ℓ) ρ
  ⊢-id {ρ} = solve ρ (⊃R (init (here refl)))

  _ : ∀ {ρ : Fin 2 → Set} {a : ρ zero} → ⊢-id {ρ} a ≡ a
  _ = refl

  -- each entry point finds a proof…
  _ : [] ⊢ (A ∧′ B ⇒′ B ∧′ A)
  _ = from-just (search 8 [] (A ∧′ B ⇒′ B ∧′ A))

  _ : [] ⊢ (A ∧′ B ⇒′ B ∧′ A)
  _ = from-just (decide [] (A ∧′ B ⇒′ B ∧′ A))

  _ : [] ⊢ (¬′ ¬′ (A ∨′ ¬′ A))           -- exercises the ⊃L⊃ rule
  _ = from-just (decideFast [] (¬′ ¬′ (A ∨′ ¬′ A)))

  -- …and `decide`/`decideFast` reject the (classically valid) Peirce's law
  -- (`search` on Peirce is covered by Limitation 1 above)
  _ : decide [] peirce ≡ nothing
  _ = refl

  _ : decideFast [] peirce ≡ nothing
  _ = refl
