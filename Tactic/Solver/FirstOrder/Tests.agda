{-# OPTIONS --without-K --safe #-}
--------------------------------------------------------------------------------
-- Capabilities and limitations of the `firstorder` solver.
--
-- PART 1 (capabilities): 115 goals proved automatically by the `firstorder`
-- macro — propositional reasoning over →, ×, ⊎, ¬, ⊤, ⊥ (complete for
-- intuitionistic propositional logic), universal-quantifier prefixes, ambient
-- hypotheses (local variables of propositional type), definitional aliases of
-- the connectives (unfolded by a connective-blocking `normalise`), and leaves
-- discharged by side oracles: reflexivity of `_≡_`; an in-scope instance of the
-- leaf's type; any decidable proposition that holds — or, dually, a decidably
-- *false* hypothesis (absurd ⇒ anything), given `Class.Decidable` instances;
-- ring/semiring equations over a bundle (`firstorderR R`); user-supplied
-- lemmas (`firstorderWith`); and — opt-in — leaves solved by recursive
-- constructor search (`firstorderC`, inductive predicates) or by quantifier
-- reasoning over context hypotheses (`firstorderQ`/`firstorderQN n`, ∀-elim and
-- ∃-intro — both recursive: an instantiation's leftover hypothesis arguments and
-- an existential witness's residual goal are themselves solved recursively, so
-- e.g. `(∀ x → P x → Q x) → P a → Q a` and compound/nested existentials go
-- through; `firstorderQWith`/`firstorderQNWith n` additionally instantiate the
-- *supplied lemmas*, so `firstorderQWith <-trans` chains transitivity unaided).
-- The level-polymorphic `⊤`/`⊥` are handled by gated oracles. An unprovable
-- goal reports a real error — definitive unprovability plus the atom table —
-- instead of an unsolved `from-just` constraint.
-- Every atom
-- carries its own universe level, so the goals below are stated
-- level-polymorphically and freely mix levels (with `⊤`/`⊥` staying the genuine
-- `Set₀` units). The search runs inside Agda's evaluator during type-checking,
-- so a green module means every goal was discharged.
--
-- PART 2 (limitations): negative tests. A *failing* macro call is a hard type
-- error and cannot live in a compiling file, so instead we assert at the value
-- level that the search returns `nothing` — a machine-checked demonstration that
-- the solver cannot prove these. The limitations that manifest only at the
-- reflection level (classical reasoning, quantifier instantiation, the whole-RHS
-- meta quirk — `A → ⊤` and functions into η-records) are shown as commented
-- macro calls at the bottom.
--------------------------------------------------------------------------------

module Tactic.Solver.FirstOrder.Tests where

open import Data.Nat       using (ℕ; _+_)
open import Data.Product   using (_×_; ∃)
open import Data.Sum       using (_⊎_)
open import Data.Unit      using (⊤)
open import Data.Empty     using (⊥)
open import Level          using (Level)
open import Relation.Binary.PropositionalEquality using (_≡_)
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

  -- A whole-RHS goal `… → C` whose `C` is inhabited without the argument (`⊤`
  -- here, also η-records / record products) leaves the domain an unsolved meta
  -- (Limitation 4); introducing the argument first sidesteps it.
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

-- Definitional aliases of the connectives are unfolded before reification (the
-- goal is normalised with the connectives themselves blocked), so a goal stated
-- through `def`-aliases is solved just like the primitive form.
module _ {A B : Set} where
  _×ᵈ_ : Set → Set → Set ; M ×ᵈ N = M × N
  _⊎ᵈ_ : Set → Set → Set ; M ⊎ᵈ N = M ⊎ N
  ¬ᵈ_  : Set → Set       ; ¬ᵈ M   = ¬ M

  alias-∧ : (A ×ᵈ B) → A
  alias-∧ = firstorder

  alias-⊎ : A → A ⊎ᵈ B
  alias-⊎ = firstorder

  alias-¬ : A → ¬ᵈ (¬ᵈ A)
  alias-¬ = firstorder

  alias-mixed : (A ×ᵈ B) → B × A    -- alias on the left, primitive on the right
  alias-mixed = firstorder

-- Leaf oracles: a leaf the propositional engine treats as opaque may still be
-- discharged by a side oracle (currently reflexivity of `_≡_`) and then used
-- like any hypothesis — at any nesting, and under a stripped ∀-prefix.
module _ {a : Level} {A : Set a} {x : A} where
  refl-goal : x ≡ x
  refl-goal = firstorder

  refl-nested : A → A × (x ≡ x)             -- the oracle proves the right conjunct
  refl-nested = firstorder

  refl-hyp : (x ≡ x → A) → A                 -- and a discharged leaf feeds modus ponens
  refl-hyp = firstorder

-- definitional equality is discharged by the same `refl` oracle
defeq-refl : 3 + 4 ≡ 7
defeq-refl = firstorder

-- a refl leaf whose terms are stripped ∀-binders (oracle runs in their context)
poly-refl : (X : Set) (z : X) → z ≡ z
poly-refl = firstorder

-- Decidable leaves: with `Class.Decidable` instances in scope, the Dec oracle
-- discharges any decidable proposition that holds (e.g. `_≤_`, `_<_`) — the
-- engine still handles the logical skeleton. Without the import it is inert, so
-- the regression goals elsewhere (which do not import it) are unaffected.
module DecLeaves where
  open import Data.Nat       using (_≤_; _<_)
  open import Class.Decidable using (_⁇)

  dec-le : 2 ≤ 5
  dec-le = firstorder

  dec-lt : 1 < 4
  dec-lt = firstorder

  dec-nested : {A : Set} → A → A × (2 ≤ 5)        -- decidable leaf built into structure
  dec-nested = firstorder

  dec-hyp : {A : Set} → (1 < 4 → A) → A            -- decidable leaf discharged, feeds MP
  dec-hyp = firstorder

-- Equational leaves: `firstorderR R` additionally discharges `_≡_` leaves with
-- the ring solver over the bundle `R`, composing ring reasoning with the
-- propositional skeleton (the bundle is supplied, as it cannot be inferred).
module RingLeaves where
  open import Data.Nat            using (ℕ; _+_; _*_)
  open import Data.Nat.Properties using (+-*-commutativeSemiring)

  ring-comm : (x y : ℕ) → x + y ≡ y + x                  -- pure ring equation
  ring-comm = firstorderR +-*-commutativeSemiring

  ring-distrib : (x y z : ℕ) → x * (y + z) ≡ x * y + x * z
  ring-distrib = firstorderR +-*-commutativeSemiring

  ring-nested : {A : Set} (x y : ℕ) → A → A × (x + y ≡ y + x)   -- skeleton + ring leaf
  ring-nested = firstorderR +-*-commutativeSemiring

  ring-hyp : {A : Set} (x y : ℕ) → (x + y ≡ y + x → A) → A      -- ring leaf feeds MP
  ring-hyp = firstorderR +-*-commutativeSemiring

-- Decidable FALSITY: a decidably-false hypothesis is absurd, so any goal
-- follows. (Needs `Class.Decidable` instances in scope.)
module DecFalseLeaves where
  open import Data.Nat        using (_≤_; _<_)
  open import Class.Decidable using (_⁇)

  absurd-≤ : {A : Set} → 5 ≤ 2 → A
  absurd-≤ = firstorder

  absurd-< : {A : Set} → 4 < 1 → A
  absurd-< = firstorder

  absurd-mix : {A B : Set} → A → 3 < 1 → B      -- a false hypothesis ⇒ anything
  absurd-mix = firstorder

-- Instance search: a leaf is discharged when an instance of its own type is in
-- scope.
module InstanceLeaves where
  record Tag : Set where constructor tag
  instance tagInst : Tag
  tagInst = tag

  use-inst : Tag
  use-inst = firstorder

  use-inst-∧ : {A : Set} → A → A × Tag           -- discharged leaf built into ×
  use-inst-∧ = firstorder

-- User-supplied lemmas (`firstorderWith`): extra facts usable as hypotheses,
-- even when not in the goal's local context. `firstorder` alone cannot prove the
-- opaque atom `Marker`; the supplied `fact` discharges it. A single lemma is
-- passed bare; several (of possibly different types/levels) as a `_,,_`-tuple.
module UserLemmas where
  record Marker : Set  where constructor mk
  record Other  : Set₁ where constructor mkO    -- a different type, different level
  fact : Marker
  fact = mk
  other : Other
  other = mkO

  use-lemma : Marker
  use-lemma = firstorderWith fact                  -- single lemma, bare

  use-lemma-∧ : {A : Set} → A → A × Marker         -- lemma proves one conjunct
  use-lemma-∧ = firstorderWith fact

  -- two lemmas of different types AND different universe levels, in one tuple
  use-hetero : Marker × Other
  use-hetero = firstorderWith (fact ◂ other)

-- Products of record types: `A × B` of two records normalises to `Σ A (λ _ → B)`
-- (the `_×_` alias is unfolded), so the reifier recognises a non-dependent `Σ`
-- as `∧`. Without that, these goals were silently unprovable.
module RecordProducts where
  record S : Set where constructor mkS ; field f : ⊤
  record T : Set where constructor mkT ; field g : ⊤
  module _ {A : Set} where
    rec-×-self : S → S × S
    rec-×-self x = firstorder
    rec-×-two  : S → T → S × T
    rec-×-two  x y = firstorder
    rec-×-hyp  : S × T → T × S            -- record product as hypothesis and goal
    rec-×-hyp  h = firstorder
    rec-×-mix  : S → A → S × A            -- one record operand (always worked)
    rec-×-mix  x y = firstorder

-- `firstorderC` (opt-in): also discharges leaves by recursive constructor search
-- (`Tactic.Constrs`), so inductively-defined propositions become solvable.
module Constructors where
  open import Data.Nat using (ℕ; zero; suc; _≤_)
  data Even : ℕ → Set where
    ez : Even 0
    es : ∀ {n} → Even n → Even (suc (suc n))

  le-leaf : 0 ≤ 5                       -- a `_≤_` proof, built from z≤n/s≤s
  le-leaf = firstorderC

  ev-leaf : Even 4                      -- a user inductive predicate
  ev-leaf = firstorderC

  ev-nested : {A : Set} → A → A × Even 4    -- constructor leaf + propositional skeleton
  ev-nested = firstorderC

  ev-hyp : {A : Set} → (Even 4 → A) → A      -- constructor leaf feeds modus ponens
  ev-hyp = firstorderC

-- `firstorderQ` (opt-in): quantifier reasoning over *context* hypotheses — both
-- ∀-elimination and ∃-introduction, with witnesses found by unification. The
-- ∀-hypothesis / ∃-witness proof must be a local argument.
module Quantifiers {D : Set} {P Q : D → Set} {R : D → D → Set} where
  -- ∀-elimination: a universally quantified context hypothesis is instantiated by
  -- applying it to fresh metas, which unification against the leaf then solves.
  ∀-inst : (∀ x → P x) → (a : D) → P a
  ∀-inst f a = firstorderQ

  ∀-inst2 : (∀ x y → R x y) → (a b : D) → R a b        -- n-ary, both witnesses found
  ∀-inst2 f a b = firstorderQ

  ∀-inst-∧ : (∀ x → P x) → (a b : D) → P a × P b        -- engine splits ×, oracle each leaf
  ∀-inst-∧ f a b = firstorderQ

  ∀-inst-mp : (∀ x → P x) → (a : D) → (P a → Q a) → Q a -- instantiation feeds modus ponens
  ∀-inst-mp f a g = firstorderQ

  -- the instantiated hypothesis itself needs an argument: the witness `a` is pinned
  -- by the conclusion, and the remaining obligation `P a` is solved recursively.
  ∀-hyparg : (∀ x → P x → Q x) → (a : D) → P a → Q a
  ∀-hyparg f a p = firstorderQ

  ∀-hyparg2 : (∀ x → P x → Q x → R x x) → (a : D) → P a → Q a → R a a  -- two arguments
  ∀-hyparg2 f a p q = firstorderQ

  -- the argument obligation is compound (`P a × Q a`), assembled by the engine
  ∀-conjarg : (∀ x → (P x × Q x) → R x x) → (a : D) → P a → Q a → R a a
  ∀-conjarg f a p q = firstorderQ

  -- ∃-introduction: a `Σ`/`∃` leaf is discharged by `(w , h)` with a witness `w`
  -- from the context. The proof obligation `B w` is met either by pairing `w` with
  -- a context hypothesis (`unify` pins a metavariable witness through the
  -- predicate's rigid spine), or by *recursively solving* `B w` — so a compound or
  -- nested existential proof is assembled by the engine / a deeper ∃ step.
  ∃-intro : (a : D) → P a → ∃ P
  ∃-intro a p = firstorderQ

  ∃-pick : (a b : D) → P b → ∃ P                        -- picks the witness that has a proof
  ∃-pick a b p = firstorderQ

  ∃-rel : (a b : D) → R a b → ∃ (λ x → R x b)           -- ∃ over the first slot of a relation
  ∃-rel a b r = firstorderQ

  ∃-app : (f : D → D) (a : D) → P (f a) → ∃ P           -- witness is an application `f a`
  ∃-app f a p = firstorderQ

  ∃-nested : {A : Set} → A → (a : D) → P a → A × ∃ P    -- ∃ leaf inside the skeleton
  ∃-nested x a p = firstorderQ

  -- compound predicate: the residual `P a × Q a` is solved recursively (the engine
  -- splits the ×; the leaves come from the context proofs `p`, `q`).
  ∃-conj : (a : D) → P a → Q a → ∃ (λ x → P x × Q x)
  ∃-conj a p q = firstorderQ

  -- nested existential: the residual is itself a `∃`, discharged by a deeper step.
  ∃-∃ : (a b : D) → R a b → ∃ (λ x → ∃ (λ y → R x y))
  ∃-∃ a b r = firstorderQ

  -- both at once: a product whose right component is a nested existential.
  ∃-deep : (a b : D) → R a b → P a → ∃ (λ x → P x × ∃ (λ y → R x y))
  ∃-deep a b r p = firstorderQ

  -- ∀-elim and ∃-intro compose: the witness `a` comes from the context, the proof
  -- `f a` from instantiating the universal hypothesis.
  ∀-then-∃ : (∀ x → P x) → (a : D) → ∃ P
  ∀-then-∃ f a = firstorderQ

  -- explicit quantifier-recursion depth (`firstorderQ` defaults to 2)
  ∀-inst-fuel : (∀ x → P x) → (a : D) → P a
  ∀-inst-fuel f a = firstorderQN 1

-- The level-polymorphic units (`Data.Unit.Polymorphic.⊤`, which normalises to
-- `Lift ℓ ⊤`, and dually `⊥`) are handled by gated oracles: a `Lift ℓ ⊤` leaf is
-- proved outright, and a `Lift ℓ ⊥` hypothesis is absurd. (They cannot be the
-- `⊤′`/`⊥′` connectives: the Core interpretation is monomorphic.)
module PolyUnits {ℓ : Level} {A : Set} where
  open import Data.Unit.Polymorphic  renaming (⊤ to ⊤ₚ)
  open import Data.Empty.Polymorphic renaming (⊥ to ⊥ₚ)

  top-poly : A → A × ⊤ₚ {ℓ}
  top-poly a = firstorder

  bot-poly : ⊥ₚ {ℓ} → A
  bot-poly b = firstorder

-- `firstorderQWith` (and `firstorderQNWith n`): the supplied lemmas are both
-- extra hypotheses and *instantiation candidates* for the quantifier oracles —
-- a universally quantified lemma is applied (and chained) automatically.
module LemmaInstantiation where
  open import Data.Nat            using (ℕ; _<_)
  open import Data.Nat.Properties using (<-trans)

  module _ (a b c d e : ℕ) (p : a < b) (q : b < c) (r : c < d) (s : d < e) where
    chain3 : a < d                        -- <-trans p (<-trans q r), found alone
    chain3 = firstorderQWith <-trans

    chain4 : a < e                        -- three compositions need depth 3
    chain4 = firstorderQNWith 3 <-trans

    ∃-chain : ∃ (λ x → a < x)             -- lemma candidates feed the ∃-oracle too
    ∃-chain = firstorderQWith <-trans

-- Record introduction and elimination (`firstorderQ`):
--   * a leaf headed by a record — or a data type with a *unique* constructor —
--     is proved by introducing the constructor and solving the fields with the
--     engine; `_⇔_`/`Equivalence` goes through `mk⇔`, so its congruence fields
--     come for free and only `to`/`from` remain;
--   * a *hypothesis* of record type is expanded into its field projections
--     (`e : A ⇔ B` yields `to e : A → B` as a usable ⇒-antecedent), and the
--     projections also serve as instantiation candidates — for `e : ∃ P` that
--     is ∃-elimination (`proj₂ e : P (proj₁ e)` pins witnesses).
module RecordIntroElim {A B C D : Set} {P : D → Set} where
  open import Function.Bundles using (_⇔_)

  ⇔-refl : A ⇔ A
  ⇔-refl = firstorderQ

  ×-comm-⇔ : (A × B) ⇔ (B × A)
  ×-comm-⇔ = firstorderQ

  deMorgan-⇔ : (¬ (A ⊎ B)) ⇔ (¬ A × ¬ B)
  deMorgan-⇔ = firstorderQ

  curry-⇔ : (A × B → C) ⇔ (A → B → C)
  curry-⇔ = firstorderQ

  -- = Data.Sum.Function.Propositional._⊎-⇔_ (stdlib proves it via ⊎-map +
  -- mk⇔ plumbing); intro and elim combined.
  ⊎-⇔ : A ⇔ B → C ⇔ D → (A ⊎ C) ⇔ (B ⊎ D)
  ⊎-⇔ e f = firstorderQ

  -- = Data.Product.Function.NonDependent.Propositional._×-⇔_
  ×-⇔ : A ⇔ B → C ⇔ D → (A × C) ⇔ (B × D)
  ×-⇔ e f = firstorderQ

  ⇔-trans : A ⇔ B → B ⇔ C → A ⇔ C
  ⇔-trans e f = firstorderQ

  -- ∃-elimination: the Σ-hypothesis's projections do the work
  ∃-elim : ∃ P → (∀ x → P x → C) → C
  ∃-elim e g = firstorderQ

  -- a generic single-constructor record, built from engine-solved fields
  record Wrap (X : Set) : Set where
    constructor wrap
    field unwrap : X

  wrap-intro : A → Wrap ((A × B) ⊎ A)
  wrap-intro a = firstorderQ

--------------------------------------------------------------------------------
-- Real lemmas from the standard library, re-proved by a single tactic call.
-- Each goal below restates a *named* stdlib lemma (module and name cited at the
-- clause); the originals are proved by hand, several through a classical detour
-- (excluded middle / the ¬¬-monad) that the IPL-complete engine does not need.
-- A companion module, `Tactic.Solver.FirstOrder.Tests.Colist`, holds two more
-- (over musical colists) that cannot live here because `Codata.Musical.Colist`
-- is not `--safe`.
--------------------------------------------------------------------------------

module StdlibNegation {A B C W : Set} where
  -- = Relation.Nullary.Negation.independence-of-premise-⊎ .  The original goes
  -- through excluded middle, with a `Dec A` case-split helper:
  --   independence-of-premise-⊎ f = ¬¬-map helper ¬¬-excluded-middle
  --     where
  --     helper : Dec A → (A → B) ⊎ (A → C)
  --     helper (yes p) = Sum.map const const (f p)
  --     helper (no ¬p) = inj₁ (flip contradiction ¬p)
  -- The engine instead finds a direct intuitionistic proof.
  independence-of-premise-⊎ : (A → B ⊎ C) → ¬ ¬ ((A → B) ⊎ (A → C))
  independence-of-premise-⊎ = firstorder

  -- = Relation.Nullary.Negation.call/cc (the ¬¬-translation of Peirce's law);
  -- original: `call/cc hyp ¬a = hyp (flip contradiction ¬a) ¬a`.
  call/cc : ((A → W) → ¬ ¬ A) → ¬ ¬ A
  call/cc = firstorder

  -- = Relation.Nullary.Negation.Core.stable  (`Stable A` unfolded);
  -- original: `stable ¬[¬¬a→a] = ¬[¬¬a→a] (contradiction (¬[¬¬a→a] ∘ const))`.
  stable : ¬ ¬ (¬ ¬ A → A)
  stable = firstorder

  -- = Relation.Nullary.Negation.Core.negated-stable
  negated-stable : ¬ ¬ ¬ A → ¬ A
  negated-stable = firstorder

  -- = Relation.Nullary.Negation.Core.contra-diagonal
  contra-diagonal : (A → ¬ A) → ¬ A
  contra-diagonal = firstorder

  -- = Relation.Nullary.Negation.Core.contradiction₂
  contradiction₂ : A ⊎ B → ¬ A → ¬ B → W
  contradiction₂ = firstorder

module StdlibInfinitelyOften where
  open import Level using (0ℓ)
  open import Relation.Unary using (Pred; _∪_)
  open import Data.Nat.InfinitelyOften using (Inf; _∪-Fin_)

  -- = Data.Nat.InfinitelyOften.commutes-with-∪ : "true infinitely often"
  -- distributes over union, classically.  The original is four lines of
  -- ¬¬-monad combinators:
  --   commutes-with-∪ p∪q =
  --     call/cc λ ¬[p⊎q] →
  --     (λ ¬p ¬q → contradiction (¬p ∪-Fin ¬q) p∪q)
  --       <$> ¬[p⊎q] ∘ inj₁ ⊛ ¬[p⊎q] ∘ inj₂
  -- Supplying the one non-propositional ingredient — `_∪-Fin_ : Fin P → Fin Q →
  -- Fin (P ∪ Q)` — lets the engine do all the logic (`Inf = ¬ Fin`, so the three
  -- `Fin` types are the atoms).  Plain `firstorder` fails here: without the
  -- lemma the atoms are unrelated.
  module _ {P Q : Pred ℕ 0ℓ} where
    commutes-with-∪ : Inf (P ∪ Q) → ¬ ¬ (Inf P ⊎ Inf Q)
    commutes-with-∪ = firstorderWith (_∪-Fin_ {P = P} {Q = Q})

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
-- type error and cannot sit in a compiling file, so uncomment the module (and a
-- chosen clause) to observe the failure it documents. The module is
-- self-contained — its imports and the alias it needs are included.
--------------------------------------------------------------------------------

-- module CommentedFailures {A B : Set} {D : Set} {P Q : D → Set}
--                          {R : D → D → Set} {a : D} {u v : A} where
--   open import Data.Product using (_×_; ∃)
--   open import Relation.Binary.PropositionalEquality using (_≡_)
--
--   -- Limitation 1 (classical), via the macro: Peirce's law.
--   peirceM : ((A → B) → A) → A
--   peirceM = firstorder
--
--   -- Limitation 3 (∀-instantiation under plain `firstorder`): the bare macro only
--   -- *strips* a ∀-prefix from the goal (see `∀-id`, `∀-pred` above); it never
--   -- *instantiates* a quantified hypothesis — that is `(∀ x → P x)` and `P a` are
--   -- two unrelated atoms. The opt-in `firstorderQ` does instantiate (see the
--   -- `Quantifiers` module) — but the bare macro below still fails.
--   instM : ((x : D) → P x) → P a
--   instM = firstorder
--
--   -- Limitation 3 (∃-introduction under plain `firstorder`): dually, a witness
--   -- `P a` is not recognised as evidence for `∃ P` by the bare macro. `firstorderQ`
--   -- handles it; the line below uses `firstorder`, so it fails.
--   intro-∃ : P a → ∃ P
--   intro-∃ = firstorder
--
--   -- Limitation 3 (no theory of equality beyond the oracles): the refl oracle
--   -- discharges reflexive leaves (see `refl-goal` above), but there is no theory
--   -- relating *distinct* equality atoms, so symmetry — `u ≡ v` and `v ≡ u` are
--   -- two unrelated atoms — is still out of reach.
--   ≡-sym : u ≡ v → v ≡ u
--   ≡-sym = firstorder
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
