------------------------------------------------------------------------
-- A reflection-based first-order (currently: intuitionistic
-- propositional) logic solver.
--
-- `firstorder` reifies the goal type into a `Formula`, runs the
-- fuel-bounded `search` from `Tactic.FirstOrder.Search`, and — if a
-- derivation is found — interprets it via `Core.solve`. The search is
-- evaluated by Agda's own conversion checker when the emitted term is
-- unified with the hole, so the macro itself only reifies and assembles.
--
-- Shared substrate with `Tactic.Solver.Algebra`/`.Ring`: the α-equality
-- atom table (`Reflection.Utils.Core.insertAtom`/`findAtomIndex`) and the
-- stdlib argument combinators. The macro skeleton differs because the
-- goal here is a whole proposition (not an `LHS ≈ RHS` equation) and the
-- implication connective is a `pi`, not a projected `def`.

{-# OPTIONS --without-K --safe #-}

module Tactic.Solver.FirstOrder where

open import Data.Bool             using (Bool; true; false; if_then_else_; not)
open import Data.Empty            using (⊥)
open import Data.List as List     using (List; []; _∷_; _++_; length; foldr; replicate; filterᵇ)
open import Data.Maybe            using (Maybe; just; nothing; is-just)
open import Data.Nat              using (ℕ; zero; suc; _+_)
open import Data.Nat.Reflection   using (toTerm; toFinTerm)
open import Data.Nat.Show         using (show)
open import Data.Product          using (_×_; Σ; _,_; proj₁; proj₂)
open import Data.String as String using (String)
open import Data.Sum              using (_⊎_)
open import Data.Unit             using (⊤; tt)
open import Data.Vec.Base as Vec  using (Vec)
open import Function              using (case_of_; _$_)
open import Function.Bundles      using (Equivalence; mk⇔)
open import Level                 using (Level; _⊔_; Lift; lift; lower)
open import Relation.Nullary      using (¬_)
open import Relation.Nullary.Decidable using (True; False; toWitness; toWitnessFalse)

open import Class.Decidable       using (_⁇; ¿_¿)  -- brings the decidability instances

open import Agda.Builtin.Reflection using (Visibility; withReduceDefs; runSpeculative; solveInstanceConstraints)
open import Agda.Builtin.Equality   using (_≡_; refl)
open import Reflection
open import Reflection.AST.Argument
open import Reflection.AST.DeBruijn using (strengthen; weaken)
import Reflection.AST.Name as Name
open import Reflection.AST.Term
open import Reflection.TCM.Syntax
open import Reflection.Utils.Args  using (getVisibleArgs; vArgs)
open import Reflection.Utils.Core  using (insertAtom; findAtomIndex; extractNat)
open import Reflection.Utils.Metas using (firstMeta; findMetas)

open import Tactic.FirstOrder.Core   using (Formula; atom; ⊤′; ⊥′; _∧′_; _∨′_; _⇒′_; solve)
import Tactic.FirstOrder.Core as Core
open import Tactic.FirstOrder.Decide using (decideFast)
open import Tactic.FirstOrder.Search using (search)
open import Tactic.Solver.Ring        using (solve-≈-macro)
open import Tactic.Constrs            using (tryConstrsᵗ)
open import Tactic.Defaults                                  -- TCOptions instance for `tryConstrsᵗ`

------------------------------------------------------------------------
-- Lemma tuple for `firstorderWith`: a right-nested *non-dependent* pair, so
-- several lemmas of different types (and even different universe levels) can be
-- passed as `p ◂ q ◂ r`. A non-dependent pair avoids the metavariable that a
-- `Σ`/`_,_` tuple would leave (its second component type is dependent), and
-- stays in `Set` (level = ⊔ of the parts) rather than needing `Setω`.

infixr 5 _◂_
record LemmaTuple {a b} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  constructor _◂_
  field fst : A ; snd : B

------------------------------------------------------------------------
-- I. Connective recognition

private
  data Conn : Set where andC orC : Conn

  -- `_×_` ↦ ∧, `_⊎_` ↦ ∨; anything else is not a binary connective.
  connOf : Name → Maybe Conn
  connOf nm =
    if nm Name.≡ᵇ quote _×_ then just andC
    else if nm Name.≡ᵇ quote _⊎_ then just orC
    else nothing

  isBot isTop isNeg : Name → Bool
  isBot nm = nm Name.≡ᵇ quote ⊥
  isTop nm = nm Name.≡ᵇ quote ⊤
  isNeg nm = nm Name.≡ᵇ quote ¬_   -- `¬ A` ↦ `A ⇒′ ⊥′`

  -- The recognised connectives. Fed to `withReduceDefs` (block-list mode) so the
  -- goal can be normalised *without* unfolding them: a definitional alias of a
  -- connective then reduces down to the connective itself, while the connective
  -- stays put (rather than unfolding `_×_ ↦ Σ`, `⊥ ↦ ⊥-poly`, …).
  connNames : List Name
  connNames = quote _×_ ∷ quote _⊎_ ∷ quote ⊤ ∷ quote ⊥ ∷ quote ¬_ ∷ []

------------------------------------------------------------------------
-- II. `Formula` Term builders. `Formula` has a single parameter `n`,
-- supplied as a leading hidden argument to each constructor.

private
  fTop fBot : Term → Term
  fTop `n = con (quote ⊤′) (`n ⟅∷⟆ [])
  fBot `n = con (quote ⊥′) (`n ⟅∷⟆ [])

  fBin : Name → Term → Term → Term → Term
  fBin c `n x y = con c (`n ⟅∷⟆ x ⟨∷⟩ y ⟨∷⟩ [])

  fAtom : Term → ℕ → Term
  fAtom `n i = con (quote atom) (`n ⟅∷⟆ toFinTerm i ⟨∷⟩ [])

------------------------------------------------------------------------
-- III. Reification. `classify` recognises one connective layer; `collect`
-- (which builds the α-deduplicated atom table) and `reify` (which encodes the
-- goal, looking atoms up in that table) both recurse over it, so they cannot
-- drift apart. A visible, non-dependent `pi` is an implication; a dependent
-- one (its bound variable occurs in the codomain) is treated atomically.

private
  data Shape : Set where
    sTop sBot : Shape
    sNeg      : Term → Shape              -- ¬ A
    sBin      : Name → Term → Term → Shape -- ∧/∨/→, tagged with its `Formula` con
    sAtom     : Term → Shape

  classify : Term → Shape
  classify t@(def nm xs) =
    if isBot nm then sBot
    else if isTop nm then sTop
    else if isNeg nm then
      (case getVisibleArgs 1 t of λ where
        (just (a Vec.∷ Vec.[])) → sNeg a
        _                       → sAtom t)
    -- `A × B` of two record types normalises to `Σ A (λ _ → B)` (the `_×_` alias
    -- gets unfolded), so recognise a *non-dependent* `Σ` as `∧`; a genuinely
    -- dependent `Σ` stays an opaque atom.
    else if nm Name.≡ᵇ quote Σ then
      (case getVisibleArgs 2 t of λ where
        (just (a Vec.∷ lam visible (abs _ b) Vec.∷ Vec.[])) →
          (case strengthen b of λ where
            (just b′) → sBin (quote _∧′_) a b′
            nothing   → sAtom t)
        _ → sAtom t)
    else case (connOf nm , getVisibleArgs 2 t) of λ where
      (just andC , just (a Vec.∷ b Vec.∷ Vec.[])) → sBin (quote _∧′_) a b
      (just orC  , just (a Vec.∷ b Vec.∷ Vec.[])) → sBin (quote _∨′_) a b
      _                                            → sAtom t
  classify t@(pi (arg (arg-info visible _) dom) (abs _ cod)) =
    case strengthen cod of λ where
      (just cod') → sBin (quote _⇒′_) dom cod'
      nothing     → sAtom t
  classify t = sAtom t

-- Recursion is bounded by `depth` rather than structural: a connective's
-- operands are recovered through `getVisibleArgs`/`strengthen`, which Agda
-- can't see as subterms. The bound only limits formula *nesting* and is far
-- above anything realistic; on exhaustion the remaining term becomes an atom.
private
  depth : ℕ
  depth = 100000

  collect : ℕ → Term → List Term → TC (List Term)
  collect 0       t acc = pure (insertAtom t acc)
  collect (suc d) t acc = case classify t of λ where
    sTop         → pure acc
    sBot         → pure acc
    (sNeg a)     → collect d a acc
    (sBin _ a b) → collect d a acc >>= collect d b
    (sAtom u)    → pure (insertAtom u acc)

  reify : ℕ → List Term → Term → Term → TC Term
  reify dpt atoms `n = go dpt
    where
    atomT : Term → TC Term
    atomT t = case findAtomIndex t atoms of λ where
      (just i) → pure (fAtom `n i)
      nothing  → typeError (strErr "firstorder: atom not found in table: " ∷ termErr t ∷ [])

    go : ℕ → Term → TC Term
    go 0       t = atomT t
    go (suc d) t = case classify t of λ where
      sTop         → pure (fTop `n)
      sBot         → pure (fBot `n)
      (sNeg a)     → do a′ ← go d a; pure (fBin (quote _⇒′_) `n a′ (fBot `n))
      (sBin c a b) → do a′ ← go d a; b′ ← go d b; pure (fBin c `n a′ b′)
      (sAtom u)    → atomT u

------------------------------------------------------------------------
-- IV. Quantifier prefix.
--
-- A *dependent* leading `pi` (its bound variable occurs in the codomain) is a
-- genuine quantifier: we strip it (this is a selective `stripPis` — stdlib's
-- strips *all* leading pis), reify the body, and re-introduce the binders with
-- stdlib `prependLams` in the proof. A *non-dependent* leading `pi` is an
-- implication and stays in the formula (stripping it would drop the hypothesis,
-- as `solve` proves from the empty context). The body is left in the extended
-- context, so the atom de Bruijn indices line up with the re-introduced λs.

private
  -- Each stripped binder keeps its domain (`Arg Type`) so the oracle phase can
  -- re-enter its context; `prepBinders` recovers what `prependLams` needs.
  stripQ : Term → List (String × Arg Type) × Term
  stripQ t@(pi a (abs s cod)) =
    case strengthen cod of λ where
      nothing  → let bs , body = stripQ cod in (s , a) ∷ bs , body   -- quantifier
      (just _) → [] , t                                             -- implication
  stripQ t = [] , t

  prepBinders : List (String × Arg Type) → List (String × Visibility)
  prepBinders = List.map λ where (s , arg (arg-info v _) _) → s , v

  -- run a TC action in the context extended by the stripped binders, so a leaf's
  -- de Bruijn indices (and any oracle proof of it) line up with the proof's λs
  extendCtx : ∀ {A : Set} → List (String × Arg Type) → TC A → TC A
  extendCtx []            k = k
  extendCtx ((s , a) ∷ bs) k = extendContext s a (extendCtx bs k)

------------------------------------------------------------------------
-- V. Environment: ρ = lookupᴱ ⟨atom₀ , … , atomₙ₋₁⟩ : (i : Fin n) → Set (λs i)
--
-- A `Core.Env` cons-list of the reified atom types. Its index constructs the
-- per-atom level assignment `λs`, so n, λs and ρ are all inferred from the
-- atoms — each atom keeps its own level, and goals may mix levels freely.

private
  mkAtoms : List Term → Term
  mkAtoms []       = con (quote Core.[])  []
  mkAtoms (t ∷ ts) = con (quote Core._∷_) (3 ⋯⟅∷⟆ t ⟨∷⟩ mkAtoms ts ⟨∷⟩ [])

  mkEnv : List Term → Term
  mkEnv atoms = def (quote Core.lookupᴱ) (2 ⋯⟅∷⟆ mkAtoms atoms ⟨∷⟩ [])

------------------------------------------------------------------------
-- VI. Ambient hypotheses
--
-- A local variable `h : T` is a usable propositional hypothesis; a type
-- variable like `A : Set` is an atom, not a hypothesis. We prepend the former
-- to the goal as `⇒`-antecedents, prove the resulting closed formula, and apply
-- the proof to the actual variables — so no new soundness lemma is needed, only
-- a bigger `solve` call.

private
  -- A local variable is a usable hypothesis unless its type is *itself a
  -- universe* `Set _` — a type variable (`A : Set ℓ`), which forms atoms rather
  -- than being one — or `Level`, whose values can never discharge a goal.
  -- Everything else qualifies at any level: `h : A` (A : Set ℓ), `f : A → B`,
  -- `n : ℕ`, …. Including a redundant hypothesis only ever weakens the sequent,
  -- so this never changes which goals are provable; the heterogeneous
  -- environment admits a hypothesis at any level directly.
  isProp : Term → TC Bool
  isProp T = check <$> normalise T
    where
    check : Term → Bool
    check (agda-sort _)         = false
    check (def (quote Level) _) = false
    check _                     = true

  -- `collect`/`reify` lifted over a list of terms
  collectList : ℕ → List Term → List Term → TC (List Term)
  collectList d []       acc = pure acc
  collectList d (t ∷ ts) acc = collect d t acc >>= collectList d ts

  reifyList : ℕ → List Term → Term → List Term → TC (List Term)
  reifyList d atoms `n []       = pure []
  reifyList d atoms `n (t ∷ ts) = do
    t′  ← reify d atoms `n t
    ts′ ← reifyList d atoms `n ts
    pure (t′ ∷ ts′)

  -- the propositional ambient hypotheses, as (variable , type) pairs, with the
  -- type weakened past the `nb` λ-binders the proof will sit under.
  contextHyps : ℕ → TC (List (Term × Term))
  contextHyps nb = length <$> getContext >>= λ n → go n 0
    where
    go : ℕ → ℕ → TC (List (Term × Term))
    go zero    _ = pure []
    go (suc r) i = do
      Tᵢ   ← inferType (var i []) >>= normalise   -- under the caller's `withReduceDefs`
      ok   ← isProp Tᵢ
      rest ← go r (suc i)
      pure (if ok then (var (i + nb) [] , weaken nb Tᵢ) ∷ rest else rest)

  -- A hypothesis of record type is also usable through its fields: `e : A ⇔ B`
  -- yields `Equivalence.to e : A → B` (and `from`, …), and `e : ∃ P` yields
  -- `proj₁ e` and `proj₂ e : P (proj₁ e)` — record elimination, and in
  -- particular ∃-elimination, for free. One level deep; the projected types
  -- re-enter the formula like any hypothesis, so an implication field becomes
  -- a usable ⇒-antecedent rather than part of an opaque atom.
  projectHyps : List (Term × Term) → TC (List (Term × Term))
  projectHyps []               = pure []
  projectHyps ((pf , ty) ∷ hs) = do
    here ← case ty of λ where
      (def nm _) → catchTC
        (getDefinition nm >>= λ where
          (record-type _ fs) → projs fs
          _                  → pure [])
        (pure [])
      _ → pure []
    rest ← projectHyps hs
    pure (here ++ rest)
    where
    projs : List (Arg Name) → TC (List (Term × Term))
    projs []       = pure []
    projs (f ∷ fs) = do
      rest ← projs fs
      catchTC
        (do let p = def (unArg f) (vArg pf ∷ [])
            fty ← inferType p >>= normalise
            ok  ← isProp fty
            pure (if ok then (p , fty) ∷ rest else rest))
        (pure rest)

------------------------------------------------------------------------
-- VII. Leaf oracles
--
-- The propositional engine treats every leaf as an opaque atom. An oracle is a
-- side procedure that may *prove* a leaf outright (e.g. reflexivity of `_≡_`).
-- A discharged leaf is fed back in exactly as a synthesised hypothesis — same
-- channel as ambient hypotheses, only its proof term is the oracle's result
-- rather than a context variable — so the trusted core is untouched. Oracles are
-- tried in order (`defaultOracles`): reflexivity of `_≡_`, then any decidable
-- proposition that holds. Further oracles (e.g. the ring solver) slot in here.

private
  -- Given a leaf, an oracle may return a synthesised hypothesis `(proof , type)`.
  -- The `type` need not be the leaf itself: the falsity oracle returns `¬ leaf`.
  Oracle : Set
  Oracle = Type → TC (Maybe (Term × Term))

  -- Try alternatives in sequence: keep the first `just`.
  infixr 2 _orElse_
  _orElse_ : {A : Set} → TC (Maybe A) → TC (Maybe A) → TC (Maybe A)
  m orElse k = m >>= λ where
    (just r) → pure (just r)
    nothing  → k

  -- Run `act` speculatively: unless it returns `just`, every typechecking
  -- effect it had (metavariables, constraints) is rolled back, and a failure
  -- becomes `nothing`. `catchTC` alone is not enough: a deferred instance
  -- constraint, or an orphan hole left by a failed sub-solver, would leak past
  -- the caller and only fail at the call site.
  speculate : {A : Set} → TC (Maybe A) → TC (Maybe A)
  speculate act = runSpeculative ((λ r → r , is-just r) <$> catchTC act (pure nothing))

  -- Accept `pf` as a synthesised hypothesis of type `ty` only once it is fully
  -- resolved: force any deferred instance search, then reject if a
  -- metavariable is left.
  settle : Term → Term → TC (Maybe (Term × Term))
  settle pf ty = do
    solveInstanceConstraints
    pf′ ← normalise pf
    pure $ case firstMeta pf′ of λ where
      (just _) → nothing
      nothing  → just (pf′ , ty)

  -- A synchronous oracle: try `cand` at `ty`; it either checks or fails
  -- immediately, so plain `catchTC` suffices (used for `refl`, which has no
  -- instance arguments to defer).
  trySynAs : Term → Term → TC (Maybe (Term × Term))
  trySynAs cand ty = catchTC (do pf ← checkType cand ty; pure (just (pf , ty)))
                             (pure nothing)

  tryElabAs : Term → Term → TC (Maybe (Term × Term))
  tryElabAs cand ty = speculate (checkType cand ty >>= λ pf → settle pf ty)

  -- Like `tryElabAs`, but elaborates `cand` against a fresh metavariable of type
  -- `ty` and `unify`s the two. For a constructor application with a dependent
  -- field (`_,_ {A}{B} w h` against `Σ D P`), `unify` pins `B` from the known hole
  -- type, whereas `checkType` elaborates the fields bottom-up and is left with the
  -- non-pattern constraint `B w = P w` (an abstract `B` applied to a free variable),
  -- leaking an unsolved metavariable. Used by the ∃-introduction oracle.
  tryUnifyAs : Term → Term → TC (Maybe (Term × Term))
  tryUnifyAs cand ty = speculate (do h ← newMeta ty; unify h cand; settle h ty)

  -- `¬ t` built as the bare function type `t → ⊥` (which is what `¬_` unfolds to):
  -- this avoids an unsolved level metavariable from `¬_`'s implicit, and `reify`
  -- already turns it into `t ⇒′ ⊥′`.
  ¬-of : Term → Term
  ¬-of t = pi (vArg t) (abs "_" (def (quote ⊥) []))

  oracleRefl : Oracle
  oracleRefl t = trySynAs (con (quote refl) []) t

  -- An instance of the leaf's own type, found by instance search.
  byInstance : ∀ {ℓ} {P : Set ℓ} ⦃ p : P ⦄ → P
  byInstance ⦃ p ⦄ = p

  oracleInstance : Oracle
  oracleInstance t = tryElabAs (def (quote byInstance) []) t

  -- Discharge a decidable proposition that holds, via the `Class.Decidable`
  -- instances (`_≤_`, `_<_`, `_≡_` with a `DecEq`, …). The `True ¿ P ¿` proof is
  -- solved by η when the decision is `yes`, so this fails (leaf stays opaque)
  -- exactly when the proposition is false or has no decidability instance.
  byDec : ∀ {ℓ} {P : Set ℓ} ⦃ _ : P ⁇ ⦄ {_ : True ¿ P ¿} → P
  byDec {_} {_} ⦃ _ ⦄ {pr} = toWitness pr

  oracleDec : Oracle
  oracleDec t = tryElabAs (def (quote byDec) []) t

  -- Dually: if the leaf is decidably *false*, synthesise `¬ leaf`. When that leaf
  -- is also a hypothesis the engine derives `⊥` (via `⊃Lat` then `⊥L`), so an
  -- absurd hypothesis proves anything. `False ¿ P ¿` η-solves exactly on a `no`.
  byDecFalse : ∀ {ℓ} {P : Set ℓ} ⦃ _ : P ⁇ ⦄ {_ : False ¿ P ¿} → ¬ P
  byDecFalse {_} {_} ⦃ _ ⦄ {pr} = toWitnessFalse pr

  oracleDecFalse : Oracle
  oracleDecFalse t = tryElabAs (def (quote byDecFalse) []) (¬-of t)

  -- The level-polymorphic units (`Data.Unit.Polymorphic.⊤`, `Data.Empty.
  -- Polymorphic.⊥`) normalise to `Lift ℓ ⊤` / `Lift ℓ ⊥`, which the monomorphic
  -- `⊤′`/`⊥′` of the Core cannot absorb (the interpretation lives in `Set₀`).
  -- Two gated rules restore their logic as leaves: a `Lift ℓ ⊤` leaf is proved
  -- outright (`lift tt`), and a `Lift ℓ ⊥` leaf yields the synthesised
  -- hypothesis `¬ leaf` (via `lower`), from which the engine derives anything.
  oracleLift : Oracle
  oracleLift t@(def nm _) =
    if nm Name.≡ᵇ quote Lift
      then (case getVisibleArgs 2 t of λ where
        (just (_ Vec.∷ def inner _ Vec.∷ Vec.[])) →
          if isTop inner then trySynAs (con (quote lift) (con (quote tt) [] ⟨∷⟩ [])) t
          else if isBot inner then
            trySynAs (lam visible (abs "x" (def (quote lower) (var 0 [] ⟨∷⟩ [])))) (¬-of t)
          else pure nothing
        _ → pure nothing)
      else pure nothing
  oracleLift _ = pure nothing

  -- Run a whole sub-tactic on a fresh hole of the leaf's type, keeping the *raw*
  -- result: such proofs carry obligations Agda discharges at the enclosing
  -- `unify`, so `settle`'s meta-freeness check would wrongly reject them.
  -- `speculate` still rolls the orphan hole back when the sub-tactic fails.
  viaTactic : (Term → TC ⊤) → Type → TC (Maybe (Term × Term))
  viaTactic tac t = speculate (do h ← newMeta t; tac h; pure (just (h , t)))

  -- Discharge an *equational* leaf `lhs ≡ rhs` with the ring solver over the
  -- bundle `R` (a `CommutativeSemiring`/`CommutativeRing`). Gated to `_≡_` so
  -- the heavy solver isn't run on every atom (and so it composes with rings
  -- whose `_≈_` is `_≡_`); supplied by `firstorderR`, since the bundle cannot
  -- be inferred from the goal.
  oracleRing : Term → Oracle
  oracleRing R t@(def nm _) =
    if nm Name.≡ᵇ quote _≡_ then viaTactic (solve-≈-macro R) t else pure nothing
  oracleRing _ _ = pure nothing

  -- Discharge a leaf by recursive constructor search (`Tactic.Constrs`, to depth
  -- `n`): inductively-defined propositions like `0 ≤ n`, `Even 4`, `x ∈ xs`. It
  -- will inhabit *any* constructor-solvable leaf (including data types, e.g.
  -- `ℕ ↦ 0`), so it is opt-in via `firstorderC` rather than always on.
  oracleConstrs : ℕ → Oracle
  oracleConstrs n = viaTactic (tryConstrsᵗ n)

  -- (∀-elimination and ∃-introduction are recursive oracles defined after
  -- `solveBody`, since they call it on sub-obligations: `oracleInstRec` /
  -- `oracleExistsRec`.)

  -- The always-on oracles. `firstorderR` adds `oracleRing` on top.
  defaultOracles : List Oracle
  defaultOracles =
    oracleRefl ∷ oracleInstance ∷ oracleDec ∷ oracleDecFalse ∷ oracleLift ∷ []

  tryOracles : List Oracle → Type → TC (Maybe (Term × Term))
  tryOracles []       t = pure nothing
  tryOracles (o ∷ os) t = o t orElse tryOracles os t

  -- the synthesised (proof , type) hypotheses an oracle list discharges
  oracleHyps : List Oracle → List Term → TC (List (Term × Term))
  oracleHyps os []       = pure []
  oracleHyps os (t ∷ ts) = do
    rest ← oracleHyps os ts
    tryOracles os t >>= λ where
      (just r) → pure (r ∷ rest)
      nothing  → pure rest

------------------------------------------------------------------------
-- VIII. The solver core

private
  -- Split a `_◂_`-tuple `t₁ ◂ … ◂ tₙ` into its element Terms (a lone non-`◂`
  -- term is a single lemma); used by `firstorderWith`. The pair is non-dependent
  -- so the lemmas may be heterogeneous / multi-level. (`getVisibleArgs` only
  -- handles `def`, so we read the `con`'s visible args with `vArgs`; the
  -- recursion is fuel-bounded as the tail is not a structural subterm.)
  parseLemmas : ℕ → Term → List Term
  parseLemmas (suc d) t@(con c args) =
    if c Name.≡ᵇ quote _◂_
      then (case vArgs args of λ where
              (h ∷ rest ∷ _) → h ∷ parseLemmas d rest
              _              → t ∷ [])
      else t ∷ []
  parseLemmas _ t = t ∷ []   -- a single lemma (non-`◂`), or fuel exhausted

  -- User lemmas as (proof , type) hypotheses, weakened past the `nb` binders the
  -- proof will sit under (the terms are given in the goal's local context).
  lemmaHyps : ℕ → List Term → TC (List (Term × Term))
  lemmaHyps nb []       = pure []
  lemmaHyps nb (l ∷ ls) = do
    T    ← inferType l >>= normalise
    rest ← lemmaHyps nb ls
    pure ((weaken nb l , weaken nb T) ∷ rest)

  -- The unprovability report: definitive for the fuel-free decider (the engine
  -- is complete for IPL), qualified for fuel-bounded `search`. The atom table is
  -- printed because the second failure mode users hit is two leaves they expect
  -- to coincide being reified as *distinct* atoms (not syntactically equal after
  -- normalisation) — listing the atoms makes that visible at a glance.
  unprovableMsg : Maybe ℕ → List Term → List ErrorPart
  unprovableMsg mfuel atoms =
    strErr (case mfuel of λ where
      nothing  → "firstorder: the goal is not provable in intuitionistic\
                 \ propositional logic over its atoms (the search is complete —\
                 \ more fuel cannot help)."
      (just k) → "firstorderN: no proof found within fuel "
                   String.++ show k
                   String.++ " (the fuel-free `firstorder` is complete).")
    ∷ strErr "\nDistinct atoms seen (a leaf you expected to match another may\
             \ differ syntactically):"
    ∷ go 0 atoms
    where
    go : ℕ → List Term → List ErrorPart
    go _ []       = []
    go i (t ∷ ts) = strErr ("\n  [" String.++ show i String.++ "]  ")
                  ∷ termErr t ∷ go (suc i) ts

  -- Build a *proof term* for an already-normalised `goal` (stated in the caller's
  -- `withReduceDefs` context), discharging leaves with the oracles `oraclesOf`
  -- builds from the (weakened) lemma proof terms — they are an input here because
  -- the quantifier oracles also *instantiate* the lemmas (`scanCtx` candidates),
  -- and the weakening depends on the binder prefix only `solveBody` knows. This
  -- is the core shared by the macro entry points (`solveFOL`, below) and the
  -- quantifier oracles' `subSolve`, which calls it on sub-obligations.
  -- `nothing` for the fuel runs the complete `decideFast`; `just k` runs the
  -- bounded `search` at fuel `k` (`decideFast = search (μ …)`, identical work).
  solveBody : (List Term → List Oracle) → List Term → Maybe ℕ → Term → TC Term
  solveBody oraclesOf lemmas mfuel goal = do
    let binders , body = stripQ goal     -- strip the universal-quantifier prefix
    -- prepend the ambient hypotheses' types as `⇒`-antecedents; the proof of the
    -- resulting closed formula is then applied to the hypothesis variables.
    hyps      ← contextHyps (length binders)
    uHyps     ← lemmaHyps (length binders) lemmas
    -- field projections of record-typed hypotheses (already stated in the
    -- binder-extended context, so no further weakening)
    pHyps     ← extendCtx binders (projectHyps (hyps ++ uHyps))
    let baseHyps = hyps ++ uHyps ++ pHyps
    let hTys  = List.map proj₂ baseHyps
    atoms     ← collect depth body [] >>= collectList depth hTys
    -- discharge what the oracles can; their proofs join the ambient hypotheses.
    -- `withReduceDefs (false , [])` undoes the connective blocking *for the oracle
    -- elaboration*: the falsity oracle's `¬ P` target must reduce to `P → ⊥`.
    -- The always-on oracles see every atom (the falsity/lift rules act on
    -- *hypothesis* atoms). The extra oracles — quantifier instantiation, ring,
    -- constructor search — only see atoms that are not already hypotheses or
    -- default-discharged: they could only re-prove those redundantly, and the
    -- pruning is what keeps the recursive quantifier oracles linear along a
    -- lemma chain instead of re-searching every hypothesis atom at every level.
    oHyps     ← extendCtx binders
                  (withReduceDefs (false , []) (do
                    dHyps ← oracleHyps defaultOracles atoms
                    let covered = hTys ++ List.map proj₂ dHyps
                    let rest    = filterᵇ
                          (λ a → not (is-just (findAtomIndex a covered))) atoms
                    -- instantiation candidates: the lemmas and the record-field
                    -- projections (so e.g. `proj₂ e : P (proj₁ e)` can pin an
                    -- instantiation's witness — ∃-elimination)
                    eHyps ← oracleHyps (oraclesOf (List.map proj₁ (uHyps ++ pHyps))) rest
                    pure (dHyps ++ eHyps)))
    let allHyps = baseHyps ++ oHyps
    let `n    = toTerm (length atoms)
    `body     ← reify depth atoms `n body
    `hyps     ← reifyList depth atoms `n (List.map proj₂ allHyps)
    let `φ    = foldr (fBin (quote _⇒′_) `n) `body `hyps
    let `Γ    = con (quote List.List.[]) (2 ⋯⟅∷⟆ [])
    let `srch = case mfuel of λ where
                  (just fuel) → def (quote search)     (`n ⟅∷⟆ toTerm fuel ⟨∷⟩ `Γ ⟨∷⟩ `φ ⟨∷⟩ [])
                  nothing     → def (quote decideFast) (`n ⟅∷⟆ `Γ ⟨∷⟩ `φ ⟨∷⟩ [])
    -- Run the decision procedure *now* (the formula is closed, so this is pure
    -- computation) and embed the found derivation directly: an unprovable goal
    -- gets a real error instead of `from-just` dying at conversion time, and a
    -- provable one re-checks the (small) derivation rather than re-running the
    -- search.
    `drv  ← normalise `srch >>= λ where
      (con (quote just) args) → case vArgs args of λ where
        (d ∷ _) → pure d
        _       → typeError (strErr "firstorder: malformed search result" ∷ [])
      (con (quote nothing) _) → typeError (unprovableMsg mfuel atoms)
      r → typeError
        (strErr "firstorder: search did not normalise to a constructor: " ∷ termErr r ∷ [])
    -- `solve`'s implicits (n, ℓ, φ) are all pinned by the environment and `drv`
    let proof = def (quote solve)  (mkEnv atoms ⟨∷⟩ `drv ⟨∷⟩
                                    List.map (λ h → vArg (proj₁ h)) allHyps)
    pure (prependLams (prepBinders binders) proof)

  -- A function-typed whole-RHS goal whose codomain is inhabited *without* the
  -- argument — `A → ⊤`, or a function into an η-record or record product like
  -- `A → S × S` — arrives with the domain an unsolved metavariable we cannot
  -- pin (Agda solves the result by η before the macro runs); reject it with the
  -- workaround rather than a cryptic "unsolved metas".
  guardNoMetas : Term → TC ⊤
  guardNoMetas body = case firstMeta body of λ where
    (just _) → typeError
      ( strErr "firstorder: the goal contains an unsolved metavariable, so it"
      ∷ strErr " cannot be reified. This happens when `firstorder` is the whole"
      ∷ strErr " right-hand side of a function-typed goal whose result can be"
      ∷ strErr " built without the argument (e.g. `A → ⊤`, or a function into an"
      ∷ strErr " η-record). Introduce the argument(s) first, e.g. `f x = firstorder`."
      ∷ [])
    nothing  → pure tt

  -- `lemmas` are extra hypotheses; `extraOf` builds extra oracles from their
  -- (weakened) proof terms.
  solveFOL : List Term → (List Term → List Oracle) → Maybe ℕ → Term → TC ⊤
  solveFOL lemmas extraOf mfuel hole = withReduceDefs (false , connNames) $ do
    -- Normalise with the connectives blocked (see `connNames`), so a goal stated
    -- through definitional aliases unfolds down to recognisable structure.
    goal  ← inferType hole >>= normalise
    _     ← guardNoMetas (proj₂ (stripQ goal))
    proof ← solveBody extraOf lemmas mfuel goal
    unify hole proof

------------------------------------------------------------------------
-- IX. Quantifier oracles (`firstorderQ`)
--
-- The two quantifier oracles discharge a leaf by *instantiating a context
-- hypothesis* and then solving the sub-obligations it leaves with `solveBody`,
-- using a *given* oracle list `sub` for those sub-solves. They are not recursive
-- themselves: the recursion is unrolled by `qExtraAt` below (structural on fuel),
-- so the termination check stays cheap — no mutual block.

private
  -- Solve a sub-obligation `ty` in the current context with the oracle list `sub`.
  subSolve : List Oracle → Type → TC Term
  subSolve sub ty = withReduceDefs (false , connNames) (solveBody (λ _ → sub) [] nothing ty)

  -- Apply a head term to further arguments by extending its spine (lemma
  -- candidates are variables/definitions/constructors; anything else opts out).
  applySpine : Term → List (Arg Term) → Maybe Term
  applySpine (var i as)  bs = just (var i (as ++ bs))
  applySpine (def f as)  bs = just (def f (as ++ bs))
  applySpine (con c as)  bs = just (con c (as ++ bs))
  applySpine (meta x as) bs = just (meta x (as ++ bs))
  applySpine _           _  = nothing

  -- Enumerate candidate instantiations — first the supplied lemma terms
  -- `cands`, then every context variable (innermost first) — each applied to
  -- `k` fresh metavariables for `k < ar`; the first candidate `try` accepts
  -- wins.
  scanCtx : List Term → ℕ → (Term → TC (Maybe (Term × Term))) → TC (Maybe (Term × Term))
  scanCtx cands ar try = goCands cands orElse (length <$> getContext >>= goVar)
    where
    goAr : Term → ℕ → TC (Maybe (Term × Term))
    goAr h zero    = pure nothing
    goAr h (suc k) = (case applySpine h (replicate k (vArg unknown)) of λ where
        (just cand) → try cand
        nothing     → pure nothing)
      orElse goAr h k
    goCands : List Term → TC (Maybe (Term × Term))
    goCands []       = pure nothing
    goCands (c ∷ cs) = goAr c ar orElse goCands cs
    goVar : ℕ → TC (Maybe (Term × Term))
    goVar zero    = pure nothing
    goVar (suc i) = goAr (var i []) ar orElse goVar i

  -- Fill the still-unsolved metavariables of an instantiation. Two phases:
  -- a meta whose type still *mentions* other metas (`h : a < ?j`) is pinned by
  -- direct unification with a candidate, solving the value-metas (`?j`) as a
  -- side effect — this is what lets a transitivity lemma chain without
  -- consuming a quantifier-recursion level (`subSolve` remains the fallback).
  -- The ground-typed rest (the hypothesis arguments proper, `h : P a`) is then
  -- solved with `sub`. Solving a ground value-meta like `?j : ℕ` head-on would
  -- commit to an arbitrary inhabitant; a meta solved along the way is skipped.
  fillMetas : List Term → List Oracle → List Term → TC ⊤
  fillMetas cands sub ms = fillPhase true ms >> fillPhase false ms
    where
    fillPhase : Bool → List Term → TC ⊤
    fillPhase phase []       = pure tt
    fillPhase phase (m ∷ ms) = do
      _ ← normalise m >>= λ where
            m′@(meta _ _) → do
              ty ← inferType m′ >>= normalise
              if (if phase then is-just (firstMeta ty) else not (is-just (firstMeta ty)))
                then (if phase
                  then (scanCtx cands 3 (λ c → tryUnifyAs c ty) >>= λ where
                          (just (pf , _)) → unify m′ pf
                          nothing         → do rp ← subSolve sub ty; unify m′ rp)
                  else (do rp ← subSolve sub ty; unify m′ rp))
                else pure tt
            _ → pure tt        -- solved as a side effect of an earlier fill
      fillPhase phase ms

  -- Elaborate the candidate `cand` against the leaf `t`, discharging whatever
  -- argument metas the leaf does not pin with `fillMetas`; accept if fully
  -- resolved. The work-horse shared by instantiation and introduction.
  tryFill : List Term → List Oracle → Term → Type → TC (Maybe (Term × Term))
  tryFill cands sub cand t = speculate $ do
    pf ← checkType cand t
    pf ← normalise pf
    fillMetas cands sub (findMetas pf)
    settle pf t

  -- ∀-elimination: instantiate a supplied lemma or context hypothesis `f`
  -- applied to fresh metas. `checkType` pins the witnesses the leaf determines;
  -- any remaining argument metas (hypotheses the leaf does not pin) are
  -- discharged by `fillMetas`. `f : ∀ x → P x`, leaf `P a` ↦ `f a`;
  -- `f : ∀ x → P x → Q x`, leaf `Q a` with `p : P a` ↦ `f a p`. Arities 0‥5.
  oracleInstWith : List Term → List Oracle → Oracle
  oracleInstWith cands sub t = scanCtx cands 6 (λ c → tryFill cands sub c t)

  -- ∃-introduction with a sub-solved proof component. For a `Σ D B` leaf it
  -- enumerates a witness `w` from the context and discharges `B w` two ways:
  --   (A) directly, pairing `w` with a context hypothesis `h` (this also pins a
  --       metavariable witness through the predicate's rigid spine, `∃-app`);
  --   (B) by `subSolve`-ing the residual `B w` once `w` is meta-free — so a
  --       compound predicate (`P x × Q x`) is built by the engine and a nested
  --       existential by a deeper ∃ step (when `sub` itself contains this oracle).
  oracleExistsWith : List Term → List Oracle → Oracle
  oracleExistsWith cands sub t@(def nm _) =
    if nm Name.≡ᵇ quote Σ
      then scanCtx cands 3 (λ w → direct w orElse residual w)
      else pure nothing
    where
    pairT : Term → Term → Term
    pairT w h = con (quote _,_) (4 ⋯⟅∷⟆ w ⟨∷⟩ h ⟨∷⟩ [])

    direct : Term → TC (Maybe (Term × Term))
    direct w = scanCtx cands 3 (λ h → tryUnifyAs (pairT w h) t)

    residual : Term → TC (Maybe (Term × Term))
    residual w = speculate $ do
      pm  ← newMeta t
      hM  ← newMeta unknown
      unify pm (pairT w hM)
      res ← inferType hM >>= normalise
      case firstMeta res of λ where
        (just _) → pure nothing
        nothing  → do
          rp ← subSolve sub res
          unify hM rp
          settle pm t
  oracleExistsWith _ _ _ = pure nothing

  -- count the visible arguments of a (constructor's) type
  visibleArity : Name → TC ℕ
  visibleArity c = go <$> getType c
    where
    go : Term → ℕ
    go (pi (arg (arg-info visible _) _) (abs _ b)) = suc (go b)
    go (pi _                            (abs _ b)) = go b
    go _ = 0

  -- The introduction form for a leaf head, if it has a canonical one: the
  -- constructor of a record type, or of a data type with a *unique*
  -- constructor (no choice is made, so this stays predictable). `Σ` is the
  -- ∃-oracle's job (its witness needs enumeration, not a fresh meta), and
  -- `Equivalence` (the head of `_⇔_`) goes through the smart constructor
  -- `mk⇔`, whose congruence fields are `≡.cong` — only `to`/`from` remain.
  introHead : Name → TC (Maybe (Term × ℕ))
  introHead nm =
    if nm Name.≡ᵇ quote Σ then pure nothing
    else if nm Name.≡ᵇ quote Equivalence then pure (just (def (quote mk⇔) [] , 2))
    else catchTC
      (getDefinition nm >>= λ where
        (record-type c _)      → (λ k → just (con c [] , k)) <$> visibleArity c
        (data-type _ (c ∷ [])) → (λ k → just (con c [] , k)) <$> visibleArity c
        _                      → pure nothing)
      (pure nothing)

  -- Introduction: a leaf with a canonical introduction form is proved by
  -- applying it to fresh metas and solving the field obligations like any
  -- instantiation — so `A ⇔ B` becomes the two engine goals `A → B` and
  -- `B → A`, and a single-constructor record is built from its fields.
  oracleIntroWith : List Term → List Oracle → Oracle
  oracleIntroWith cands sub t@(def nm _) = introHead nm >>= λ where
    nothing         → pure nothing
    (just (hd , k)) → case applySpine hd (replicate k (vArg unknown)) of λ where
      (just cand) → tryFill cands sub cand t
      nothing     → pure nothing
  oracleIntroWith _ _ _ = pure nothing

  -- The quantifier oracle stack unrolled to depth `fuel`: at each level the two
  -- oracles get the *next-shallower* stack for their sub-obligations, and at the
  -- bottom (`zero`) sub-obligations see only the default oracles + the engine
  -- (`solveBody` always runs the defaults itself). This single structural
  -- recursion on `fuel` is the only recursion involved, so the termination
  -- check is trivial. `cands` (the supplied lemma terms) flow to every level,
  -- so a lemma can be instantiated by a sub-solve too.
  qExtraAt : List Term → ℕ → List Oracle
  qExtraAt cands zero    = []
  qExtraAt cands (suc f) =
    let sub = qExtraAt cands f
    in oracleInstWith cands sub ∷ oracleExistsWith cands sub
     ∷ oracleIntroWith cands sub ∷ []

------------------------------------------------------------------------
-- X. The macros

private
  -- shared ℕ-literal parsing for the `…N` variants
  litFuel : String → Term → TC ℕ
  litFuel who `fuel = case extractNat `fuel of λ where
    (just fuel) → pure fuel
    nothing     → typeError
      (strErr (who String.++ ": the fuel argument must be a ℕ literal") ∷ [])

macro
  -- complete, fuel-free
  firstorder : Term → TC ⊤
  firstorder = solveFOL [] (λ _ → []) nothing

  -- with an explicit fuel bound (a ℕ literal)
  firstorderN : Term → Term → TC ⊤
  firstorderN `fuel hole = do
    fuel ← litFuel "firstorderN" `fuel
    solveFOL [] (λ _ → []) (just fuel) hole

  -- as `firstorder`, but additionally discharges `_≡_` leaves with the ring
  -- solver over the given bundle `R` (a `CommutativeSemiring`/`CommutativeRing`).
  firstorderR : Term → Term → TC ⊤
  firstorderR R hole = solveFOL [] (λ _ → oracleRing R ∷ []) nothing hole

  -- as `firstorder`, but with extra user-supplied lemmas added to the available
  -- hypotheses. Pass one lemma directly (`firstorderWith p`) or several as a
  -- `_◂_`-tuple (`firstorderWith (p ◂ q ◂ r)`); the lemmas may have different
  -- types and live at different universe levels.
  firstorderWith : Term → Term → TC ⊤
  firstorderWith `lemmas hole = solveFOL (parseLemmas depth `lemmas) (λ _ → []) nothing hole

  -- as `firstorder`, but also discharges leaves by recursive constructor search
  -- (`Tactic.Constrs`) — for inductively-defined propositions (`0 ≤ n`, `Even 4`,
  -- `x ∈ xs`). Opt-in because it will inhabit any constructor-solvable leaf.
  firstorderC : Term → TC ⊤
  firstorderC hole = solveFOL [] (λ _ → oracleConstrs 10 ∷ []) nothing hole

  -- as `firstorder`, but with quantifier reasoning over *context* hypotheses:
  -- ∀-elimination (instantiate `f : ∀ x → P x` to discharge a leaf `P a`) and
  -- ∃-introduction (discharge a `∃ P` leaf from a context proof `p : P a`). In
  -- both the witness is found by unification; the ∀-hypothesis / ∃-witness proof
  -- must be a local argument. Opt-in, as it scans the local context per leaf.
  firstorderQ : Term → TC ⊤
  firstorderQ hole = solveFOL [] (λ ls → qExtraAt ls 2) nothing hole

  -- as `firstorderQ`, but with an explicit quantifier-recursion depth (a ℕ
  -- literal). Each level is one instantiation step whose sub-obligations may
  -- recurse one level shallower, so e.g. chaining a transitivity lemma `n`
  -- times needs depth `n`. Cost grows quickly with depth; the default is 2.
  firstorderQN : Term → Term → TC ⊤
  firstorderQN `fuel hole = do
    fuel ← litFuel "firstorderQN" `fuel
    solveFOL [] (λ ls → qExtraAt ls fuel) nothing hole

  -- `firstorderWith` and `firstorderQ` combined: the supplied lemmas serve both
  -- as extra hypotheses *and* as instantiation candidates for the quantifier
  -- oracles — so a universally quantified lemma need not be instantiated by
  -- hand: `firstorderQWith <-trans` finds `<-trans p q` itself, and chains it
  -- (to the quantifier-recursion depth, here the default 2).
  firstorderQWith : Term → Term → TC ⊤
  firstorderQWith `lemmas hole =
    solveFOL (parseLemmas depth `lemmas) (λ ls → qExtraAt ls 2) nothing hole

  -- as `firstorderQWith` with an explicit quantifier-recursion depth: a chain
  -- of `n` lemma applications needs depth `n`.
  firstorderQNWith : Term → Term → Term → TC ⊤
  firstorderQNWith `fuel `lemmas hole = do
    fuel ← litFuel "firstorderQNWith" `fuel
    solveFOL (parseLemmas depth `lemmas) (λ ls → qExtraAt ls fuel) nothing hole
