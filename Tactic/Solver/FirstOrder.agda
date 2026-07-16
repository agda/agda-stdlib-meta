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

open import Data.Bool             using (Bool; true; false; if_then_else_)
open import Data.Empty            using (⊥)
open import Data.List as List     using (List; []; _∷_; length; foldr)
open import Data.Maybe            using (Maybe; just; nothing; from-just)
open import Data.Nat              using (ℕ; zero; suc; _+_)
open import Data.Nat.Reflection   using (toTerm; toFinTerm)
open import Data.Product          using (_×_; _,_; proj₁; proj₂)
open import Data.String           using (String)
open import Data.Sum              using (_⊎_)
open import Data.Unit             using (⊤; tt)
open import Data.Vec.Base as Vec  using (Vec)
open import Level                 using (Level)
open import Function              using (case_of_)
open import Relation.Nullary      using (¬_)

open import Agda.Builtin.Reflection using (Visibility)
open import Reflection
open import Reflection.AST.Argument
open import Reflection.AST.DeBruijn using (strengthen; weaken)
import Reflection.AST.Name as Name
open import Reflection.AST.Term
open import Reflection.TCM.Syntax
open import Reflection.Utils.Args  using (getVisibleArgs)
open import Reflection.Utils.Core  using (insertAtom; findAtomIndex; extractNat)
open import Reflection.Utils.Metas using (firstMeta)

open import Tactic.FirstOrder.Core   using (Formula; atom; ⊤′; ⊥′; _∧′_; _∨′_; _⇒′_; solve)
import Tactic.FirstOrder.Core as Core
open import Tactic.FirstOrder.Decide using (decideFast)
open import Tactic.FirstOrder.Search using (search)

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
  stripQ : Term → List (String × Visibility) × Term
  stripQ t@(pi (arg (arg-info v _) _) (abs s cod)) =
    case strengthen cod of λ where
      nothing  → let bs , body = stripQ cod in (s , v) ∷ bs , body   -- quantifier
      (just _) → [] , t                                              -- implication
  stripQ t = [] , t

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
      Tᵢ   ← inferType (var i [])
      ok   ← isProp Tᵢ
      rest ← go r (suc i)
      pure (if ok then (var (i + nb) [] , weaken nb Tᵢ) ∷ rest else rest)

------------------------------------------------------------------------
-- VII. The macro

private
  -- `nothing` runs the complete fuel-free `decideFast`; `just k` runs the
  -- bounded `search` at fuel `k`. Since `decideFast = search (μ …)`, the two do
  -- identical search work — they differ only in who supplies the fuel ceiling.
  solveFOL : Maybe ℕ → Term → TC ⊤
  solveFOL mfuel hole = do
    -- the goal type as-is: `normalise` would unfold our connectives
    -- (`_×_ ↦ Σ`, `⊥ ↦ Irrelevant Empty`, …)
    goal      ← inferType hole
    let binders , body = stripQ goal     -- strip the universal-quantifier prefix
    -- A function-typed whole-RHS goal whose codomain ignores its domain (`A → ⊤`)
    -- arrives with the domain an unsolved metavariable we cannot pin; reject it
    -- with the workaround rather than a cryptic "unsolved metas".
    _ ← case firstMeta body of λ where
          (just _) → typeError
            ( strErr "firstorder: the goal contains an unsolved metavariable, so it"
            ∷ strErr " cannot be reified. This happens when `firstorder` is the whole"
            ∷ strErr " right-hand side of a function-typed goal whose result ignores"
            ∷ strErr " the argument (e.g. `A → ⊤`). Introduce the argument(s) first,"
            ∷ strErr " e.g. `f x = firstorder`."
            ∷ [])
          nothing  → pure tt
    -- prepend the ambient hypotheses' types as `⇒`-antecedents; the proof of the
    -- resulting closed formula is then applied to the hypothesis variables.
    hyps      ← contextHyps (length binders)
    let hTys  = List.map proj₂ hyps
    atoms     ← collect depth body [] >>= collectList depth hTys
    let `n    = toTerm (length atoms)
    `body     ← reify depth atoms `n body
    `hyps     ← reifyList depth atoms `n hTys
    let `φ    = foldr (fBin (quote _⇒′_) `n) `body `hyps
    let `Γ    = con (quote List.List.[]) (2 ⋯⟅∷⟆ [])
    let `srch = case mfuel of λ where
                  (just fuel) → def (quote search)     (`n ⟅∷⟆ toTerm fuel ⟨∷⟩ `Γ ⟨∷⟩ `φ ⟨∷⟩ [])
                  nothing     → def (quote decideFast) (`n ⟅∷⟆ `Γ ⟨∷⟩ `φ ⟨∷⟩ [])
    let `drv  = def (quote from-just) (2 ⋯⟅∷⟆ `srch ⟨∷⟩ [])
    -- `solve`'s implicits (n, ℓ, φ) are all pinned by the environment and `drv`
    let proof = def (quote solve)  (mkEnv atoms ⟨∷⟩ `drv ⟨∷⟩
                                    List.map (λ h → vArg (proj₁ h)) hyps)
    unify hole (prependLams binders proof)

macro
  -- complete, fuel-free
  firstorder : Term → TC ⊤
  firstorder = solveFOL nothing

  -- with an explicit fuel bound (a ℕ literal)
  firstorderN : Term → Term → TC ⊤
  firstorderN `fuel hole = do
    just fuel ← pure (extractNat `fuel)
      where nothing → typeError (strErr "firstorderN: first argument must be a ℕ literal" ∷ [])
    solveFOL (just fuel) hole
