-- The object-level core of the reflective simplifier (SPIKE, round 2:
-- multi-sorted).
--
-- Nothing here is problem-specific: there is one untyped expression
-- language `Expr` whose operation symbols and sorts are indices into
-- *value-level* tables (a list of pointed types and a list of
-- arity-typed curried implementations), one verified-by-construction
-- rewriting engine (match-then-verify via `eqExpr?`), and one fueled
-- greedy loop.  A macro instantiates the whole thing per goal without
-- declaring any datatypes.
--
-- Multi-sortedness design: expressions are sort-annotated but
-- untyped; evaluation is total thanks to `cast`, which transports
-- between equal sorts and falls back to the sort's designated
-- default element otherwise.  All equations are stated through
--
--   evalAt s ρ e  =  cast (sortOf e) s (eval ρ e)
--
-- quantified over the target sort `s`, which keeps every proof
-- homogeneous (no dependent transports anywhere).  On well-sorted
-- expressions all casts collapse definitionally, so `evalAt` still
-- reduces to the actual goal term — the property the macro relies on.
-- Ill-sorted expressions merely evaluate to defaults and make the
-- tactic fail; they can never make it lie, since every emitted proof
-- is re-checked.
--
-- Remaining restriction: all sorts live at one universe level ℓ.

{-# OPTIONS --safe #-}

module Tactic.Simp.Reflective.Core where

open import Level using (Level; Lift; lift) renaming (suc to ℓsuc)
open import Data.Empty   using (⊥; ⊥-elim)
open import Data.List    using (List; []; _∷_)
open import Data.Bool    using (Bool; true; false)
open import Data.Maybe   using (Maybe; just; nothing)
open import Data.Nat     using (ℕ; zero; suc; _<ᵇ_; _+_)
open import Data.Nat.Properties using (_≟_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Unit    using (⊤; tt)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; subst)

private variable ℓ : Level

----------------------------------------------------------------
-- Sorts as values: a sort is a pointed type (type + default).
----------------------------------------------------------------

Pointed : (ℓ : Level) → Set (ℓsuc ℓ)
Pointed ℓ = Σ (Set ℓ) (λ T → T)

----------------------------------------------------------------
-- Expressions: every node carries its (claimed) sort.  `var` is a
-- rule pattern variable; goal-side expressions are var-free.
----------------------------------------------------------------

data Expr : Set where
  var : (i s : ℕ) → Expr
  op  : (o s : ℕ) → List Expr → Expr

sortOf : Expr → ℕ
sortOf (var _ s)  = s
sortOf (op _ s _) = s

mutual
  eqExpr? : (a b : Expr) → Maybe (a ≡ b)
  eqExpr? (var i s) (var j s′) with i ≟ j | s ≟ s′
  ... | yes refl | yes refl = just refl
  ... | _        | _        = nothing
  eqExpr? (op o s es) (op o′ s′ es′) with o ≟ o′ | s ≟ s′
  ... | yes refl | yes refl with eqExprs? es es′
  ...   | just refl = just refl
  ...   | nothing   = nothing
  eqExpr? (op o s es) (op o′ s′ es′) | _ | _ = nothing
  eqExpr? (var _ _) (op _ _ _) = nothing
  eqExpr? (op _ _ _) (var _ _) = nothing

  eqExprs? : (as bs : List Expr) → Maybe (as ≡ bs)
  eqExprs? []       []       = just refl
  eqExprs? (a ∷ as) (b ∷ bs) with eqExpr? a b
  ... | nothing   = nothing
  ... | just refl with eqExprs? as bs
  ...   | just refl = just refl
  ...   | nothing   = nothing
  eqExprs? []      (_ ∷ _) = nothing
  eqExprs? (_ ∷ _) []      = nothing

----------------------------------------------------------------
-- A boolean strict total order on expressions, used ONLY as a
-- heuristic gate for permutative rules: a permutative rule fires only
-- when it strictly decreases this order.  No properties are proved —
-- it merely restricts *when* a rule applies, so soundness is untouched.
-- Lexicographic: `var` < `op`; then numerically on the head indices;
-- then on the argument list (lexicographic, mutual List version).
----------------------------------------------------------------

-- Node count.  Used as the primary key of `ltExpr` so that a compound
-- subterm is always "larger" than a leaf: this stops a permutative
-- commutativity rule from ever pulling a compound to the front of a
-- right-associated spine (which would create a left-nest the gate then
-- locks in), the key to AC-style convergence.
mutual
  sizeExpr : Expr → ℕ
  sizeExpr (var _ _)  = 1
  sizeExpr (op _ _ es) = suc (sizeExprs es)

  sizeExprs : List Expr → ℕ
  sizeExprs []       = 0
  sizeExprs (e ∷ es) = sizeExpr e + sizeExprs es

mutual
  -- Lexicographic on (size, kind, head index, args).  Size first keeps
  -- leaves below compounds; then `var` < `op`; then numerically on the
  -- head; then on the argument list.
  ltExpr : Expr → Expr → Bool
  ltExpr a b with sizeExpr a ≟ sizeExpr b
  ... | no _  = sizeExpr a <ᵇ sizeExpr b
  ... | yes _ = ltExpr′ a b

  ltExpr′ : Expr → Expr → Bool
  ltExpr′ (var i _)    (var j _)    = i <ᵇ j
  ltExpr′ (var _ _)    (op _ _ _)   = true
  ltExpr′ (op _ _ _)   (var _ _)    = false
  ltExpr′ (op o _ es)  (op o′ _ es′) with o ≟ o′
  ... | yes _ = ltExprs es es′
  ... | no _  = o <ᵇ o′

  ltExprs : List Expr → List Expr → Bool
  ltExprs []       []       = false
  ltExprs []       (_ ∷ _)  = true
  ltExprs (_ ∷ _)  []       = false
  ltExprs (a ∷ as) (b ∷ bs) with eqExpr? a b
  ... | just _  = ltExprs as bs
  ... | nothing = ltExpr a b

----------------------------------------------------------------
-- Substitutions and first-order matching.  Both are sort-guarded:
-- a pattern variable of sort s only binds/substitutes expressions
-- whose sort annotation is s.  `match` itself is unverified;
-- callers re-check with `eqExpr?`.
----------------------------------------------------------------

Subst : Set
Subst = List (ℕ × Expr)

lookupS : Subst → ℕ → Maybe Expr
lookupS []             _ = nothing
lookupS ((j , e) ∷ σ) i with i ≟ j
... | yes _ = just e
... | no _  = lookupS σ i

mutual
  applyS : Subst → Expr → Expr
  applyS σ (var i s) with lookupS σ i
  ... | nothing = var i s
  ... | just e with sortOf e ≟ s
  ...   | yes _ = e
  ...   | no _  = var i s
  applyS σ (op o s es) = op o s (applySs σ es)

  applySs : Subst → List Expr → List Expr
  applySs σ []       = []
  applySs σ (e ∷ es) = applyS σ e ∷ applySs σ es

-- The sort-guards make substitution sort-preserving on variables.
sortOf-applySV : ∀ σ i s → sortOf (applyS σ (var i s)) ≡ s
sortOf-applySV σ i s with lookupS σ i
... | nothing = refl
... | just e with sortOf e ≟ s
...   | yes p = p
...   | no _  = refl

mutual
  match : Expr → Expr → Subst → Maybe Subst
  match (var i s) e σ with sortOf e ≟ s
  ... | no _ = nothing
  ... | yes _ with lookupS σ i
  ...   | nothing = just ((i , e) ∷ σ)
  ...   | just e′ with eqExpr? e e′
  ...     | just _  = just σ
  ...     | nothing = nothing
  match (op o s ps) (op o′ s′ es) σ with o ≟ o′ | s ≟ s′
  ... | yes _ | yes _ = matchs ps es σ
  ... | _     | _     = nothing
  match (op _ _ _) (var _ _) _ = nothing

  matchs : List Expr → List Expr → Subst → Maybe Subst
  matchs []       []       σ = just σ
  matchs (p ∷ ps) (e ∷ es) σ with match p e σ
  ... | just σ′ = matchs ps es σ′
  ... | nothing = nothing
  matchs []      (_ ∷ _) _ = nothing
  matchs (_ ∷ _) []      _ = nothing

----------------------------------------------------------------
-- Closedness (var-freeness).  Goal-side expressions and rules
-- instantiated from the goal are var-free; `eval` of a closed
-- expression is environment-independent (see `eval-closed` below),
-- which lets a conditional step decided at one environment be lifted
-- to all environments.  Closedness is *checked* at firing time with
-- `closed?` rather than tracked as an engine invariant.
----------------------------------------------------------------

mutual
  Closed : Expr → Set
  Closed (var _ _)   = ⊥
  Closed (op _ _ es) = ClosedL es

  ClosedL : List Expr → Set
  ClosedL []       = ⊤
  ClosedL (e ∷ es) = Closed e × ClosedL es

mutual
  closed? : (e : Expr) → Dec (Closed e)
  closed? (var _ _)   = no λ ()
  closed? (op _ _ es) = closedL? es

  closedL? : (es : List Expr) → Dec (ClosedL es)
  closedL? []       = yes tt
  closedL? (e ∷ es) with closed? e | closedL? es
  ... | yes p | yes q = yes (p , q)
  ... | no ¬p | _     = no λ where (p , _) → ¬p p
  ... | _     | no ¬q = no λ where (_ , q) → ¬q q

----------------------------------------------------------------
-- Sort interpretation, casting, and operation types.
----------------------------------------------------------------

module WithSorts {ℓ} (Ts : List (Pointed ℓ)) where

  lookupT : List (Pointed ℓ) → ℕ → Pointed ℓ
  lookupT []       _       = Lift ℓ ⊤ , lift tt
  lookupT (p ∷ _)  zero    = p
  lookupT (_ ∷ ps) (suc i) = lookupT ps i

  ⟦_⟧ : ℕ → Set ℓ
  ⟦ s ⟧ = proj₁ (lookupT Ts s)

  default : (s : ℕ) → ⟦ s ⟧
  default s = proj₂ (lookupT Ts s)

  -- Total coercion: identity on equal sorts, default otherwise.
  cast : (s s′ : ℕ) → ⟦ s ⟧ → ⟦ s′ ⟧
  cast s s′ x with s ≟ s′
  ... | yes refl = x
  ... | no _     = default s′

  cast-refl : ∀ s x → cast s s x ≡ x
  cast-refl s x with s ≟ s
  ... | yes refl = refl
  ... | no ¬p    = ⊥-elim (¬p refl)

  cast-diff : ∀ {s s′} → s ≢ s′ → ∀ x → cast s s′ x ≡ default s′
  cast-diff {s} {s′} ¬p x with s ≟ s′
  ... | yes p = ⊥-elim (¬p p)
  ... | no _  = refl

  -- Curried function type over a list of argument sorts.
  Fun : List ℕ → ℕ → Set ℓ
  Fun []       r = ⟦ r ⟧
  Fun (a ∷ as) r = ⟦ a ⟧ → Fun as r

  -- An operation: (argument sorts, result sort) + implementation.
  Op : Set ℓ
  Op = Σ (List ℕ × ℕ) (λ p → Fun (proj₁ p) (proj₂ p))

----------------------------------------------------------------
-- Evaluation and the verified rewriting engine.
----------------------------------------------------------------

module Eval {ℓ} (Ts : List (Pointed ℓ)) (ops : List (WithSorts.Op Ts)) where

  open WithSorts Ts public

  lookupO : List Op → ℕ → Op
  lookupO []       _       = ([] , 0) , default 0
  lookupO (o ∷ _)  zero    = o
  lookupO (_ ∷ os) (suc i) = lookupO os i

  argSorts : ℕ → List ℕ
  argSorts o = proj₁ (proj₁ (lookupO ops o))

  resSort : ℕ → ℕ
  resSort o = proj₂ (proj₁ (lookupO ops o))

  impl : (o : ℕ) → Fun (argSorts o) (resSort o)
  impl o = proj₂ (lookupO ops o)

  Env : Set ℓ
  Env = (s : ℕ) → ℕ → ⟦ s ⟧

  mutual
    eval : Env → (e : Expr) → ⟦ sortOf e ⟧
    eval ρ (var i s)   = ρ s i
    eval ρ (op o s es) =
      cast (resSort o) s (applyE ρ (argSorts o) (resSort o) (impl o) es)

    -- Evaluate at a requested target sort.
    evalAt : (s : ℕ) → Env → (e : Expr) → ⟦ s ⟧
    evalAt s ρ e = cast (sortOf e) s (eval ρ e)

    applyE : Env → (as : List ℕ) (r : ℕ) → Fun as r → List Expr → ⟦ r ⟧
    applyE ρ []       r v _        = v
    applyE ρ (a ∷ as) r f []       = applyE ρ as r (f (default a)) []
    applyE ρ (a ∷ as) r f (e ∷ es) = applyE ρ as r (f (evalAt a ρ e)) es

  evalAt-cast : ∀ (x : Expr) s′ s ρ
              → sortOf x ≡ s′ → evalAt s ρ x ≡ cast s′ s (evalAt s′ ρ x)
  evalAt-cast x _ s ρ refl =
    cong (cast (sortOf x) s) (sym (cast-refl (sortOf x) (eval ρ x)))

  ----------------------------------------------------------------
  -- Equational steps: target-sort-quantified eval equality.
  ----------------------------------------------------------------

  EStep : Expr → Expr → Set ℓ
  EStep e e′ = ∀ s ρ → evalAt s ρ e ≡ evalAt s ρ e′

  data ESteps : List Expr → List Expr → Set ℓ where
    []  : ESteps [] []
    _∷_ : ∀ {e e′ es es′}
        → EStep e e′ → ESteps es es′ → ESteps (e ∷ es) (e′ ∷ es′)

  eRefl : ∀ e → EStep e e
  eRefl e s ρ = refl

  applyE-cong : ∀ ρ as r (f : Fun as r) {es es′}
              → ESteps es es′ → applyE ρ as r f es ≡ applyE ρ as r f es′
  applyE-cong ρ as       r f []       = refl
  applyE-cong ρ []       r v (p ∷ ps) = refl
  applyE-cong ρ (a ∷ as) r f (_∷_ {e} {e′} {es} {es′} p ps) =
    trans (cong (λ x → applyE ρ as r (f x) es) (p a ρ))
          (applyE-cong ρ as r (f (evalAt a ρ e′)) ps)

  op-cong : ∀ o s {es es′} → ESteps es es′ → EStep (op o s es) (op o s es′)
  op-cong o s ps s′ ρ =
    cong (cast s s′)
      (cong (cast (resSort o) s)
        (applyE-cong ρ (argSorts o) (resSort o) (impl o) ps))

  ----------------------------------------------------------------
  -- Substitution lemma.
  ----------------------------------------------------------------

  substVar : Env → Subst → Env
  substVar ρ σ s i = evalAt s ρ (applyS σ (var i s))

  mutual
    subst-eval : ∀ s ρ σ e
               → evalAt s ρ (applyS σ e) ≡ evalAt s (substVar ρ σ) e
    subst-eval s ρ σ (var i s′)  =
      evalAt-cast (applyS σ (var i s′)) s′ s ρ (sortOf-applySV σ i s′)
    subst-eval s ρ σ (op o s₁ es) =
      cong (cast s₁ s)
        (cong (cast (resSort o) s₁)
          (applyE-subst ρ σ (argSorts o) (resSort o) (impl o) es))

    applyE-subst : ∀ ρ σ as r (f : Fun as r) es
                 → applyE ρ as r f (applySs σ es)
                 ≡ applyE (substVar ρ σ) as r f es
    applyE-subst ρ σ []       r v es       = refl
    applyE-subst ρ σ (a ∷ as) r f []       =
      applyE-subst ρ σ as r (f (default a)) []
    applyE-subst ρ σ (a ∷ as) r f (e ∷ es) =
      trans (cong (λ x → applyE ρ as r (f x) (applySs σ es))
                  (subst-eval a ρ σ e))
            (applyE-subst ρ σ as r (f (evalAt a (substVar ρ σ) e)) es)

  ----------------------------------------------------------------
  -- Rules.  `sound` is stated at the rule's own sort, where all
  -- casts collapse definitionally, so the macro can discharge it by
  -- `λ τ → lemma (τ s₁ i₁) … (τ sₖ iₖ)`.  `soundAt` lifts it to all
  -- target sorts (off-sort, both sides cast to the same default).
  ----------------------------------------------------------------

  record Rule : Set ℓ where
    constructor mkRule
    field
      lhs rhs : Expr
      sEq     : sortOf rhs ≡ sortOf lhs
      sound   : ∀ τ → evalAt (sortOf lhs) τ lhs ≡ evalAt (sortOf lhs) τ rhs
      -- Permutative gate (heuristic, no proof obligation): when `true`,
      -- the rule fires only if its instantiated rhs is strictly smaller
      -- than the matched term in `ltExpr`.  This makes commutativity-
      -- style rules terminate by orienting them towards a canonical form.
      perm    : Bool

  Rules : Set ℓ
  Rules = List Rule

  soundAt : (r : Rule) → EStep (Rule.lhs r) (Rule.rhs r)
  soundAt r s ρ with s ≟ sortOf (Rule.lhs r)
  ... | yes p =
        subst (λ z → evalAt z ρ (Rule.lhs r) ≡ evalAt z ρ (Rule.rhs r))
              (sym p) (Rule.sound r ρ)
  ... | no ¬p =
        trans (cast-diff (λ q → ¬p (sym q)) (eval ρ (Rule.lhs r)))
              (sym (cast-diff (λ q → ¬p (sym (trans (sym (Rule.sEq r)) q)))
                              (eval ρ (Rule.rhs r))))

  ----------------------------------------------------------------
  -- The rewriting engine.
  ----------------------------------------------------------------

  Step : Expr → Set ℓ
  Step e = Σ Expr (λ e′ → EStep e e′)

  -- The verified step produced by a successful match (proof unchanged
  -- regardless of the permutative gate; only *whether* we return it
  -- depends on `perm`).
  mkStep : (r : Rule) (σ : Subst) (e : Expr)
         → applyS σ (Rule.lhs r) ≡ e → Step e
  mkStep r σ e eq =
    applyS σ (Rule.rhs r)
    , λ s ρ → trans (cong (evalAt s ρ) (sym eq))
              (trans (subst-eval s ρ σ (Rule.lhs r))
              (trans (soundAt r s (substVar ρ σ))
              (sym (subst-eval s ρ σ (Rule.rhs r)))))

  tryRule : Rule → (e : Expr) → Maybe (Step e)
  tryRule r e with match (Rule.lhs r) e []
  ... | nothing = nothing
  ... | just σ with eqExpr? (applyS σ (Rule.lhs r)) e
  ...   | nothing = nothing
  ...   | just eq with Rule.perm r
  ...     | false = just (mkStep r σ e eq)
  ...     | true  with ltExpr (applyS σ (Rule.rhs r)) e
  ...       | true  = just (mkStep r σ e eq)
  ...       | false = nothing

  tryRules : Rules → (e : Expr) → Maybe (Step e)
  tryRules []       e = nothing
  tryRules (r ∷ rs) e with tryRule r e
  ... | just s  = just s
  ... | nothing = tryRules rs e

  mutual
    -- One rewrite step anywhere (root first, then leftmost-outermost).
    rewrite₁ : Rules → (e : Expr) → Maybe (Step e)
    rewrite₁ rs e with tryRules rs e
    ... | just s  = just s
    ... | nothing = rewriteSub rs e

    rewriteSub : Rules → (e : Expr) → Maybe (Step e)
    rewriteSub rs (var i s)   = nothing
    rewriteSub rs (op o s es) with rewrites₁ rs es
    ... | nothing        = nothing
    ... | just (es′ , p) = just (op o s es′ , op-cong o s p)

    rewrites₁ : Rules → (es : List Expr)
              → Maybe (Σ (List Expr) (ESteps es))
    rewrites₁ rs []       = nothing
    rewrites₁ rs (e ∷ es) with rewrite₁ rs e
    ... | just (e′ , p) = just (e′ ∷ es , p ∷ eRefls es)
      where
        eRefls : ∀ es → ESteps es es
        eRefls []       = []
        eRefls (e ∷ es) = eRefl e ∷ eRefls es
    ... | nothing with rewrites₁ rs es
    ...   | just (es′ , ps) = just (e ∷ es′ , eRefl e ∷ ps)
    ...   | nothing         = nothing

  -- NB: the recursive result is shared via `with` (a pattern-let
  -- would desugar to two projections of the redex, making the
  -- evaluator recompute the recursion once per projection —
  -- exponential in the length of the rewrite chain).
  simplify : ℕ → Rules → (e : Expr) → Step e
  simplify zero    rs e = e , eRefl e
  simplify (suc n) rs e with rewrite₁ rs e
  ... | nothing       = e , eRefl e
  ... | just (e′ , p) with simplify n rs e′
  ...   | (e″ , q) = e″ , λ s ρ → trans (p s ρ) (q s ρ)

  -- Try reducing rules before permutative ones: a gated permutative
  -- step (e.g. commutativity pulling a unit literal to the front) can
  -- otherwise permanently destroy a redex of an ordinary rule.  Pure
  -- list reordering — soundness is per-rule, so order is free.
  prioritize : Rules → Rules
  prioritize rs = nonPerm rs ++ʳ permOnly rs
    where
      _++ʳ_ : Rules → Rules → Rules
      []       ++ʳ ys = ys
      (x ∷ xs) ++ʳ ys = x ∷ (xs ++ʳ ys)

      nonPerm : Rules → Rules
      nonPerm [] = []
      nonPerm (r ∷ rs) with Rule.perm r
      ... | false = r ∷ nonPerm rs
      ... | true  = nonPerm rs

      permOnly : Rules → Rules
      permOnly [] = []
      permOnly (r ∷ rs) with Rule.perm r
      ... | true  = r ∷ permOnly rs
      ... | false = permOnly rs

  solve : ℕ → Rules → (l r : Expr) → Maybe (EStep l r)
  solve n rs₀ l r with prioritize rs₀
  ... | rs with simplify n rs l | simplify n rs r
  ...   | (l′ , p) | (r′ , q) with eqExpr? l′ r′
  ...     | just eq =
            just (λ s ρ → trans (p s ρ)
                          (trans (cong (evalAt s ρ) eq) (sym (q s ρ))))
  ...     | nothing = nothing

  -- Entry point for the macro: fix the goal sort and use the
  -- defaults environment (goal expressions are var-free).
  ρ₀ : Env
  ρ₀ s _ = default s

  solveAt : (g : ℕ) → ℕ → Rules → (l r : Expr)
          → Maybe (evalAt g ρ₀ l ≡ evalAt g ρ₀ r)
  solveAt g n rs l r with solve n rs l r
  ... | just p  = just (p g ρ₀)
  ... | nothing = nothing

  -- The normal form `simplify` reaches.  Plain (non-proof) helper the
  -- frontend uses ONLY on the failure path, to evaluate the two stuck
  -- sides into a goal-sized term for a better error message.
  normalForm : ℕ → Rules → Expr → Expr
  normalForm n rs e = proj₁ (simplify n (prioritize rs) e)

  -- The verified ≡-step transporting one side of a relation goal to its
  -- engine normal form, at the goal sort, in the defaults environment.
  -- Used by `simpRel!`: the type `evalAt g ρ₀ e ≡ evalAt g ρ₀ (normalForm n rs e)`
  -- reduces (by definitional collapse) to `goalSide ≡ goalSideNF`.
  simplifyEq : (g : ℕ) (n : ℕ) (rs : Rules) (e : Expr)
             → evalAt g ρ₀ e ≡ evalAt g ρ₀ (normalForm n rs e)
  simplifyEq g n rs e = proj₂ (simplify n (prioritize rs) e) g ρ₀

  ----------------------------------------------------------------
  -- Conditional rules.
  --
  -- A `CondRule` is a rule whose soundness is *partial*: `fire τ` returns
  -- `just proof` when the side condition holds at the environment `τ`, and
  -- `nothing` when it does not (so the rule does not fire there).  This is
  -- the verified core of the side-condition feature; the macro frontend
  -- builds `fire` (deciding the condition on the matched values, via a
  -- `Class.Decidable` instance or a context hypothesis).
  --
  -- DESIGN NOTE.  This is the "Closed" variant: we keep the existing
  -- ∀-environment `EStep`/engine and recover the closed-term property that
  -- a conditional step needs by *checking* it at firing time (`closed?`)
  -- and transporting across environments (`eval-closed`).  The alternative
  -- — the design used by the MIT-PLV verified reflective rewriter, where
  -- rules are `option`-returning and the term representation is closed by
  -- construction (so no `eval-closed`/`closed?` is needed) — is documented
  -- in:  Gross, Erbsen, Poddar-Agrawal, Philipoom, Chlipala, "Accelerating
  -- Verified-Compiler Development with a Verified Rewriting Engine", ITP
  -- 2022 (DOI 10.4230/LIPIcs.ITP.2022.17; repo github.com/mit-plv/rewriter,
  -- the `rew_with_opt` rules).  Switch to that if we ever index `Expr` by
  -- its variable context instead of carrying `var`/`Env` openly.
  ----------------------------------------------------------------

  -- `eval` of a closed expression does not depend on the environment.
  -- (`e` is explicit: `Closed` is a reducing function, so the index is not
  -- recoverable from `Closed e` by unification.)
  mutual
    eval-closed : (e : Expr) → Closed e → (ρ ρ′ : Env) → eval ρ e ≡ eval ρ′ e
    eval-closed (var _ _)   ()
    eval-closed (op o s es) cl ρ ρ′ =
      cong (cast (resSort o) s)
        (applyE-closed (argSorts o) (resSort o) (impl o) es cl ρ ρ′)

    evalAt-closed : (e : Expr) → Closed e → (s : ℕ) (ρ ρ′ : Env)
                  → evalAt s ρ e ≡ evalAt s ρ′ e
    evalAt-closed e cl s ρ ρ′ = cong (cast (sortOf e) s) (eval-closed e cl ρ ρ′)

    applyE-closed : ∀ as r (f : Fun as r) es → ClosedL es → (ρ ρ′ : Env)
                  → applyE ρ as r f es ≡ applyE ρ′ as r f es
    applyE-closed []       r v _        _          ρ ρ′ = refl
    applyE-closed (a ∷ as) r f []       _          ρ ρ′ =
      applyE-closed as r (f (default a)) [] tt ρ ρ′
    applyE-closed (a ∷ as) r f (e ∷ es) (ce , ces) ρ ρ′ =
      trans (cong (λ x → applyE ρ as r (f x) es) (evalAt-closed e ce a ρ ρ′))
            (applyE-closed as r (f (evalAt a ρ′ e)) es ces ρ ρ′)

  record CondRule : Set ℓ where
    constructor mkCondRule
    field
      lhs rhs : Expr
      sEq     : sortOf rhs ≡ sortOf lhs
      fire    : (τ : Env)
              → Maybe (evalAt (sortOf lhs) τ lhs ≡ evalAt (sortOf lhs) τ rhs)

  -- Lift a base equality at the rule's own sort to all target sorts —
  -- exactly `soundAt`, but taking the proof as an argument (so it can come
  -- from `fire`) instead of from a `Rule.sound` field.
  csoundAt : (l r : Expr) → sortOf r ≡ sortOf l → (τ : Env)
           → evalAt (sortOf l) τ l ≡ evalAt (sortOf l) τ r
           → ∀ s → evalAt s τ l ≡ evalAt s τ r
  csoundAt l r sEq τ base s with s ≟ sortOf l
  ... | yes p = subst (λ z → evalAt z τ l ≡ evalAt z τ r) (sym p) base
  ... | no ¬p =
        trans (cast-diff (λ q → ¬p (sym q)) (eval τ l))
              (sym (cast-diff (λ q → ¬p (sym (trans (sym sEq) q))) (eval τ r)))

  -- The verified conditional step.  `base` is `fire`'s witness at the
  -- matched environment `substVar ρ₀ σ`; `ecl`/`rcl` witness that the redex
  -- and its replacement are closed.  The proof decides the condition at
  -- `ρ₀` (mirroring `mkStep`) and the two `evalAt-closed` wings transport
  -- that `ρ₀`-equation out to an arbitrary `ρ`, recovering a full `EStep`.
  mkCondStep : (cr : CondRule) (σ : Subst) (e : Expr)
             → applyS σ (CondRule.lhs cr) ≡ e
             → Closed e → Closed (applyS σ (CondRule.rhs cr))
             → evalAt (sortOf (CondRule.lhs cr)) (substVar ρ₀ σ) (CondRule.lhs cr)
             ≡ evalAt (sortOf (CondRule.lhs cr)) (substVar ρ₀ σ) (CondRule.rhs cr)
             → Step e
  mkCondStep cr σ e eq ecl rcl base =
    applyS σ (CondRule.rhs cr)
    , λ s ρ → trans (evalAt-closed e ecl s ρ ρ₀)
              (trans (p₀ s) (evalAt-closed (applyS σ (CondRule.rhs cr)) rcl s ρ₀ ρ))
    where
      p₀ : ∀ s → evalAt s ρ₀ e ≡ evalAt s ρ₀ (applyS σ (CondRule.rhs cr))
      p₀ s = trans (cong (evalAt s ρ₀) (sym eq))
             (trans (subst-eval s ρ₀ σ (CondRule.lhs cr))
             (trans (csoundAt (CondRule.lhs cr) (CondRule.rhs cr) (CondRule.sEq cr)
                       (substVar ρ₀ σ) base s)
                    (sym (subst-eval s ρ₀ σ (CondRule.rhs cr)))))

  -- Try a conditional rule: match, re-check the match, confirm the redex
  -- and replacement are closed, and decide the side condition via `fire`.
  tryRuleC : CondRule → (e : Expr) → Maybe (Step e)
  tryRuleC cr e with match (CondRule.lhs cr) e []
  ... | nothing = nothing
  ... | just σ with eqExpr? (applyS σ (CondRule.lhs cr)) e
  ...   | nothing = nothing
  ...   | just eq with closed? e
                     | closed? (applyS σ (CondRule.rhs cr))
                     | CondRule.fire cr (substVar ρ₀ σ)
  ...     | yes ecl | yes rcl | just base = just (mkCondStep cr σ e eq ecl rcl base)
  ...     | _       | _       | _         = nothing

  ----------------------------------------------------------------
  -- Rule-usage diagnostics (for `simp?`).  This re-runs the SAME
  -- control flow as `simplify`/`rewrite₁`/`tryRules`/`tryRule` but,
  -- instead of building proofs, accumulates the engine indices of the
  -- rules that actually fired (and, for permutative rules, passed the
  -- `ltExpr` gate).  Pure first-order data only — no proof obligations,
  -- so it does not touch the verified engine and keeps `--safe`.
  --
  -- Rules are paired with their ORIGINAL engine index (before
  -- `prioritize` reorders them); the indices returned are these
  -- original positions, so the frontend can map them back to source
  -- names regardless of the `prioritize` shuffle.
  ----------------------------------------------------------------

  IRule : Set ℓ
  IRule = ℕ × Rule

  IRules : Set ℓ
  IRules = List IRule

  -- Attach each rule's position in the original list as its index.
  enumRules : Rules → IRules
  enumRules = go 0
    where
      go : ℕ → Rules → IRules
      go _ []       = []
      go i (r ∷ rs) = (i , r) ∷ go (suc i) rs

  -- `prioritize`, lifted to indexed rules (same reordering; the carried
  -- index travels with each rule, so the original positions survive).
  prioritizeI : IRules → IRules
  prioritizeI rs = nonPerm rs ++ʳ permOnly rs
    where
      _++ʳ_ : IRules → IRules → IRules
      []       ++ʳ ys = ys
      (x ∷ xs) ++ʳ ys = x ∷ (xs ++ʳ ys)

      nonPerm : IRules → IRules
      nonPerm [] = []
      nonPerm (ir ∷ rs) with Rule.perm (proj₂ ir)
      ... | false = ir ∷ nonPerm rs
      ... | true  = nonPerm rs

      permOnly : IRules → IRules
      permOnly [] = []
      permOnly (ir ∷ rs) with Rule.perm (proj₂ ir)
      ... | true  = ir ∷ permOnly rs
      ... | false = permOnly rs

  -- Detection twin of `tryRule`: on a successful (and gated) match it
  -- returns the rule's original index together with the rewritten
  -- expression, mirroring `tryRule`/`mkStep` exactly (it uses the same
  -- `applyS … rhs` as the result so the rewrite chain coincides).
  tryRuleU : IRule → Expr → Maybe (ℕ × Expr)
  tryRuleU (i , r) e with match (Rule.lhs r) e []
  ... | nothing = nothing
  ... | just σ with eqExpr? (applyS σ (Rule.lhs r)) e
  ...   | nothing = nothing
  ...   | just _ with Rule.perm r
  ...     | false = just (i , applyS σ (Rule.rhs r))
  ...     | true  with ltExpr (applyS σ (Rule.rhs r)) e
  ...       | true  = just (i , applyS σ (Rule.rhs r))
  ...       | false = nothing

  tryRulesU : IRules → Expr → Maybe (ℕ × Expr)
  tryRulesU []        e = nothing
  tryRulesU (ir ∷ rs) e with tryRuleU ir e
  ... | just s  = just s
  ... | nothing = tryRulesU rs e

  mutual
    rewrite₁U : IRules → Expr → Maybe (ℕ × Expr)
    rewrite₁U rs e with tryRulesU rs e
    ... | just s  = just s
    ... | nothing = rewriteSubU rs e

    rewriteSubU : IRules → Expr → Maybe (ℕ × Expr)
    rewriteSubU rs (var i s)   = nothing
    rewriteSubU rs (op o s es) with rewrites₁U rs es
    ... | nothing        = nothing
    ... | just (i , es′) = just (i , op o s es′)

    rewrites₁U : IRules → List Expr → Maybe (ℕ × List Expr)
    rewrites₁U rs []       = nothing
    rewrites₁U rs (e ∷ es) with rewrite₁U rs e
    ... | just (i , e′) = just (i , e′ ∷ es)
    ... | nothing with rewrites₁U rs es
    ...   | just (i , es′) = just (i , e ∷ es′)
    ...   | nothing        = nothing

  -- Mirror of `simplify`, threading the set of fired indices.  `acc`
  -- holds the indices seen so far (in reverse-discovery order); the
  -- frontend deduplicates and reorders for display.
  simplifyU : ℕ → IRules → Expr → List ℕ → List ℕ
  simplifyU zero    rs e acc = acc
  simplifyU (suc n) rs e acc with rewrite₁U rs e
  ... | nothing       = acc
  ... | just (i , e′) = simplifyU n rs e′ (i ∷ acc)

  -- The fired-index list for solving `l ≡ r`, mirroring `solve`:
  -- `prioritize` once, then simplify both sides with the same fuel.
  usedRules : ℕ → Rules → (l r : Expr) → List ℕ
  usedRules n rs₀ l r =
    let irs = prioritizeI (enumRules rs₀)
    in simplifyU n irs r (simplifyU n irs l [])

----------------------------------------------------------------
-- Maybe extraction that forces the solver at type-checking time.
----------------------------------------------------------------

From-just : {A : Set ℓ} → Maybe A → Set ℓ
From-just {A = A} (just _)  = A
From-just {ℓ}     nothing   = Lift ℓ ⊤

from-just! : {A : Set ℓ} (m : Maybe A) → From-just m
from-just! (just x) = x
from-just! nothing  = lift tt
