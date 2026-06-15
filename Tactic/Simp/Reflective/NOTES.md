# Macro-layer pitfalls — a tactic author's guide

Hard-won lessons from building `Tactic.Simp.Reflective`, written for anyone
writing OTHER reflection-based tactics in this repo. Each item is a trap that
cost real debugging time, with the one-line fix.

## 1. `quoteTC` under `normalisation = false` reifies thunk graphs

The TC default is `normalisation = false`. Quoting a *value* you built lazily
(here: a `Core.Expr`) then reifies its **unevaluated computation graph** as
syntax — astronomically large terms, and a type-checker that appears to hang.

Fix: quote values inside `local (λ env → record env { normalisation = true })
(quoteTC e)`. See `quoteNorm` in `Reflective.agda`. Never meta-`normalise` a
*proof object* you intend to emit (that forces the whole solver at quote time);
only the data you are reflecting.

## 2. Constructor parameters reflect as `unknown` without `reconstruction = true`

Reflected terms drop hidden constructor/level/type arguments by default —
e.g. `List.[]`'s level and element type come back as `unknown`, which breaks
sort inference and any table keyed on the reflected term.

Fix: run the whole tactic body inside
`local (λ env → record env { reconstruction = true })`. See `simpRTactic`.

## 3. `error1` / `error` only in tail position

The TC `error`/`error1` combinators must be the *last* thing on a `do`-branch.
Calling them mid-`do` (and continuing) leaves the result-type meta unsolved and
yields confusing "unsolved metas" errors far from the cause.

Fix: structure branches so the error is the final statement, e.g.
`case … of λ where (just x) → …; nothing → error1 "…"`.

## 4. TC `unify`-with-metas for matching is unpredictable

Using `unify` (with fresh metas standing for pattern variables) to test whether
a rule matches a subterm is unreliable: lossy/eager solving makes spurious
matches, and the framework's `catch` swallows the error *content*, so you can't
even diagnose failures.

Fix: do matching with a **pure syntactic matcher** over reflected `Term`s
(see `matchT`/`matchAs`). A wrong match is then harmless — the emitted rule
just never fires, and the verified core re-checks everything anyway.

## 5. Verification discipline (don't trust the exit code you *think* you saw)

- Run `export LC_ALL=C.UTF-8; agda <file>` **unpiped** and read `$?` directly;
  piping (`agda … | tail`) reports the pipe's exit status, not agda's.
- Delete the relevant `_build/2.8.0/agda/**/<Module>.agdai` before a definitive
  check — a stale interface hides real errors.
- If a run exceeds ~5 min it is almost certainly a hang (usually pitfall #1):
  kill it with `pkill -9 -f "Agda-2.8.0-bin"`. Do **not** `pkill -f "bin/agda"`
  — that matches the wrapper, not the running process, and won't stop it.

## 6. Termination: recurse over the *original* `Args`, not a computed list

Agda's termination checker sees structural recursion on a constructor's
sub-`Args`, but **not** on a list you computed (`filterVisible as`, `subApps
t`, etc.). Recursing on the latter fails termination.

Fix: recurse structurally over the original `Args`/`Term` (see `convArgs`,
which descends the real argument list), or thread an explicit ℕ **fuel**
parameter (see `stripAndReduce`, `unquoteHypList`, the goal-binder loop).

## 7. Name-ambiguity gotchas with the standard import set

With this repo's usual imports several names are ambiguous and must be
qualified, or you get scope/“ambiguous” errors:

- `Data.Nat._≟_`, `Data.Nat._≡ᵇ_`, `Data.List.zipWith` — qualify explicitly.
- `Meta.Prelude` **renames** `Level._⊔_` to `_⊔ˡ_`; use that for level joins.
- Bundle fields like `refl`/`trans`/`sym` clash with `≡`'s; `open … renaming`.

## 8. De Bruijn conventions used by the frontend

Crossing between the goal context and a rule's telescope is the single
trickiest part. The conventions, all visible in `processRuleMono` /
`mkSoundTerm` / `mkImpl`:

- **Telescope vars ↦ pattern indices.** A rule with `d` binders, outermost
  first, maps binder `k` to engine pattern variable `d ∸ 1 ∸ k` (`pats =
  reverse bs`). Goal-context vars in a rule body are at index `≥ d`.
- **`strengthenBy d = mapVars (_∸ d)`** removes the `d` rule binders from a
  term known not to mention them (op implementations, sort types). Always
  guard with a "does it mention a var `< d`?" check (`usesVarBelow`) first.
- **`mapVars suc` under emitted lambdas.** When you wrap a goal-context term
  under a fresh λ (e.g. the `λ τ → …` soundness witness, or a `subst`
  predicate), shift its free vars by one (`map-Args (mapVars suc)`), because
  they are now one binder deeper.
- **`strengthenBy` between contexts vs `mapVars (_+ depth)`.** Call-site
  hypothesis terms are relative to the call site (which *excludes* the ∀-binders
  the tactic strips); shift them *into* the leaf context with
  `mapVars (_+ depth)` (see `simpRGoal`), the mirror image of `strengthenBy`.

When a soundness witness fails to type-check, it is nearly always an
off-by-`d` or a missing `suc`-shift here — re-derive the index by hand against
these four rules before touching anything else.

## Additions from the testing campaign (2026-06-12)

9. **Macro `Term`-arguments are elaborated like `quoteTerm`** — the
   argument expression is type-checked (with a single inferred type)
   before being quoted.  Consequence: a LIST literal of hypotheses
   `(h₁ ∷ h₂ ∷ [])` only elaborates when all hypotheses have the same
   statement.  Use a right-nested PAIR `(h₁ , h₂)` for heterogeneous
   collections — Σ-pairs elaborate each component at its own type.

10. **ℕ numerals have two reflected spellings** — `lit (nat 0)` and
    `con zero []` (likewise `suc (lit n)`), and they are NOT
    α-equal.  Any syntactic matcher must canonicalize one way (see
    `canonNums` in the frontend), or a rule stated with `0` will not
    match a goal written with `zero`.

11. **Re-exported lemmas spell operators as record projections** —
    e.g. `Data.Nat.Properties.⊔-comm` (re-exported through a module
    application) states its operator as `MaxOperator._⊔_ … x y`, not
    `x ⊔ y`.  A syntactic matcher must re-align such heads (one
    `reduce`, guarded so definitional constants the user explicitly
    references stay folded — see `realign`).

12. **Don't render deep terms through the evaluator** — error-path
    pretty-printing of a ~100-node deep-embedding normal form via
    meta-level `normalise` takes minutes (no sharing).  Bound the size
    first and summarize when large.

13. **`noConstraints` is a no-op here; reject undischarged conditions with
    `findMetas`, but resolve instances EXPLICITLY first** — the conditional
    discharge applies the rule to a proof of each premise and then rejects
    the candidate if `findMetas ≢ []` on the elaborated application
    (re-exported by `Reflection.Utils`).  Two pitfalls compound here:
    - When a condition is FALSE the proof's `True (dec …)` argument has type
      `⊥`; Agda does not error, it POSTPONES the unsolved meta (which would
      otherwise leak as a confusing top-level "Unsolved metavariables").
      Keeping it as a `meta` node is exactly why the `findMetas` reject
      works.  `Class.MonadTC.noConstraints` does NOT help force it: it only
      sets an unread `TCEnv.noConstraints` flag (the `MonadTC-TC`/`-TCI`
      instances call the raw `R.checkType` primitive, never the primitive
      `R.noConstraints`).  `inferType` alone is also insufficient — it
      returns the result type without forcing the term's metas; `checkType`
      the application instead.
    - DO NOT discharge by emitting a bare instance-resolved helper (e.g.
      `prove : ⦃ P ⁇ ⦄ {True (dec …)} → P`).  Its `⦃ P ⁇ ⦄` argument is a
      *deferred* instance meta at macro time — it only resolves at the final
      elaboration — so `findMetas` sees it and rejects the rule even for a
      TRUE condition.  This silently disabled the whole by-decision path;
      it went unnoticed because the test operator `_⊓_` computes, so
      `3 ⊓ 5 ≡ 3` closed via the definitional fallback regardless (a real
      by-decision test needs an OPAQUE operator — see `CondTests.agda`).
      Fix: resolve the instance yourself with `findInstances (P ⁇)` and bake
      it in (`toWitness {a? = ¿ P ¿ ⦃ inst ⦄} _`), leaving only the
      `True (dec …)` meta — which eta-solves to `tt` when true and stays the
      `⊥`-meta (correctly rejected) when false.  NB `toWitness` has three
      implicits `{a}{A}{a?}` before its visible argument; the `Dec` goes in
      the third slot.

14. **`getLocalContext` is empty at a macro's call site — use `getContext`
    to reach the caller's hypotheses** — `initTCEnvWithGoal` seeds
    `globalContext` from the real `R.getContext` (the call-site telescope:
    the user's in-scope variables and hypotheses) and starts `localContext`
    `[]`.  `extendContext` only grows `localContext`, so it holds just the
    binders the *macro itself* entered (e.g. ∀-binders stripped off the
    goal).  To discharge a side condition "by assumption" you must scan
    `getContext` (= `localContext ++ globalContext`), which is exactly the
    space `var i` indexes (`var 0` = head = innermost binder).  Scanning
    `getLocalContext` finds nothing for a goal like `∀ {m n} → m ≤ n → …`
    proved by `λ h → simp! …` (there `h` is a *call-site* var, in
    `globalContext`).  Probe with `checkType (var i []) premiseTy` per index
    and take the first that does not throw.
