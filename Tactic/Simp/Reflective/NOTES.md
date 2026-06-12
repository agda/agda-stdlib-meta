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
