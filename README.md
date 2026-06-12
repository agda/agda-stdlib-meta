## agda-stdlib-meta: Meta-programming utilities for Agda [![CI](https://github.com/agda/agda-stdlib-meta/workflows/CI/badge.svg)](https://github.com/agda/agda-stdlib-meta/actions)

Browse the Agda code in HTML [here](https://agda.github.io/agda-stdlib-meta).

## Version compatibility

We mirror the version numbers of [agda-stdlib](https://github.com/agda/agda-stdlib).

| **agda** | **agda-stdlib** | **agda-stdlib-classes** | **agda-stdlib-meta** |
|----------|-----------------|-------------------------|-----------------|
| [v2.6.3](https://github.com/agda/agda/releases/tag/v2.6.3) | [v1.7.2](https://github.com/agda/agda-stdlib/releases/tag/v1.7.2) | [v1.7.2](https://github.com/agda/agda-stdlib-classes/releases/tag/v1.7.2) | [v1.7.2](https://github.com/agda/agda-stdlib-meta/releases/tag/v1.7.2) |
| [v2.6.4](https://github.com/agda/agda/releases/tag/v2.6.4) | [v1.7.3](https://github.com/agda/agda-stdlib/releases/tag/v1.7.3) | [v1.7.3](https://github.com/agda/agda-stdlib-classes/releases/tag/v1.7.3) | [v1.7.3](https://github.com/agda/agda-stdlib-meta/releases/tag/v1.7.3) |
| [v2.6.4](https://github.com/agda/agda/releases/tag/v2.6.4) | [v2.0](https://github.com/agda/agda-stdlib/releases/tag/v2.0) | [v2.0](https://github.com/agda/agda-stdlib-classes/releases/tag/v2.0) | [v2.0](https://github.com/agda/agda-stdlib-meta/releases/tag/v2.0) |
| [v2.6.4](https://github.com/agda/agda/releases/tag/v2.6.4) | [v2.1](https://github.com/agda/agda-stdlib/releases/tag/v2.1) | [v2.1](https://github.com/agda/agda-stdlib-classes/releases/tag/v2.1) | [v2.1](https://github.com/agda/agda-stdlib-meta/releases/tag/v2.1) |
| [v2.7.0](https://github.com/agda/agda/releases/tag/v2.7.0) | [v2.1.1](https://github.com/agda/agda-stdlib/releases/tag/v2.0) | [v2.1.1](https://github.com/agda/agda-stdlib-classes/releases/tag/v2.1.1) | [v2.1.1](https://github.com/agda/agda-stdlib-meta/releases/tag/v2.1.1) |
| [v2.7.0.1](https://github.com/agda/agda/releases/tag/v2.7.0.1) | [v2.2](https://github.com/agda/agda-stdlib/releases/tag/v2.2) | [v2.2](https://github.com/agda/agda-stdlib-classes/releases/tag/v2.2) | [v2.2](https://github.com/agda/agda-stdlib-meta/releases/tag/v2.2) |
| [v2.8.0](https://github.com/agda/agda/releases/tag/v2.8.0) | [v2.3](https://github.com/agda/agda-stdlib/releases/tag/v2.3) | [v2.3](https://github.com/agda/agda-stdlib-classes/releases/tag/v2.3) | [v2.3](https://github.com/agda/agda-stdlib-meta/releases/tag/v2.3) |

Minor revisions will append to these major versions (e.g. `v1.7.3b` or `v1.7.3.10`).

## The reflective simplifier (`Tactic.Simp.Reflective`)

`Tactic.Simp.Reflective` is a `simp`-style rewriting tactic: you hand it a
list of equational lemmas (rule names) and it closes the goal by repeatedly
rewriting with them. It is *reflective* — the goal and every rule are
reified into a small first-order expression language and the rewriting search
runs by **evaluation during type-checking** of a verified object-level engine
(`Tactic.Simp.Reflective.Core`, `--safe`).

Four macros are provided:

```agda
-- Propositional equality: rewrite both sides to a common normal form.
_ : ∀ {x y : ℕ} → (x + 0) + y ≡ x + (0 + y)
_ = simp! (quote +-assoc ∷ quote +-identityˡ ∷ quote +-identityʳ ∷ [])

-- Rules drawn from a `Simp D` instance dictionary instead of a literal list.
_ : ∀ {x : ℕ} → x + 0 ≡ x
_ = simpD! ArithRules

-- Like simp!, but also use local hypotheses as rewrite rules.
_ : ∀ {x : ℕ} → (h : x ≡ 0) → x + 0 ≡ 0
_ = λ {x} h → simpH! (quote +-identityʳ ∷ []) (h ∷ [])

-- A non-≡ relation goal: ≡-normalise both sides, then chain the
-- relation's own lemmas, closing with its reflexivity/transitivity.
_ : ∀ {n : ℕ} → n + 0 ≤ 1 + n
_ = simpRel! (quote +-identityʳ ∷ []) (quote n≤1+n ∷ [])
             (mkRelInfo (quote ≤-trans) (quote ≤-refl))
```

**Soundness.** The meta level is never trusted. Matchers and heuristics in
the macro frontend may be wrong, but the only consequences are a type error
or a rule that never fires — every term the macro emits is fully
re-elaborated by Agda, and the rewriting engine is verified by construction.
Notably **no `--lossy-unification`** is required (unlike the older
`Tactic.Simp`). Features include multi-sorted goals, raw polymorphic stdlib
rules (instantiated from the goal), mixed universe levels, and ordered
rewriting for permutative rules (e.g. commutativity, via a termination gate).

**Current limitations.** Performance degrades steeply with large rule sets
(roughly 20+ rules of distinct operators per call becomes expensive; ~50
rules can exhaust the type-checker) — keep rule sets focused. Module-local
relation bundles (e.g. an abstract monoid's `≈`) and conditional rules are
not yet supported.

See [`reflective-simp-plan.md`](reflective-simp-plan.md) for the roadmap,
the migration matrix against the older `Tactic.Simp`, and benchmark numbers;
[`Tactic/Simp/Reflective/NOTES.md`](Tactic/Simp/Reflective/NOTES.md) collects
the macro-layer pitfalls for other tactic authors.
