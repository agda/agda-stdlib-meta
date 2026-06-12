# Reflective simp: roadmap

Status: `Tactic.Simp.Reflective` proves ≡-goals with a single `simp!` call —
multi-sorted, raw polymorphic stdlib rules, verified-by-construction core
(`--safe`, no `--lossy-unification`), 24 tests, ~20 s clean check.

Guiding principle that has paid off twice: the engine never trusts the
meta level. Matchers and heuristics may be wrong; the worst outcome is a
type error or a rule that never fires. Keep every new feature on that side
of the line.

## Phase 0 — Housekeeping (do first, ~an hour)

1. **Commit the spike.** Everything is untracked on the `simp` worktree
   (`Tactic/Simp/Reflective.agda`, `Tactic/Simp/Reflective/Core.agda`,
   the comparison survey, this plan). Two commits: core + frontend.
2. **Add a `_≗_`-stated rule test.** `stripAndReduce` should already unfold
   it (same mechanism as `RightIdentity`); one test to confirm, or a
   small fix if not.
3. **Decide the fate of `Tactic.Simp.Witness`.** Superseded as an engine;
   its `Chain` algebra may be worth keeping for Phase 2's relation
   chaining. Recommendation: keep the module, retire its `SimpSetup`/
   `greedy` half once Phase 2 lands.

## Phase 1 — Ergonomics (low risk, high daily value)

4. **Extensible dictionaries (`simp!` + instance dicts).** Port the
   `Simp D` instance-record pattern from `Tactic.Simp` (`getDictNames`)
   so call sites can say `simpD! ArithRules`. ~30 lines of frontend.
5. **Local hypotheses as rules.** Accept context terms, not just `Name`s:
   a hypothesis `h : x ≡ 0` becomes a ground `Rule` with `sound = λ _ → h`.
   Fixes old simp's limitation #2; small frontend addition (rule
   processing from a `Term` + its inferred type instead of `getType`).
6. **Error quality.** On failure, report the two normal forms the solver
   got stuck at (cheap: they're computable by one more meta-level
   `normalise` of `simplify`-applications, done only on the error path).

## Phase 2 — Coverage (the big usability gaps)

7. **Relation goals (`simpRel!`).** Reproduce old `simpRel` on the new
   engine: (a) ≡-normalise both sides with the verified engine, transport
   along the relation with `subst`, close with `relRefl` — this is pure
   frontend reuse; (b) top-level ~-rule chaining via `relTrans`
   (old Option B) — meta-level chaining first; an object-level typed
   chain (the `Witness.Chain` algebra) is the principled follow-up.
   Unlocks the `≤`/`↭`/monoid-`≈` test families.
8. **Mixed universe levels.** Engine is level-uniform per goal; goals like
   `length xs ≡ n` with `A : Set a` need it. Frontend-only plan: compute
   the max level, `Lift` lower-level sorts, wrap impls with `lift`/`lower`
   (definitional collapse keeps `evalAt` reducing to the goal), emit
   `cong lower` at the end when the goal sort was lifted. No core changes.
   Fiddly; gate behind "all sorts same level → current fast path".

## Phase 3 — Power features

9. **Ordered rewriting (permutative rules).** The Isabelle feature neither
   Lean nor Rocq has, and it's uniquely cheap here: a total order on the
   deep `Expr` gates rule application (apply only if the instantiated rhs
   is strictly smaller). The order is a *heuristic filter* — zero proof
   burden, soundness untouched. Auto-detect permutative rules (lhs/rhs
   equal up to variable permutation) or take a user flag. Makes `+-comm`
   in a rule set terminate with a canonical form, enabling AC-normalising
   rule sets.
10. **Instantiation candidates beyond the goal.** Polymorphic-rule
    instantiation currently scans only goal subterms, so rule A can't
    enable rule B's instantiation post-rewrite. Bounded fixpoint: after
    specialising, add the specialised rules' rhs subterms to the candidate
    pool and re-scan until stable (cap iterations).
11. **Conditional rules — decidable-hypothesis version.** Full Lean-style
    recursive discharge fights the verified-by-evaluation design (the
    condition must be discharged *per match*, i.e. object-level). Scoped
    version that fits: rules `∀ xs → ⌊ P? xs ⌋ ≡ true → lhs ≡ rhs` whose
    side condition is decidable — the engine evaluates the decision
    procedure during matching and threads the proof. Design before
    building; this is the most research-shaped item.

## Phase 4 — Maturation

12. **Performance with realistic rule sets.** Current cost ≈0.3 s per call
    with toy sets. Before scaling: benchmark with 30–100 rules on
    ledger-style goals. If linear scan hurts, add an op-head index over
    rules (object-level map from head index to rule list — the poor man's
    discrimination tree).
13. **Migration.** Port old `Tactic.Simp` test scenarios, benchmark
    head-to-head, then deprecate the `--lossy-unification` simp. Decide
    final module naming (`Tactic.Simp` ← reflective implementation?).
14. **Docs**: README section; note the macro-layer pitfalls (quoteTC
    normalisation, reconstruction, error1-in-do) somewhere discoverable
    for other tactic authors in this repo.

## Suggested order

0 → 4 → 5 → 7 → 9 → 8 → 10 → 6 → 12 → 11 → 13 → 14.

Rationale: 4/5 are quick wins that make `simp!` pleasant to use while the
design is fresh; 7 unlocks the largest blocked test family (relations);
9 is cheap relative to its payoff and differentiates this simplifier;
8 is fiddly frontend work that benefits from accumulated test pressure;
11 last among features because it needs a design round.
