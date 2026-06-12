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

## Performance (item 12)

Standalone benchmark: `Tactic/Simp/Reflective/Bench.agda` (not imported by
anything). Three rule-set sizes and five realistic goals (g1 nested
arithmetic, g2 list, g3 multi-sorted, g4 polymorphic instantiation, g5 deep
arithmetic), each proved once per size, plus an AC goal `gAC`. Cold-cache
wall time of the whole module: **~168 s** (needs `agda +RTS -M11g -RTS` — see
below). Verification was done unpiped, deleting `.agdai` first.

### Per-call attribution (`agda --profile=internal`, `Typing.Reflection` bucket)

Each row is a single `simp!` call in its own module (so the number is pure
per-call macro execution incl. final unify; stdlib deserialization, a fixed
~8–10 s, is excluded). Rule-set sizes shown are the actual ones the module
uses (5 / 8 / 12) plus larger isolated probes:

| call                         | rules | Typing.Reflection |
|------------------------------|------:|------------------:|
| g4 (polymorphic ++-id)       |     1 |            0.31 s |
| g1 nested arith              |     5 |            1.10 s |
| g1 nested arith              |     8 |            3.99 s |
| g1 nested arith              |    12 |           14.3 s  |
| g5 deep arith                |    12 |           17.7 s  |
| g3 multi-sorted              |    15 |           17.7 s  |
| (probe) trivial goal `x≡x`   |     5 |            0.19 s |
| (probe) trivial goal `x≡x`   |    15 |            9.5 s  |
| (probe) trivial goal `x≡x`   |    19 |           21.4 s  |
| (probe) real goal g1         |    19 |           28.2 s  |
| (probe) 50 mixed rules       |    50 |   OOM (killed)    |

### Interpretation

The cost is **dominated by per-call meta-level rule reprocessing**, not the
object-level engine and not enrichment:

* **Trivial-goal probes isolate the rule-processing cost** (object-level
  search does nothing for `x ≡ x`): 19 rules already cost **21.4 s** with a
  trivial goal, vs **28.2 s** with the real g1 goal — so ≥75 % of the time is
  meta-level processing of the rules (`getType` / `stripAndReduce` /
  `inferType >>= normalise` per subterm / `conv` / `quoteNorm`), and the
  object-level `solveAt` evaluation adds only the remainder.
* **The super-linearity is driven by the number of DISTINCT operators**, via
  the O(table) α-equality dedup scans in `addOp`/`addSort` (heavier under
  `reconstruction = true`). Control experiment: **19 rules that all share one
  operator** (`+-identityʳ` ×19, tiny op table) cost **3.8 s**, while 19 rules
  over many operators cost **21 s** — same rule count, ~6× the time.
* **Enrichment is NOT a significant cost.** Disabling the candidate-enrichment
  fixpoint entirely changed Typing.Reflection from 14.5 s → 13.5 s on the
  15-rule g1 case (~1 s, ~7 %), and ~0 on goals with no candidates. So the
  "lazy enrichment" idea from the task would buy almost nothing.
* **The object-level rule scan is cheap** (one `ℕ ≟` on the head per
  non-matching rule), confirmed by the trivial-goal numbers — so an op-head
  index over `Rules` would not help.
* **Commutativity + distributivity in a large set explodes the object-level
  search**: a 17-rule arithmetic set with `+-comm`+`*-comm` OOMs at ~28 s,
  while the same set without comm completes. This is the known-hard AC ×
  distributivity interaction, not a frontend bug; `Bench.agda` therefore keeps
  comm out of the scaling sets and exercises it alone in `gAC`.

### What was optimized: nothing (deliberately)

The profile points at **per-call re-elaboration of every rule's type** as the
hot path. The three fixes the task floated do not apply:

* *Lazy enrichment* — enrichment is ~1 s, not the cost.
* *Cross-call meta caching* — impossible; macros are stateless.
* *Object-level head-index* — the engine scan is already negligible.

The remaining genuine lever (the O(table²) α-dedup in `addOp`/`addSort`) would
require re-keying the shared sort/op tables, whose insertion order is
load-bearing for the de Bruijn indices the emitted terms use — an invasive
change to the reification correctness path. Weakening the `normalise` in
`inferSort` risks fragmenting the sort table (matching silently stops firing).
Neither is a *cheap effective* fix, and realistic call sites use ≤ ~5 rules
(the 53 main-file tests run in ~42 s total, ≈0.3 s/call), so the cost is
acceptable in practice. **Decision: no optimization made; documented the
20-rule soft ceiling / 50-rule OOM cliff as a known limitation instead.**
The `+RTS -M11g` flag is only needed to compile the *benchmark* (16 heavy
calls accumulate proof terms in one module); ordinary use does not need it.

## Migration matrix vs the old `Tactic.Simp` (item 13)

Status of every scenario in the old `Tactic.Simp` test suite under the
reflective implementation. "✓ test" means an equivalent test exists in
`Tactic.Simp.Reflective`; "✓ added" means this work added it.

| old scenario | reflective macro / call shape | status |
|---|---|---|
| `test₁`–`test₁₃` (ℕ ≡-rewriting) | `simp! (quote … ∷ [])` | ✓ test (`t₁`–`t₁₃`) |
| `testBinder₁`–`₃` (∀/implicit/mixed binders) | `simp!` | ✓ test (`tb₁`–`tb₃`) |
| `testDict₁`–`₃` (instance dictionary) | `simpD! ArithRules` | ✓ test (`testDict₁`–`₃`) |
| `testRel₁`–`₆` (≤, Option C: ≡-normalise + relRefl) | `simpRel! eqs [] (mkRelInfo …)` | ✓ test (`testRel₁`–`₆`) |
| `testRelB₁`,`₃` (≤, Option B: n≤1+n chaining) | `simpRel! eqs (quote n≤1+n ∷ []) …` | ✓ test (`testRelB₁`,`₃`) |
| `testRelB₂`,`₄`,`₅`,`₆` (chains; rhs subterm `1+(n+0)` etc.) | `simpRel!` | ✓ added (`testRelB₂`,`₄`,`₅`,`₆`) — the engine ≡-normalises the rhs side too, so the chain connects even when the ~-target carries an un-normalised subterm. (Suspected gap; verified to work.) |
| `testBag₁` (↭, Option C, `xs ++ []`→`xs`) | `simpRel! (quote ++-identityʳ ∷ []) [] …` | ✓ test (`testBag₁`, monomorphic `List ℕ`) |
| `testBag₄` (↭, pure ++-comm ~-step) | `simpRel! [] (quote ↭Prop.++-comm ∷ []) …` | ✓ test (`testBag₄`) |
| `testBag₂` (↭, both sides ≡-normalise) | `simpRel! (++-idˡ ∷ ++-idʳ ∷ []) [] …` | ✓ added (`testBag₂`) |
| `testBag₃` (↭, mixed ≡+~ chain) | `simpRel! (++-idˡ ∷ []) (++-comm ∷ []) …` | ✓ added (`testBag₃`) |
| `testBag₅` (↭, double ≡-normalise + ~-step) | `simpRel! (++-idˡ ∷ ++-idʳ ∷ []) (++-comm ∷ []) …` | ✓ added (`testBag₅`) |
| `testRelDict₁`,`₂` (simpRel from a dictionary) | — | gap — no `simpRelD!` frontend yet; `simpRel!` takes explicit name lists. Trivial to add (mirror `simpD!`'s `getDictNames`); not blocking. |
| `testMonoid₁`–`₄` (abstract monoid `≈`) | — | **open gap (confirmed)** — module-local relation bundles. Verified: `simpRel! [] (quote ∙-identR ∷ []) …` on `x ∙ M-ε ≈ x` fails with `simpRel!: mixed universe levels are unsupported for relation goals`. The carrier `Carrier : Set mc` and the relation `_≈_ : … → Set mℓ` sit at *different module-parameter levels*, which `simpRel!`'s `buildLiftFlags` (deliberately) refuses for relation goals. Needs module-parameter-as-sort + lifted relation-goal handling. Documented, not fixed. |
| Known limitation #1: commutativity diverges | `simp! (quote +-comm ∷ [])` | **now WORKS** — ordered rewriting (item 9) orients `+-comm` via the permutative gate (`ltExpr`). ✓ test (`torder₁`: `x + y ≡ y + x`); AC trio in `torder₂`/`torder₄`, and `gAC` in the bench. This is a *reversal* of the old limitation. |
| Known limitation #2: no local hypotheses | `simpH! names (h ∷ [])` | **now WORKS** — `simpH!` accepts context terms as ground / ∀-carrier rules. ✓ test (`th₁`–`th₄`). |
| Known limitation #3: conditional equations | — | **open gap (confirmed)** — `stripAndReduce` strips all Pi binders including hypothesis arrows, so only unconditional `∀ x… → lhs ≡ rhs` rules work. This is roadmap item 11 (decidable-hypothesis design), deliberately unimplemented. Documented, not fixed. |

Headline: every ℕ/list/≤/↭ rewriting scenario is covered (and two old
*limitations* — commutativity and local hypotheses — now pass); the genuine
remaining gaps are module-local relation bundles (monoid `≈`), conditional
rules, the rhs-non-normalised ~-target case (`testRelB₂/₄/₆`), and a
convenience `simpRelD!`. The old module and its tests are left untouched.

## Next steps (post-roadmap, 2026-06-12)

All four phases of the original roadmap are done (commits 5273694, 2f4638d,
f1e92f7, b78fd0f). What remains, in recommended order:

1. **Table re-keying (performance).** The Phase-4 benchmark shows per-call
   cost is dominated by meta-level rule reprocessing, super-linear in the
   number of *distinct operators* via the O(table) `=α=` dedup scans in
   `addOp`/`addSort` (~20-rule soft ceiling, 50 rules OOM). The fix is to
   key both tables by something cheaper than α-comparison of full terms —
   e.g. bucket by head `Name` first and α-compare only within a bucket.
   Invasive to the de-Bruijn-load-bearing reification path; do it with the
   test suite as a safety net and re-run the bench before/after. This is
   the gating item for Lean-style large default rule sets.
2. **Conditional rules, ground-literal fragment.** Per the Phase-3 design
   analysis: a proof-free `Subst → Bool` gate on rules (reusing the `perm`
   plumbing verbatim — safe by construction since gates only restrict
   firing), with the macro synthesizing the gate from decidable predicates
   over literal-valued matched arguments. The symbolic generalization
   (Env-threaded `csound` + a new Core substitution lemma) is the research
   follow-up.
3. **Monoid-`≈` / module-local relation bundles.** Two sub-problems:
   module-parameter-valued sorts (`Carrier M`) and relation goals whose
   carrier and relation live at different module-parameter levels (needs
   the mixed-level Lift machinery extended to `simpRel!`, or the old
   `modVarFix`-style explicit-prefix emission).
4. **`simpRelD!`** — trivial: mirror `simpD!`'s `getDictNames` for the
   relation macro's two rule lists.
5. **Eta-matching for function atoms.** `length-map`'s specialized pattern
   variable matches the atom `suc` but not `λ x → suc x` (different atom
   keys). Normalising atom keys to eta-short form in `conv` would close
   this.
6. **Verified relation chains.** Replace `simpRel!`'s meta-level
   trans-chaining with the object-level `Witness.Chain` algebra, making
   Option B verified-by-construction like the ≡ engine; then retire the
   unused half of `Tactic.Simp.Witness`.
7. **Retirement decisions (maintainer).** Whether/when to deprecate the
   lossy `Tactic.Simp` and whether the reflective implementation takes
   over the `Tactic.Simp` name; whether the Bench module stays in-repo
   (it needs `+RTS -M11g` and ~164 s, so it should not join any default
   check path).

## Testing campaign findings (2026-06-12)

`Tactic/Simp/Reflective/Tests.agda`: ~50 tests across nine categories
(goal shapes, rule shapes, polymorphic rules, ordered rewriting, local
hypotheses, dictionaries, relation goals, universe levels, longer
rewrites), plus commented-out documented limitations.  Issues found and
fixed during the campaign:

1. `zero`-spelled numerals didn't match literal-stated rules →
   `canonNums` canonicalization at all reifier entry points.
2. No definitional reasoning (`2 + 3 ≡ 5` failed) → failure-path
   fallback, later strengthened to *compose* with rewriting: each side
   is rewritten to its engine normal form and the residual gap is
   closed by a definitional `refl` (`(x + 0) + (2 + 3) ≡ x + 5` works).
3. Error path hung for minutes on diverging rule sets (rendering a
   200-node normal form through the evaluator) → size guard with a
   "diverging rule set?" hint.
4. A gated permutative rule could permanently destroy an ordinary
   rule's redex (comm pulling a unit literal forward before the
   identity rule saw it; rule-order-dependent) → the engine now tries
   non-permutative rules first (`prioritize`, pure reordering).
5. Multiple hypotheses with different statements were impossible to
   pass (macro Term-arguments elaborate like `quoteTerm`; list literals
   force one element type) → `simpH!` accepts right-nested pairs.
6. Rules re-exported through module applications (e.g. `⊔-comm`) spell
   their operator as a record projection and never matched → guarded
   head re-alignment (`realign`).

Remaining documented limitations (commented tests): expanding rules
diverge (clean failure with a hint); rhs-only rule variables never
close; polymorphic hypotheses rejected; conditional rules unsupported
(roadmap item 11).  Pleasant surprises: eta-contraction makes
`λ x → suc x` match a rule about `suc`; instance binders, non-linear
patterns, partial applications, `Set`-valued element types, and
three-level goals all work unchanged.
