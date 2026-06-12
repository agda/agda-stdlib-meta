# Simplifiers in Rocq (Coq), Lean and Isabelle

A comparative survey of the term-rewriting simplification tactics in the three major proof assistants. Each system has both a **kernel-level reduction** machinery (β/δ/ι/ζ) and a **user-extensible rewriting tactic** built on top of it; the latter is what is usually meant by "the simplifier". They look superficially similar — bottom-up conditional rewriting with a discrimination tree and congruence rules — but they differ in foundations, termination guarantees, customisation, and how aggressively they normalise.

---

## 1. Rocq (Coq)

Rocq has **three** distinct simplification tactics, plus a separate generalised-rewriting framework. They are not interchangeable.

### 1.1 `simpl` — kernel reduction with refolding

`simpl` is the oldest tactic. It performs β/δ/ι/ζ reduction (i.e. unfolds definitions, contracts matches, substitutes lets) but tries to *refold* fixpoints when reduction "got stuck", to avoid spitting out unreadable unfolded `Fix` constructions.

- **Strategy**: head-normal-form-style reduction, then refolding.
- **User control**: `Arguments f /` to allow simplification under specific arguments; `simpl never` to mark constants opaque to it.
- **Weakness**: refolding heuristics surprise users — e.g. `simpl` on `pred (x + y)` typically does nothing useful, while `cbn` reduces it to `x + y - 1`. See [rocq#18576](https://github.com/rocq-prover/rocq/pull/18576) and [rocq#13983](https://github.com/rocq-prover/rocq/issues/13983) for ongoing tweaks.

### 1.2 `cbn` — call-by-name with controllable reduction flags

`cbn` ("call-by-name") was introduced as a more predictable replacement for `simpl`. It is parameterised by which reductions are enabled (`beta`, `delta`, `iota`, `zeta`, `match`, `fix`, `cofix`) and which constants are unfolded.

- **Reference**: Rocq Reference Manual, *Term rewriting and simplification* chapter — https://rocq-prover.org/doc/V8.20.0/refman/proofs/writing-proofs/rewriting.html
- **Internals**: based on a Refolding Algebraic Krivine Abstract Machine (RAKAM); the manual exposes a `cbn` debug flag that prints the machine's progress.
- Like `simpl`, it is purely a *reduction* tactic — it does not consult user-supplied lemmas.

### 1.3 `rewrite` / `setoid_rewrite` — generalised rewriting via type classes

This is the closest analogue to Lean's `simp` or Isabelle's simplifier. It replaces sub-terms using user-supplied equations and (for `setoid_rewrite`) arbitrary user-defined relations.

- **Foundational paper**: Matthieu Sozeau, *A New Look at Generalized Rewriting in Type Theory*, Journal of Formalized Reasoning 2(1), 2009 — https://jfr.unibo.it/article/download/1574/1077/3383
  - Replaces the earlier monolithic algorithm of Sacerdoti Coen (Coq 2004) and Basin (NuPRL 1994).
  - Generates type-class constraints (`Proper`, `subrelation`, `Reflexive`, …) which are discharged by a customisable instance-search procedure.
  - Supports **higher-order morphisms, polymorphism, subrelations, automatic dualisation, rewriting under binders**, all unified via the `Proper`/`respectful` infrastructure.
- **Earlier history**: Lawrence Paulson's "conversions" in Cambridge LCF — combinators for custom rewriting strategies — are cited as the conceptual ancestor.
- **Weakness**: `rewrite` does **not** automatically iterate to fixed point and does **not** maintain a default lemma database (nothing analogous to Lean's `[simp]` or Isabelle's `[simp]`). Users compose `rewrite` calls manually, fall back to `autorewrite` with named hint databases, or rely on third-party plug-ins.

### 1.4 Specialised reflective rewriters

Where Coq lacks a single "throw all simp lemmas at it" tactic, it compensates with verified **reflective** tactics: `ring`, `field`, `lia`, `lra`, `nia`, `psatz`. Each one normalises within a specific algebraic structure and is checked by the kernel via computation.

- Damien Pous, *Tactics for Reasoning modulo AC in Coq*, CPP 2011 — https://arxiv.org/pdf/1106.4448 — describes an OCaml oracle that selects associativity/commutativity rewrites and a kernel-checked verifier. This is the AC-aware extension of `rewrite`.

### 1.5 Documentation

- Rocq Reference Manual, *Generalized rewriting* — https://rocq-prover.org/doc/V8.20.0/refman/addendum/generalized-rewriting.html
- Rocq Reference Manual, *Term rewriting and simplification* — covers `simpl`, `cbn`, `cbv`, `vm_compute`, `native_compute`.

---

## 2. Lean 4

Lean has effectively **one** simplifier — `simp` — together with its definitional sibling `dsimp`, plus user-defined `simproc`s.

### 2.1 `simp`

`simp` is a conditional, bottom-up term-rewriting tactic that consults a user-extensible database (`@[simp]` attribute), uses higher-order pattern matching via discrimination trees, and discharges side conditions by recursively calling itself.

- **Reference manual**: Lean 4 Reference, *The Simplifier* —
  - Invocation: https://lean-lang.org/doc/reference/latest/The-Simplifier/Invoking-the-Simplifier/
  - Configuration: https://lean-lang.org/doc/reference/latest/The-Simplifier/Configuring-Simplification/
  - Simp vs rewrite: https://lean-lang.org/doc/reference/latest/The-Simplifier/Simplification-vs-Rewriting/
- **Source**: `lean4/src/Lean/Elab/Tactic/Simp.lean` and `lean4/src/Lean/Meta/Tactic/Simp/` — https://github.com/leanprover/lean4/blob/master/src/Lean/Elab/Tactic/Simp.lean
- **Key implementation papers**: There is no single "the simp paper" for Lean. The architecture is documented across:
  - The Lean 4 paper: Leonardo de Moura & Sebastian Ullrich, *The Lean 4 Theorem Prover and Programming Language*, CADE 2021 — https://link.springer.com/chapter/10.1007/978-3-030-79876-5_37
  - The Lean community blog post *Fantastic Simprocs and How to Write Them* — https://leanprover-community.github.io/blog/posts/simprocs-tutorial/
  - The `mathlib` "Simp" extras page — https://leanprover-community.github.io/extras/simp.html
  - DeepWiki summary of the simp tactic — https://deepwiki.com/leanprover/lean4/4.1-simplification-(simp)-tactic
- **Variants**:
  - `simp` — full set, rewrites until fixed point or until `maxSteps` (default 100k).
  - `simp only [hs]` — disables the global simp set; uses just the listed lemmas. Recommended for stability.
  - `simp_all` — repeatedly simplifies hypotheses and target until nothing changes.
  - `simpa [hs] using e` — simplifies both the goal and a candidate proof and tries to close.
  - `dsimp` — only definitional rewrites (those provable by `rfl`); never produces a propositional proof obligation.
  - `simp?` — reports the minimal `simp only` call that would suffice (cf. Isabelle's `try0`).
- **Configuration** (rich): `beta`, `eta`, `iota`, `zeta`, `proj`, `decide`, `arith`, `ground`, `contextual`, `unfoldPartialApp`, `failIfUnchanged`, `maxDischargeDepth`, `maxSteps`, `singlePass`, `index`, `implicitDefEqProofs`. The `index := false` switch reproduces the simpler Lean 3 lookup (root-symbol only).
- **Simprocs**: arbitrary Lean meta-functions registered as simp rewriters that produce both a new term and its proof. Used heavily by `grind`, `bv_decide`, `norm_cast`, decimal/numeric normalisation. Tutorial: https://leanprover-community.github.io/blog/posts/simprocs-tutorial/
- **`register_simp_attr`**: lets users define their own named simp sets (e.g. `mfld_simps`, `field_simps` in mathlib).
- **Extensibility**: `simp` reuses **auto-generated congruence lemmas** (`mkCongrSimpForConst?`) to descend into function arguments. Recent releases (4.22–4.28, 2025–2026) have spent considerable engineering effort on optimising this — see for instance Lean 4.23.0 release notes (PRs #9305, #9385, #9293) and 4.28.0 (PRs #11892, #11721) which cut congruence-lemma generation time roughly in half.
- **Mathlib scale**: ~40,000 `[simp]` lemmas as of Feb 2026 (per the mathlib extras page). Lookup is via discrimination trees so cost is sub-linear in the size of the simp set, not linear.
- **Weakness**: Lean's `simp` is famously *not* termination-checked. Users add lemmas that send the rewriter into a loop; the tactic catches this via a step counter. There is no analogue of Isabelle's permutative-rewriting heuristic for AC-like rules; instead, a few hand-coded simprocs and the `grind` tactic cover that ground.

### 2.2 `grind`

A newer (2025+) tactic that combines E-matching, congruence closure, simp-style normalisation and theory propagators. `grind` reuses `simp` internally for its normalisation step and shares the simproc/congruence-lemma machinery. See the Lean 4.23–4.28 release notes for the architectural details — `grind` is to `simp` roughly as Isabelle's `auto` is to `simp`.

### 2.3 LeanSSR

Vladimir Gladshtein, George Pîrlea, Ilya Sergey, *Small Scale Reflection for the Working Lean User*, ITP 2024 — https://arxiv.org/pdf/2403.12733 — describes a port of SSReflect's rewriting style to Lean 4. Notable because it shows how Lean 4's metaprogramming makes the tactic cheap to implement entirely in user space; LeanSSR exposes finer-grained proof-state changes than Coq's SSReflect.

---

## 3. Isabelle

Isabelle's simplifier is the oldest of the three and historically the most influential — both Coq's `setoid_rewrite` and Lean's `simp` cite it as a model.

### 3.1 The simplifier

Bottom-up conditional rewriting, parameterised by a *simpset* (rewrite rules + congruence rules + a "subgoaler" + a "solver" + a "looper"). Crucially, it is built on **higher-order pattern matching** (Miller patterns), which lets it rewrite under binders without the user declaring morphisms.

- **Foundational paper**: Tobias Nipkow, *Equational Reasoning in Isabelle*, Science of Computer Programming 12, 1989 — and *Term Rewriting and Beyond — Theorem Proving in Isabelle*, Formal Aspects of Computing 1(1):320–338, 1989 — https://link.springer.com/article/10.1007/BF01887212
  - Establishes how to lift first-order rewriting to higher-order, conditional rewriting with induction schemata and program-transformation rules.
- **Foundational paper for HOL pattern matching**: Tobias Nipkow, *Functional Unification of Higher-Order Patterns*, LICS 1993 — described in *From LCF to Isabelle/HOL* (Paulson, Nipkow, Wenzel, 2019) https://arxiv.org/pdf/1907.02836 as the basis of Isabelle's rewrite engine.
- **Reference manuals** (the two essential documents):
  - Isabelle/Isar Reference Manual — https://isabelle.in.tum.de/doc/isar-ref.pdf — chapter on the Simplifier covers `simp`, `simp_all`, `clarsimp`, configuration of simpsets, ordered/permutative rewriting, configurable strategies.
  - Tutorial *Programming and Proving in Isabelle/HOL* by Nipkow — https://isabelle.in.tum.de/doc/tutorial.pdf — chapters on simplification, rewriting with definitions, conditional rewriting, automatic case splitting.
- **Tracing & debugging**: Lars Hupel, *Interactive Simplifier Tracing and Debugging in Isabelle*, CICM 2014 — https://arxiv.org/pdf/1406.0292 — describes the hierarchical jEdit-integrated trace facility, including incremental re-tracing after edits. (For comparison, Lean only added comparable diagnostics in 2024–2025; Coq's `Set Debug "tactic-unification"` and similar are still flat traces.)
- **Distinctive features**:
  - **Simpsets are data, not state**: the user can construct a fresh simpset, call the simplifier with it, and discard it. Unlike Lean and Coq, Isabelle treats the simp database as a first-class value.
  - **Permutative/ordered rewriting**: handles AC-like rules safely. `?x + ?y = ?y + ?x` is allowed because the simplifier rewrites only when the LHS is "lex-greater" than the RHS — guaranteeing termination even though the rule itself is non-terminating in general. (Coq has nothing equivalent in the kernel rewrite tactic; Lean does not either, and its docs explicitly warn that bare commutativity loops the simplifier.)
  - **Solver / looper / subgoaler**: the conditional-rewriting machinery is parameterised by user-replaceable tactics. Conditional simp lemmas with side conditions are handled by recursively running the solver — unlike Lean's `discharge` callback, the Isabelle solver is itself a fully-fledged tactic that may use `auto`, `blast`, etc.
  - **Congruence rules**: `cong:` declarations let the user redefine when the simplifier descends into sub-terms. Famously, `if_cong` enables *contextual* rewriting — the condition `b` becomes a hypothesis when simplifying the `then`-branch.
  - **Decision procedure plug-in**: Lukas Stevens & Tobias Nipkow, *A Verified Decision Procedure for Orders in Isabelle/HOL*, ITP 2021 — https://arxiv.org/pdf/2104.13117 — is now part of the simplifier as a sub-procedure.
- **Source**: `src/Pure/raw_simplifier.ML` and `src/Pure/simplifier.ML` in the Isabelle distribution.

### 3.2 Documentation pointers

- Lawrence C. Paulson (ed.), *Old Isabelle Reference Manual* (still authoritative for low-level simpset operations) — https://isabelle.in.tum.de/website-Isabelle2011-1/dist/Isabelle2011-1/doc/ref.pdf
- Clemens Ballarin's tutorial slides — https://www21.in.tum.de/~ballarin/fomus/part2/part2.pdf
- The Isabelle Programming Tutorial (Berghofer & Urban) — https://users.cecs.anu.edu.au/~jeremy/isabelle/doc/progtutorial.pdf — chapter on writing your own simplifier extensions in ML.

---

## 4. Feature comparison

| Dimension | Rocq `simpl`/`cbn` | Rocq `rewrite`/`setoid_rewrite` | Lean 4 `simp` | Isabelle simplifier |
|---|---|---|---|---|
| Primary purpose | Kernel reduction | Equational rewriting under custom relations | Conditional rewriting + reduction | Conditional rewriting |
| User-extensible default lemma set | No | No (`autorewrite` hint dbs separate) | Yes (`@[simp]`) | Yes (`[simp]`) |
| Higher-order pattern matching | β-only | Limited (via `Proper`) | Yes | Yes (Miller patterns; native) |
| Rewriting under binders | Via reduction | Yes, but requires explicit `Proper` instances | Yes (auto congruence lemmas + `funext`) | Yes (built in) |
| Custom relations (non-`eq`) | n/a | **Best-in-class** (Sozeau) | Limited (Lean 3 had it; Lean 4 deprioritised) | Possible but uncommon |
| Conditional rewriting | n/a | Manual | Yes (`discharge`) | Yes (recursive solver tactic) |
| Side-condition discharge | n/a | Via `Proper` instance search | Recursive `simp`, configurable depth | **Pluggable solver tactic** (e.g. `auto`) |
| AC / permutative rules | No | No | No (loops; users avoid) | **Yes — ordered rewriting** |
| User-defined custom rewriters | Plug-ins (OCaml) | Plug-ins (OCaml) | **Simprocs** (in-language Lean) | Simprocs (in-language ML) |
| Discrimination tree indexing | n/a | n/a | Yes | Yes (net) |
| Termination guarantee | Yes (kernel) | No | No (step limit) | No (step limit; ordered rules tame the common case) |
| Integration with decision procedures | Separate (`lia`, `ring`) | Separate (`autorewrite`) | `simp` ↔ `grind` ↔ `decide` ↔ `norm_num` | `simp` ↔ `auto` ↔ `arith` ↔ `presburger` |
| Tracing / debugging | Basic flag | Basic | `simp?`, `set_option trace.Meta.Tactic.simp` | **Interactive jEdit trace** (Hupel 2014) |
| Auto-suggest minimal call | No | No | `simp?` | `try0` (analogous; from Sledgehammer) |

---

## 5. Complexity and performance

Concrete benchmarks comparing the three head-to-head are scarce (the systems aren't easily put on the same problem), but several useful observations exist.

### 5.1 Algorithmic complexity

All three simplifiers share the same core asymptotics:

- Term traversal: **O(n)** per pass over a term of size `n`.
- Lemma lookup per sub-term: roughly **O(log m)** where `m` is the size of the simp set, via a discrimination tree (Lean) or a discrimination net (Isabelle). Coq's `rewrite` has no equivalent indexing — its cost is closer to **O(m)** per attempted rewrite, which is one reason `autorewrite` with hint databases needs care.
- Number of passes: bounded by a step counter. Lean defaults to 100,000 steps; Isabelle has a similar configurable bound; Coq's `simpl` and `cbn` are bounded by kernel reduction depth.

### 5.2 Practical performance characteristics

**Lean's `simp`** is highly optimised for the "huge default simp set" use case (mathlib has ~40,000 `[simp]` lemmas). Recent Lean releases (4.22–4.28, late 2025–early 2026) have specifically targeted:

- congruence-lemma re-generation costs (cached via `mkCongrSimpForConst?`),
- discharger/discrimination-tree interaction (e.g. in [Lean issue #2281](https://github.com/leanprover/lean4/issues/2281)),
- replacing default simprocs (`reduceCtorEq`, `simpEq`) with versions tuned for `grind`'s normalisation pipeline.

The `index := false` config option exists specifically to fall back to the Lean-3-style, slower-but-more-permissive lookup when the discrimination tree's reduction strategy interferes with intended rewrites.

**Isabelle's simplifier** is generally regarded as fast and stable, and the pluggable solver/looper means that tuning is local. Its main practical performance pitfalls are (a) overly aggressive `cong` rules that force re-simplification of large contexts and (b) expensive solvers running on every conditional rewrite.

**Coq's `simpl`/`cbn`** can be slow because they perform full reduction. The conventional wisdom is to mark constants as `simpl never` or `Arguments / ` to control this. `vm_compute` and `native_compute` (which compile to OCaml) are orders of magnitude faster but produce opaque kernel-checked proofs rather than human-readable simplifications. `setoid_rewrite` is widely reported as slow on large goals because of repeated type-class search; the Sozeau 2009 paper explicitly addresses this with the constraint-generation/instance-search split, but the absolute cost of rewriting in Coq is still typically higher than Lean's `simp` for equivalent tasks.

### 5.3 Termination

A 2022 ESOP/PLDI-adjacent comparison from the REST paper (Ji et al., *REST: Integrating Term Rewriting with Program Verification*, https://arxiv.org/pdf/2202.05872) summarises the situation succinctly:

> "the rewriting functionalities of mainstream proof assistants either do not ensure the termination of rewriting (potentially resulting in divergence, for example Isabelle) or enforce termination checks that are overly restrictive in general, potentially rejecting necessary rewrite steps (for example, Lean)"

The practical reality is that Isabelle's *ordered rewriting* gives users a principled way to add commutativity/associativity rules without looping, which neither Coq nor Lean offer. Lean and Coq users either omit such rules from the default set or call dedicated reflective tactics (`ring`, `ring_nf`, `abel`, AAC) for those cases.

### 5.4 Implementation size

Rough orders of magnitude (counting only the rewriter itself, not supporting decision procedures):

| System | Implementation language | LOC (approximate) |
|---|---|---|
| Coq `simpl`/`cbn` | OCaml | ~2,000 (core), in `tactics/` |
| Coq `setoid_rewrite` | OCaml + Coq type-class library | ~3,000 OCaml + ~1,000 Coq (`Classes.Morphisms`) |
| Lean 4 `simp` | Lean 4 | ~5,000 in `src/Lean/Meta/Tactic/Simp/` and `src/Lean/Elab/Tactic/Simp.lean` |
| Isabelle simplifier | Standard ML | ~3,000 in `src/Pure/raw_simplifier.ML` plus surrounding plumbing |

Lean's simp is the largest because it carries congruence-lemma generation, simproc dispatch, discrimination-tree integration, and the dsimp/simp split inside one module.

---

## 6. Headline papers and documentation by system

### Rocq / Coq

1. **Matthieu Sozeau**, *A New Look at Generalized Rewriting in Type Theory*, JFR 2(1), 2009. — https://jfr.unibo.it/article/download/1574/1077/3383 — the canonical reference for `setoid_rewrite`.
2. **Damien Pous**, *Tactics for Reasoning modulo AC in Coq*, CPP 2011. — https://arxiv.org/pdf/1106.4448 — AC-aware rewriting via OCaml oracle + reflective check.
3. **Rocq Reference Manual**, *Term rewriting and simplification* and *Generalized rewriting* chapters — https://rocq-prover.org/doc/V8.20.0/refman/proofs/writing-proofs/rewriting.html and https://rocq-prover.org/doc/V8.20.0/refman/addendum/generalized-rewriting.html
4. (Historical) **C. Sacerdoti Coen**, the original setoid implementation in Coq (2004); **D. Basin**, generalised rewriting in NuPRL (1994).

### Lean

1. **L. de Moura, S. Ullrich**, *The Lean 4 Theorem Prover and Programming Language*, CADE 2021. — https://link.springer.com/chapter/10.1007/978-3-030-79876-5_37 — describes the metaprogramming framework simp builds on.
2. **Lean 4 Reference Manual**, *The Simplifier* chapter — https://lean-lang.org/doc/reference/latest/The-Simplifier/
3. **V. Gladshtein, G. Pîrlea, I. Sergey**, *Small Scale Reflection for the Working Lean User*, ITP 2024. — https://arxiv.org/pdf/2403.12733 — port of SSReflect-style rewriting to Lean.
4. *Fantastic Simprocs and How to Write Them*, Lean community blog, 2024. — https://leanprover-community.github.io/blog/posts/simprocs-tutorial/
5. mathlib *Simp* extras — https://leanprover-community.github.io/extras/simp.html
6. Source: https://github.com/leanprover/lean4/tree/master/src/Lean/Meta/Tactic/Simp and https://github.com/leanprover/lean4/blob/master/src/Lean/Elab/Tactic/Simp.lean

### Isabelle

1. **Tobias Nipkow**, *Term Rewriting and Beyond — Theorem Proving in Isabelle*, Formal Aspects of Computing 1, 1989 — https://link.springer.com/article/10.1007/BF01887212 — the seminal paper.
2. **Tobias Nipkow**, *Functional Unification of Higher-Order Patterns*, LICS 1993 — basis of the higher-order pattern matching used by the simplifier.
3. **L. Hupel**, *Interactive Simplifier Tracing and Debugging in Isabelle*, CICM 2014 — https://arxiv.org/pdf/1406.0292 — the modern jEdit trace.
4. **L. Stevens, T. Nipkow**, *A Verified Decision Procedure for Orders in Isabelle/HOL*, ITP 2021 — https://arxiv.org/pdf/2104.13117 — now bundled inside the simplifier.
5. **L. Paulson, T. Nipkow, M. Wenzel**, *From LCF to Isabelle/HOL*, Formal Aspects of Computing 31(6), 2019 — https://arxiv.org/pdf/1907.02836 — historical overview, including a section on the simplifier's higher-order pattern foundation.
6. **Isabelle/Isar Reference Manual** — https://isabelle.in.tum.de/doc/isar-ref.pdf — definitive user reference.
7. **T. Nipkow, L. Paulson, M. Wenzel**, *Isabelle/HOL: A Proof Assistant for Higher-Order Logic*, LNCS 2283 (the "tutorial book") — https://isabelle.in.tum.de/doc/tutorial.pdf

---

## 7. One-sentence takeaways

- **Rocq** splits the job: a kernel reducer (`simpl`/`cbn`) that doesn't consult lemmas, a generalised rewriter (`setoid_rewrite`) with the most general theory of relations and morphisms via type classes, plus a zoo of reflective domain-specific tactics. No single "do everything" tactic.
- **Lean 4** unifies them under `simp` — one tactic with a discrimination tree, a 40k-lemma default set, simprocs for custom rewriters, tight integration with `grind`. Engineering, not theory, is the differentiator.
- **Isabelle** has the oldest and most theoretically refined simplifier — higher-order pattern matching, ordered rewriting, pluggable solver, contextual rewriting via congruence rules — and arguably the best debugging story. Lean's and Coq's tactics are best understood as different reactions to the same Isabelle template.
