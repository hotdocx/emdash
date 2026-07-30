# TypeScript Elaborator v3.2 — Book Capability Delta Audit

Date: 2026-07-30
Audit-ID: BOOK-DELTA-0A
Plan:
[`TYPESCRIPT_ELABORATOR_V3_2_BOOK_AND_REPOSITORY_GRADUATION_PLAN.md`](./TYPESCRIPT_ELABORATOR_V3_2_BOOK_AND_REPOSITORY_GRADUATION_PLAN.md)
Audit-Anchor:
`8217aa3d30a1086c45e28eb666969b5acec90a6b`
Syntax-Graduation-Review:
`38e0bc2b177773db0faba36e8aaafd12d5e50982`
Status: complete capability-oriented audit; no authored book prose, generated
artifact, public README, mathematical owner, or product behavior changed

## Purpose

This audit identifies what has materially changed since the book's requested
`8217aa3...` reconciliation anchor and decides which changes deserve a
reader-facing mathematical or formal-presentation treatment.

It is deliberately not a release note or a transcription of the intervening
Git history. The history contains hundreds of small plan, test, recovery, and
implementation checkpoints. A reader needs the resulting mathematical and
architectural capabilities, their evidence status, and their limits.

The authority order used here is:

1. active Lambdapi v3.2 declarations, rules, and independent checks;
2. the current kernel SOP, Foundations, and canonical-syntax authorities;
3. the implemented TypeScript v3.2 Core, checker, categorical program, text
   adapter, and integrated reviewer;
4. completed book architecture and formal-presentation plans;
5. the current authored book and its structured evidence manifests; and
6. historical plans and Git checkpoints as provenance only.

## Executive Finding

Two reader-facing facts have changed.

First, the active categorical kernel now contains a useful fixed-base fibred
context calculus: fibrewise products of independent displayed siblings,
displayed projections and pairing, base-change totalization, constant-domain
displayed evaluation, terminal weakening, and bounded mixed dependent chains.
These constructions retain object, arrow, and selected higher-cell action
through internal categorical owners. They are not external pointwise data plus
separately supplied naturality equations.

Second, the TypeScript side is no longer only the obsolete parent prototype
described by the current book. It now has a renewed minimal outer dependent
LF, a backend-neutral explicit emdash Core, generic checking/conversion and
bounded computation, typed categorical contextual elaboration, a fail-closed
text adapter for the reviewed mathematical subset, and a client-side
integrated reviewer. Lambdapi remains the mathematical authority and the
conformance oracle; the TypeScript product is not a second mathematical
kernel.

The work does **not** establish a complete parser for the book's canonical
surface, arbitrary displayed telescope depth or variance, whole-library
mechanical transfer, groupoidal closure of the directed calculus, or global
metatheory. Those remain explicit boundaries.

The book can therefore be updated as a theorem-led mathematical edition
without waiting for the deferred scale programme. No missing kernel
architecture blocks the proposed reader-facing edition.

## Capability Matrix

The “destination” column is an editorial routing decision, not authorization
to edit that source.

| ID | Resulting capability | Classification | Reader question | Intended destination | Evidence/status action | Explicit exclusion |
| --- | --- | --- | --- | --- | --- | --- |
| LF-1 | A minimal outer dependent LF with scoped contexts, dependent Pi/lambda/application, Sigma-style telescope data, and an explicit Core representation | formal-presentation change | What checks ordinary dependent binding outside the categorical layer? | Appendix G, with at most a forward pointer from Chapter 1 | Describe the implemented bounded profile as a product fact; retain Lambdapi as mathematical authority | Do not claim a complete source DTT, universe hierarchy, module system, or general inductive frontend |
| LF-2 | Generic TypeScript checking, conversion, bounded evaluation, runtime rewriting, and proof-time unification for reviewed rules | formal-presentation change | Which computations belong to the small checker, and which remain Lambdapi-owned? | Appendix G and compact Appendix F status row | State the demonstrated runtime/proof-rule envelope and its budgets; do not promote tests into metatheorems | No global confluence, normalization, canonicity, decidability, consistency, or standalone subject-reduction theorem |
| LF-3 | Backend-neutral Core with deterministic Lambdapi emission as an optional backend and bounded conformance oracle | formal-presentation change | Is the TypeScript product a Lambdapi wrapper or a separate explicit checker? | Appendix G architecture diagram and README authority paragraph | Correct the current “optional future elaborator” architecture | No production Lambdapi process dependency and no claim that generated Lambdapi replaces authored sources |
| XFER-1 | Generic checked transfer mechanisms for declarations, runtime rules, proof-time unification rules, and selected generated-owner contracts | formal-presentation change plus compact implementation evidence | Is the demonstrated kernel subset hand-coded case by case? | Appendix G only; one short Appendix F boundary sentence | State only the representative demonstrated envelope | No claim that all remaining modules transfer mechanically; omit acquisition digests, declaration counts, and tranche history |
| ORD-1 | Intrinsic ordinary functorial binding, recursively lowered from variable occurrences into categorical evaluation, weakening, contraction, exchange, and currying constructions | mathematical narrative change | How can a variable occur naturally inside a categorical expression without writing every `fapp*` owner? | Chapter 2 as the main mathematical explanation; Appendix A for notation; Appendix G for compilation | Use the already checked text/direct-TypeScript equality witness | Do not describe it as arbitrary untyped lambda factoring or as an external functoriality proof |
| ORD-2 | Finite nested ordinary functorial abstractions under an explicitly supplied recursive expected classifier | reader workflow and formal-presentation change | Can a reader write a genuinely nested functorial expression? | Primary running example in Appendix G, with a Chapter 2 mathematical reading; optionally one reviewer preset | Use `λ^f x : A. λ^f y : B. E y x` and its direct construction | No inference by decomposing an arbitrary target category and no arbitrary JavaScript callback parity |
| DEP-1 | Natural/indexed sections (`^n`) and displayed-functorial (`^fd`) and displayed-natural (`^nd`) binding through internalized categorical constructions | mathematical narrative and formal-presentation change | How do ordinary, indexed, displayed-functorial, and displayed-natural variables differ? | Chapter 2, Appendix A, and Appendix G | Explain intrinsic binder modes separately from optional classifier annotations | No suggestion that a binder mode is inferred from punctuation alone |
| FIB-1 | A transparent fibrewise product family for two displayed families over the same base, together with displayed projections, pairing, swap, diagonal, and componentwise internal action | mathematical narrative change and new checked evidence | What is the structural context calculus for independent siblings over a shared dependency? | Chapter 2; one cross-reference in Chapter 9 structural cuts | Add a Lambdapi-backed checked evidence claim for the fixed-base product/projection/pairing interface | Do not add or claim a primitive `Product_catd`; the product family remains a transparent composite |
| FIB-2 | Asymmetric base-change totalization `Sigma(F*D) -> Sigma(D)` with object and arrow computation | mathematical narrative change and new checked evidence | How does a dependent context move along a base functor without postulating a general pullback of total categories? | Chapter 2 totals/sections; compact Appendix G owner map | Add a checked claim owned by `sigma_pullback_total_func` and its independent checks | No generic semantic pullback comparison and no claim that every fibration is computationally reconstructed from its total projection |
| FIB-3 | Constant-domain displayed evaluation and terminal displayed weakening | mathematical narrative change and new checked evidence | How are substitution/evaluation and unused displayed variables represented internally? | Chapter 2, then Chapter 9 as a cut-elimination example if space warrants | Add a checked claim for `Eval_funcd` and `Terminal_funcd` | No arbitrary mixed-domain displayed evaluation |
| FIB-4 | Bounded genuine dependent chains and a mixed `[1,2,1]` context with independent siblings at one dependency level | mathematical narrative and reader workflow change | Can the same surface distinguish dependency edges from exchangeable siblings? | Secondary running example in Appendix G; Chapter 2 contextual explanation | Reuse the implemented mixed-telescope reviewer witness and active internal action checks | No arbitrary depth, exchange across a dependency edge, or general reindex/product definitional conversion |
| TEXT-1 | A dependency-free, fail-closed categorical text adapter for four intrinsic modes, neutral application, reviewed constructors, and finite ordinary nesting | formal-presentation and reader workflow change | Which readable expressions are executable today? | Appendix G, Appendix A, How To Read, and README | Replace the stale “future parser only” statement with an exact bounded envelope | Not a Lambdapi parser, not the complete book grammar, and not a second checker or action table |
| DEMO-1 | One client-side reviewer joins editable categorical text, explicit Core/type/result/diagnostics, the three-panel product report, and the generated book | reader workflow change | How can an external reviewer inspect the programme without learning the repository internals first? | How To Read and README; Appendix G may name the workflow once | Link one shortest command and browser route after final artifact validation | No deployment, hosted-site, performance, or external-peer-review completion claim |
| KERNEL-1 | Six post-anchor Lambdapi changes add the fibred product, comprehension/totalization, recursive displayed evaluation, dependent-chain bridge, and mixed-chain closure | new checked evidence for existing or newly explained mathematics | Which parts of the new contextual story are active kernel computation rather than TypeScript-only presentation? | Evidence register plus compact formal-status notes near Chapter 2/9 claims | Cite active owners and independent `emdash3_2_checks.lp` observations | Do not reproduce commit history in the book |
| DEV-1 | Transfer inventories, canonical-export pins, acquisition contracts, worktree recovery, per-tranche revisions, browser chunk boundaries, and test counts | developer-only implementation detail | None in the mathematical narrative | Handoff, plans, tests, and source only | No book action | Exclude from main prose and README opening |
| SCALE-1 | WalkingEnd/HIT stress transfer, larger dependency-closed batches, and whole-library mechanical-transfer graduation remain pending | future research/scale boundary | How far can the transfer workflow presently be generalized? | One concise Appendix F/G limitation and future-goal handoff | Preserve the existing scale ledger; no new claim | Do not resume bulk scale work in the current goal |
| OPEN-1 | Arbitrary displayed depth/variance, general pointwise-to-coherent factorization, groupoidal specialization/closure, and stronger categorical metatheory remain open | future research boundary | Which mathematical and elaboration problems are genuinely unsolved? | Appendix F and the closing boundary of Appendix G | Retain exact boundaries without implying infeasibility | Do not conflate missing generality with a bug in the demonstrated internalized constructions |

## Active Mathematical Delta

Only six post-anchor commits mutate the active Lambdapi kernel/check surface.
Their capability-level content is:

1. **Fixed-base fibrewise structure.** For displayed families `B,C : K -> Cat`,
   their fibrewise product is the transparent composite with
   `P(B,C)[k] = B[k] x C[k]`. The stable owners
   `Product_projL_funcd`, `Product_projR_funcd`, and
   `Product_pair_funcd` expose projections and pairing with object, base-arrow,
   capped-arrow, and selected higher action. Swap and diagonal are derived
   from these owners.
2. **Internal componentwise action.** The existing internalized cell
   `fdapp1_int_cell` computes through displayed product pairing. This is the
   relevant coherence fact: pairing retains arrow action internally rather
   than asking the caller for an external naturality square.
3. **Base-change totalization.**
   `sigma_pullback_total_func(F,D) : Sigma(F*D) -> Sigma(D)` maps `(a,u)` to
   `(F[a],u)` and maps total arrows through the functorial base action.
4. **Displayed evaluation and weakening.** `Eval_funcd` evaluates a varying
   coherent functor at a constant-domain argument, while `Terminal_funcd`
   supplies the canonical unused-variable map to the constant terminal
   family.
5. **Bounded dependent-chain bridges.** Sigma-section and pullback-total
   constructions provide the internal bridge across genuine dependency
   edges, including the mixed context used by the TypeScript reviewer.

This is the correct response to the two views of structural context:

- variables at the same dependency level are independent siblings and admit
  fibrewise weakening, contraction, and symmetry; and
- variables separated by a dependency edge form a telescope and generally
  cannot be exchanged across that edge.

The book should teach this distinction. It should not introduce primitive
“dependent weakening/symmetry/diagonal” owners merely to mirror ordinary
cartesian vocabulary.

## Renewed TypeScript Product Delta

The renewed TypeScript design is a layered compilation path:

```text
direct typed TypeScript or reviewed categorical text
  -> scoped contextual categorical elaboration
  -> backend-neutral explicit emdash Core
  -> generic outer-LF checking, conversion, and bounded computation
  -> TypeScript result
  -> optional deterministic Lambdapi emission/conformance
```

The categorical text layer is intentionally not another bidirectional kernel.
It parses located syntax and resolves it through the same
`CoreCategoricalProgram` used by direct TypeScript construction. Typed
expected classifiers select the admissible categorical operation; the
underlying kernel owners carry object/arrow/higher action.

The graduated surface includes:

- intrinsic `^f`, `^n`, `^fd`, and `^nd` binders within their reviewed
  operation families;
- neutral whitespace application resolved by expected categorical type;
- independent displayed sibling groups and the reviewed bounded mixed
  dependent context;
- selected internally factorable constructors such as fibre pairing and cell
  composition; and
- finite nested ordinary abstraction when each nested expected classifier is
  supplied explicitly.

It fails closed when no reviewed internal factorization exists. Failure to
resolve an arbitrary pointwise expression into a coherent displayed functor
is a semantic boundary, not a string-parsing ambiguity.

## Exact Stale Statements

The next editorial proposal must correct at least these now-stale statements:

1. `book/frontmatter/01-preface.md` calls the elaborator “optional future”.
2. `book/frontmatter/02-how-to-read.md` routes to “future parser notation”
   without mentioning the implemented bounded reviewer syntax.
3. Appendix F's status matrix says there is no complete parser/compiler
   without first recording the bounded implemented product.
4. Appendix F.5 says the canonical surface should eventually elaborate and
   describes only the historical parent TypeScript parser.
5. Appendix G's opening layer table and flow diagram label elaboration as
   entirely future.
6. Appendix G.5 describes only a future elaborator and the obsolete parent
   prototype.
7. Evidence claim `FORMAL-ELABORATION-BOUNDARY` says there is no current
   production parser/end-to-end compiler and that TypeScript is only
   read-only feasibility evidence.
8. `book/expansion.json` still says “optional future elaborator” and does not
   distinguish the implemented bounded product from the complete-surface
   boundary.
9. Chapter 2 has totals and sections but not the now-checked fibrewise
   sibling-context, base-change-totalization, and displayed-evaluation story.
10. Chapter 9 discusses structural product cuts but not the checked
    fixed-base displayed sibling calculus.
11. The root README's categorical-text section still says only `^f` lowers
    and treats `^n`, `^fd`, and `^nd` as pending.
12. The root README foregrounds internal plans, profile counts, and historical
    status far more than the mathematical book and one reviewer workflow.

The phrase “no complete surface parser/compiler” remains true only after the
implemented bounded profile is stated. It must not be deleted and replaced by
an unqualified completion claim.

## Evidence And Status Decision

The existing book evidence checker intentionally treats active Lambdapi
modules as mathematical owners and `emdash3_2_checks.lp` or examples as
independent reviewers. It rejects paths outside `emdash2/` and does not model
TypeScript product tests.

For this edition, the smallest accurate treatment is:

1. add ordinary `checked` evidence entries only for the new active Lambdapi
   fibred-context constructions, using existing owners and independent checks;
2. keep `FORMAL-ELABORATION-BOUNDARY` a `research-boundary` claim, but rewrite
   it to say that a bounded TypeScript product exists while a complete
   canonical-surface compiler and whole-library transfer do not;
3. describe the TypeScript checker/reviewer as an implemented product fact in
   Appendix G and the README, with one reproducible command and direct source
   route; and
4. do not broaden the mathematical evidence schema merely to encode product
   test metadata.

If prose review later determines that TypeScript product claims require a
first-class evidence marker, that is a separate small schema proposal. It is
not a prerequisite for the current mathematical evidence update.

Candidate checked evidence partitions are:

- `CAT-FIBREWISE-CONTEXT`: `Product_projL_funcd`,
  `Product_projR_funcd`, `Product_pair_funcd`, and their object/base-arrow/
  capped/higher and projection-after-pairing checks;
- `CAT-BASE-CHANGE-TOTALIZATION`: `sigma_pullback_total_func` and its
  object/arrow checks; and
- `CAT-DISPLAYED-EVALUATION`: `Eval_funcd`, `Terminal_funcd`, and their
  fibre/evaluation/weakening checks.

The exact owner/reviewer references must be frozen in `BOOK-NARRATIVE-0B`
before `evidence.json` changes.

## Running-Example Candidates

### Recommended primary example: nested ordinary functorial binding

Assume

```text
A, B, C : Cat
E : Functor B (Functor_cat A C).
```

Use:

```text
λ^f x : A. λ^f y : B. E y x
```

This is the best primary example because it shows, in one short expression:

- an intrinsic functorial binder mode;
- two recursively scoped variables;
- neutral applications whose object/arrow action is selected by typing;
- exchange/currying of an existing two-variable functor;
- equality with the direct typed TypeScript construction; and
- compilation into the same explicit Core and checker as the rest of the
  product.

The implementation and focused equality witness already exist. The exact
explicit-Core rendering and inferred classifier should be captured during
`BOOK-NARRATIVE-0B`.

This witness is not currently one of the integrated reviewer's presets.
Adding it as one derived preset would materially join the book and reviewer,
but must be part of the separately reviewed product proposal. It requires no
new parser, checker, or mathematical owner.

### Recommended secondary example: mixed displayed context

Assume the bounded displayed telescope used by the existing reviewer and use:

```text
λ^fd (a : A; b : B, c : C; d : D). fibrePair b c
```

The semicolon records a dependency transition; the comma records independent
siblings over the same prior context. This example is necessary because the
ordinary example cannot show the distinction between telescope dependency
and fibrewise structural exchange. It already appears in the integrated
reviewer and exercises internal object/arrow action.

The book should not use a larger catalogue of parser examples. These two
expressions are sufficient to connect ordinary categorical substitution,
displayed structural contexts, explicit Core, and the reviewer product.

## Proposed Editorial Destinations

`BOOK-NARRATIVE-0B` should freeze exact paragraphs and headings, but this audit
recommends the following small edit map:

| Source | Purpose | Expected scale |
| --- | --- | --- |
| Preface | Replace “optional future elaborator” with one accurate sentence about the bounded executable bridge and retained authority order | one paragraph correction |
| How To Read | Add the shortest reviewer path and distinguish mathematical notation from its executable reviewed subset | one paragraph or compact row |
| Chapter 2 | Explain sibling fibrewise products versus genuine dependency edges; introduce totalization/evaluation as contextual substitution | one theorem-led subsection, reusing the chapter's family narrative |
| Chapter 9 | Relate the checked fixed-base displayed structural calculus to structural cut elimination | one compact subsection or cross-reference, not a second full development |
| Appendix A | Record intrinsic `λ^f`, `λ^n`, `λ^fd`, and `λ^nd` modes and optional classifier annotations; retain the “not all book notation is parser syntax” boundary | one notation table/paragraph |
| Appendix F | Correct implementation status and retain scale/metatheory boundaries | two status-row/paragraph corrections |
| Appendix G | Own the four-layer architecture, bounded syntax profile, two running examples, explicit Core/checking path, and complete-surface boundary | principal formal-presentation rewrite |
| `book/evidence.json` | Add checked fibred-context claims and correct the elaboration boundary statement | structured evidence only |
| `book/expansion.json` | Synchronize the Appendix G layer and boundary descriptions | structured architecture only |
| External reviewer handoff | Point to the exact book examples and, if approved, the new nested preset | compact workflow synchronization |
| Root README | Lead with mathematical thesis, book, one reviewer route, authority boundary, limitations, and contributor links | substantial consolidation after the book artifact is validated |

Chapter 1 does not presently need a substantive rewrite. Appendix G can
explain the renewed outer LF; Chapter 1 should receive at most a forward
pointer if the final narrative otherwise leaves an ambiguity.

## Items Excluded From The Edition

The following are intentionally not book content:

- checkpoint hashes, decision IDs, test counts, and per-tranche chronology;
- canonical export digests and acquisition parser internals;
- transfer linkage, policy-overlay, and declaration-refinement experiments;
- worktree, recovery, warning, and checkpoint SOP mechanics;
- browser bundling and chunk-boundary details;
- the retired TypeScript category API except one historical contrast if
  strictly necessary;
- the proposed but deferred whole-library scale batches;
- temporary experiments and rejected architecture spikes; and
- a hosted GitHub Pages deployment workflow.

These remain available to contributors through the handoff, source, tests,
and living plans.

## Feasibility Assessment

The reader-facing update is mechanically feasible and no longer depends on a
new elaboration algorithm:

- both recommended syntax witnesses already elaborate through the reviewed
  TypeScript pipeline;
- the mixed displayed witness already appears in the integrated reviewer;
- the relevant mathematical structures and checks already exist in the
  active Lambdapi kernel;
- the book has established authored-source, evidence, assembly, render, and
  PDF-export owners; and
- the root README and stable `docs/emdash-book.pdf` route already exist,
  though their content/ownership needs consolidation.

The remaining work is primarily editorial correctness, exact evidence
mapping, one optional reviewer preset, deterministic PDF promotion, and visual
quality assurance. Those are bounded tasks. The long aggregate validation is
not needed during this audit or while only plan/proposal files change; it is
reserved for the later book artifact/release boundary after authored sources
actually change.

The main risk is overstatement, not implementation feasibility. The edition
must preserve these limits:

- bounded text subset, not complete canonical surface;
- demonstrated transfer envelope, not whole-library graduation;
- bounded mixed contexts, not arbitrary displayed depth;
- directed categorical DTT plus an outer LF, not completed groupoidal
  specialization; and
- executable evidence, not global metatheory.

## Successor

`BOOK-NARRATIVE-0B` is now the dependency-ready successor. It must:

1. capture the exact explicit Core, inferred classifiers, and observations for
   the two selected examples;
2. freeze the exact authored-source edit set and section-level narrative;
3. freeze the exact Lambdapi evidence entries and structured-manifest changes;
4. decide whether the already implemented nested witness is added as one
   reviewer preset;
5. identify the existing or smallest deterministic PDF-promotion owner;
6. state proportional validation, reserving aggregate render/release work for
   the actual artifact boundary; and
7. produce a bounded proposal for separate review before any book prose,
   generated artifact, README, or product behavior changes.
