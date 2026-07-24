# TypeScript Elaborator/Kernel For emdash v3.2 — Living Master Plan

Date: 2026-07-24
Plan-ID: TS-ELAB-V3.2
Depends-On: active emdash v3.2 authorities and the completed ELAB-0 wiring
slice
Supersedes: forward architecture and growth guidance in the ELAB-0 RFC and
handoff; preserves their historical evidence
Side-Task-Ledger: coverage, implementation, experiment, and human-review
ledgers in this file
Infinity-Codex-Origin: none; user-directed post-ELAB-0 review on 2026-07-23
Infinity-Codex-Decision-Responses: none; decisions are recorded inline
Status: active living master plan; ELAB-2B is complete, its H-01
recommendation awaits human review, and independent TSK-1A is the next
dependency-ready implementation slice
Pre-implementation baseline:
`a06433e57cba95e7d35f8577b7c71912862c3d25`

## Purpose And Operating Contract

This is the master implementation plan and decision ledger for replacing the
stale root TypeScript category layer with a TypeScript elaborator and candidate
product kernel aligned with the active emdash v3.2 design.

It is deliberately revisable. Each continuation must recover the actual state
from active code, checks, this ledger, and Git rather than treating prose or a
previous conversation as current fact. An owner-position probe or
implementation result may correct, refine, reorder, split, or reject a planned
slice. Record the evidence and changed decision here before or with the code
that depends on it.

This plan does not outrank the active mathematical authorities under
`../emdash2/`. A TypeScript implementation can become the deployed MVP kernel
only after the explicitly recorded graduation boundary below. Until then,
Lambdapi remains the executable specification and differential oracle for the
common implemented fragment.

The Git and checkpoint discipline for a persistent Codex `/goal` run is
defined in
[`PERSISTENT_GOAL_GIT_EXPERIMENTATION.md`](./PERSISTENT_GOAL_GIT_EXPERIMENTATION.md).
The ready-to-use launch prompt appears at the end of this plan.

## Authority And Recovery Order

Before starting or resuming a slice, read and inspect in this order:

1. root `AGENTS.md` and, for any `emdash2/` change, `emdash2/AGENTS.md`;
2. `emdash2/emdash3_2.lp` and its active one-way extensions;
3. `emdash2/emdash3_2_checks.lp`;
4. the current v3.2 SOP, Foundations, and canonical-syntax report named in
   `TYPESCRIPT_ELABORATOR_V3_2_HANDOFF.md`;
5. this plan and its decision/experiment ledgers;
6. the current implementation and tests, relocated with `rg`;
7. staged and unstaged Git state, worktree state, and bounded baselines.

The baseline commit above is a comparison and possible design-backtracking
anchor. It is not an instruction to reset a descendant worktree. Verify the
relationship with:

```bash
git merge-base --is-ancestor \
  a06433e57cba95e7d35f8577b7c71912862c3d25 HEAD
```

If the current work is not a descendant, document why and recover the relevant
ledger and code state before continuing.

## Current Evidence

At the baseline:

- the Git worktree is clean;
- `./scripts/pnpmw run check:ts` passes 159 tests in 44 suites, with 157
  passing and two opt-in Lambdapi probe tests skipped;
- `EMDASH_TYPECHECK_TIMEOUT=60s make -C emdash2 check` passes the active
  kernel, extensions, and diagnostics;
- ELAB-0 implements an isolated direct-TypeScript surface AST to explicit
  target AST to deterministic Lambdapi-probe path under `src/v3_2/`;
- ELAB-0 covers only `fapp0`, `fapp1_fapp0`, and `tapp1_fapp0`;
- the old root category-specific term union and standard library remain
  present, non-authoritative, and coupled to otherwise reusable generic
  elaboration mechanisms.

The active kernel contains the projection ladder that ELAB-0 does not yet
model:

| Role | Full owner | Capped/application owner |
| --- | --- | --- |
| Functor object action | — | `fapp0` |
| Functor hom action | `fapp1_func` | `fapp1_fapp0` |
| Transfor diagonal component | `tapp0_func` | `tapp0_fapp0` |
| Transfor off-diagonal action | `tapp1_func` | `tapp1_fapp0` |
| Source-varying internal Hom | `hom_int` | projected through the common ladder |
| Target-varying internal Hom | `hom_con_int` | projected through the common ladder |

The kernel also has ordinary functor-category weakening, exchange, and
contraction owners (`Const_func_func`, `sym_func_func`, and
`diag_func_func`), displayed categories and functors, pullback
(`Pullback_catd`), constant displayed families (`Const_catd`), and sections
(`Pi_cat`). The current SOP still lists displayed structural logic as a
deferred boundary. Therefore a uniform dependent elaborator is a concrete
consumer to investigate, not evidence that unspecified displayed structural
rules are already sound or should be added wholesale.

## Intended End State

The intended product architecture is:

```text
TypeScript expressions / optional parser
                 |
                 v
surface AST and typed macros
                 |
        scope, constraints, metas,
        binder roles, implicit recovery
                 |
                 v
backend-neutral explicit emdash Core IR
                 |
        +--------+--------------------+
        |                             |
        v                             v
small TypeScript checker/       deterministic Lambdapi
evaluator/rewrite-unifier       conformance emitter
        |                             |
        v                             v
candidate deployed MVP          bounded differential probes/CI
kernel                          against active v3.2 owners
```

The TypeScript surface and macro layer may offer customized constructions that
would be awkward without direct access to Lambdapi internals. Those macros
must elaborate to explicit Core terms and remain outside the small trusted
checker/evaluator.

The final deployed product need not invoke Lambdapi. Lambdapi is retained as:

- the current mathematical and computational specification;
- a rapid experimental workbench for kernel design;
- a differential oracle for the common frozen fragment;
- an optional diagnostic/reviewer backend.

The old TypeScript category theory is not a compatibility target. Its
category-specific nodes, reductions, setup, and tests should ultimately be
deleted and replaced. The sequencing constraint in `AGENTS.md` exists only to
preserve useful generic evidence long enough to extract or reimplement it
cleanly.

## Design Decisions

| ID | Status | Decision | Evidence or review condition |
| --- | --- | --- | --- |
| D-001 | accepted | Replace and eventually delete the old TypeScript category-specific layer; preserve no old category API merely for compatibility. | The old theory predates v3.2 and is entangled with the generic term union. Inventory generic invariants before deletion. |
| D-002 | accepted | Reimplement a clean generic core where extraction would preserve global mutation or stale semantic coupling. | Holes, rule registries, and traversals currently depend on the old union and global state. |
| D-003 | accepted | Use a backend-neutral explicit Core IR. Do not make Lambdapi text the semantic IR. | The product kernel and Lambdapi emitter need one shared elaboration result. |
| D-004 | accepted | Make the TypeScript checker/evaluator the intended product path; keep Lambdapi optional at runtime and mandatory as a conformance oracle until graduation. | ELAB-0 proves integration, not TypeScript parity. |
| D-005 | accepted | Describe families of owners with recursive classifier/projection schemas rather than adding one surface tag per Lambdapi symbol. | Full/capped projections and higher cells repeat the same owner pattern recursively. |
| D-006 | accepted | There is no special `fapp2`: a 2-cell is acted on by applying the ordinary `fapp1_func` schema to the hom functor obtained from the preceding `fapp1_func`. | This preserves the active iterated-hom architecture. |
| D-007 | recommended; H-01 pending | Start the context/type/term design from displayed/dependent structure, then recover ordinary structure only through an authority-classified constant-family specialization. | ELAB-2B represents context, displayed type, substitution, and section uniformly through three new semantic owners and the existing checker. General families have no ordinary route; constant sections are only proof-time comparable with ordinary functors, so dependent-first avoids both eager nondependence detection and a false runtime collapse. Human H-01 review is still required before ELAB-2C. |
| D-008 | accepted | Separate four notions of structural action: meta-level telescope operations, internal ordinary structural functors, displayed structural owners, and shape reindexing. | Naive exchange or contraction is not generally valid in a dependent telescope. |
| D-009 | accepted | Every displayed-to-ordinary comparison must be classified as runtime reduction, proof-time unification, explicit theorem/path, or intentional non-collapse. | Existing bridges do not justify blanket definitional equality. |
| D-010 | accepted | Kernel additions are consumer-led. Missing displayed operations are first recorded as failed owner-position probes; only the smallest coherent owner package may be promoted. | Required by the active v3.2 SOP and warning/subject-reduction discipline. |
| D-011 | accepted | Direct TypeScript AST construction remains the first surface; a string parser is optional and deferred. | Parsing does not test the elaboration or trusted-core boundary. |
| D-012 | accepted | Persistent implementation uses bounded experiments and, only when the launch prompt authorizes them, a dedicated local goal branch/worktree and validated checkpoint commits. | See the Git protocol linked above. |
| D-013 | accepted | Core owner identifiers and slot telescopes are backend-neutral; active Lambdapi names, modules, and source provenance live only in the conformance-backend catalog. Surface projection constructors lower through generic operation records rather than owner-named union branches. | ELAB-1A preserves all three ELAB-0 targets, adds `tapp0_fapp0`, and passes positive/negative Lambdapi probes through this split. |
| D-014 | accepted | Treat a rigid object, hom arrow, or ordinary transfor uniformly through its recursively recovered object-category. Record full, capped, and evaluator owners separately; higher-cell action is recursive reuse of the ordinary full hom schema. | ELAB-1B represents `Hom_cat` and `Transf_cat` as semantic category formers, passes the two-level 2-cell consumer without `fapp2`, rejects the wrong inner hom at its source span, and verifies all three active evaluator conversions in Lambdapi. |
| D-015 | accepted | Decode an object produced by generic `fapp0` from its target category former into the richest rigid Core view currently known. In particular, an object of `Catd_cat(K)` remains an ordinary `K → Cat_cat` functor, while opposite-category membership uses only the active `Obj(Op_cat A) ↪ Obj A` classifier equation and does not identify `A` with `Op_cat A`. | ELAB-1C retains both internal-Hom families after their first object projection, reuses ordinary `fapp0` for the later projection, verifies the distinct `Hom_A(W,Fb)` and `Hom_A(Fb,W)` normal forms in Lambdapi, and rejects both a wrong base object and a variance-reversed conversion. |
| D-016 | accepted | Use a locally nameless Core: named references denote free declarations, De Bruijn indices denote bound occurrences, and binder names are nonsemantic display hints. Structural equality is alpha-invariant; shift/substitution is index-based and capture-safe; the Lambdapi backend generates canonical noncapturing names. | ELAB-2A0 distinguishes same-spelled free/bound terms, handles shadowing and dependent binder types, rejects dangling/downward-escaping indices, composes ordered instantiation, and emits an alpha-canonical identity accepted by Lambdapi. Plicity and variation remain distinct Core metadata; only plicity has direct Lambdapi binder syntax. |
| D-017 | accepted | Split Core scope into an immutable ordered free-declaration environment and a persistent outermost-to-innermost local telescope. Store each local type at its owning depth; lookup selects the nearest local occurrence and lifts that type by its De Bruijn index plus one. Explicit declaration lookup remains available beneath local shadowing. | ELAB-2A1 validates closed declaration types and local types at their owning depths, permits only earlier free dependencies, preserves modes/provenance, keeps independent environments isolated, and abstracts a dependent telescope to a Lambdapi-accepted closed identity. |
| D-018 | accepted | Represent an elaboration metavariable by an opaque per-session identity, deterministic session-local ordinal, and explicit contextual De Bruijn substitution spine. Keep its type and single-assignment solution only in the owning session; solve only canonical identity occurrences in this bounded tranche, reject raw metas at the backend, and leave distinct flex-flex constraints explicitly stuck. | ELAB-2A2 reindexes contextual occurrences through shift/substitution and beneath internal binders, zonks transitively, rejects direct/transitive occurs cycles, scope escape, foreign identities, and noncanonical solving, revisits ordered constraints after progress, and emits a solved result accepted by Lambdapi without importing legacy mutable holes or globals. |
| D-019 | accepted | Give explicit Core a distinct meta-level universe and a generic plicity-bearing call form. Describe every current semantic owner type with one declarative dependent signature language limited to `TYPE`, earlier telescope slots, and owner applications; validate it against the separate arity catalog and let the checker consume it uniformly. | ELAB-2A3A materializes scoped Pi signatures for all 21 owners, passes a saturated application for every signature through Lambdapi, and verifies generic calls through scope/substitution/session/backend paths. `Cat : TYPE` and category-polymorphic application are accepted; arbitrary Type-in-Type polymorphism is outside the supported fragment because Lambdapi correctly exposes the `TYPE`/`KIND` boundary. |
| D-020 | accepted | Keep `KIND` as a checker-only classification rather than an ordinary or serializable Core term. The bounded checker is structural: it validates TYPE/KIND-level declarations and Pi formation, checks lambdas bidirectionally, decomposes rigid type structure, and delegates only canonical meta leaves to the session. Generic implicits are inserted when a supplied explicit argument crosses an implicit Pi binder, so a partial inner call retains later binders; fixed owner applications are saturated from the declarative signature catalog. | ELAB-2A3B checks every owner signature and saturated application through one uniform path, recovers both generic and owner implicits, preserves a nested partial-call consumer, rejects Type-in-Type, rigid/mode/plicity/non-function/missing/ambiguous/occurs/scope boundaries at source provenance, and emits checked generic/fapp0 terms accepted by Lambdapi. Evaluation, conversion, higher-order inversion, and rule validation remain outside this structural claim. |
| D-021 | accepted | Represent `Catd(K)` in Core through the decoded object classifier of `Catd_cat(K)`, as required by D-015, and add only semantic owners for displayed pullback, constant displayed families, and section categories. Store bridge authority classes separately and do not grant the structural checker runtime or proof-time conversion powers. | ELAB-2B checks all three new signatures through the uniform 24-owner catalog, recovers implicit bases, distinguishes meta-level telescope substitution from internal `Pullback_catd`, and uses Lambdapi `eq_refl`/`assertnot` evidence to preserve the runtime versus proof-time boundary. `Sigma_cat`, `Functord_cat`, and new kernel owners were not needed for the bounded consumer. |

“Accepted” records the current engineering direction, not a theorem about the
mathematics. Entries marked experimental must be resolved by the named
evidence before they can constrain the trusted core.

## Core Architecture Requirements

### 1. Separate layers

The implementation must keep these layers distinct:

1. **Surface and macros:** source spans, omitted arguments, convenient
   TypeScript constructors, and later optional parsing.
2. **Elaboration state:** scopes, telescopes, metavariables, constraints,
   expected types, and diagnostics.
3. **Explicit Core:** binders, variables, applications, classifiers, and
   declared rule heads with all semantically relevant arguments represented.
4. **Trusted TypeScript kernel:** scope/type checking, capture-safe
   substitution, weak-head evaluation, rule validation/application, and
   definitional comparison for a frozen fragment.
5. **Backends:** Lambdapi serialization, diagnostics/source-map adaptation,
   debug printers, and future persistence formats.

Surface macros may call elaborator services. They may not mutate trusted rule
tables or bypass Core checking.

### 2. Schema catalogs, not a flat symbol grammar

The first schema catalog should represent:

- classifier formation and its parameter telescope;
- projection families and their full/capped relation;
- endpoint recovery constraints;
- plicity separately from binder variation;
- internalization constructors such as `hom_int` and `hom_con_int`;
- degeneration/comparison routes, with an explicit authority class;
- backend capability and active-source provenance.

An owner schema may name a Lambdapi symbol for conformance, but the surface
grammar should express the mathematical operation. Adding an active symbol to
a catalog is not sufficient: at least one positive consumer, one relevant
negative boundary, and its expected type/normal form are required.

### 3. Recursive higher-cell stress test

Suppose:

```text
F : Functor(A,B)
x,y : Obj(A)
f,g : Hom_A(x,y)
alpha : Hom_(Hom_A(x,y))(f,g)
```

The functor's action on `alpha` should be represented by recursively applying
the same hom-action schema:

```text
fapp1_func (fapp1_func F x y) f g
```

and then applying that resulting functor to `alpha`. This must elaborate
without inventing `fapp2` or falling back to a one-category-only AST case.
A mismatch at either hom level must be rejected at the originating source
span.

### 4. Dependent-first hypothesis

The initial encoding hypothesis to test is:

```text
context Γ               ↦ category interpreting Γ
type A over Γ           ↦ A : Catd Γ
term of A               ↦ section/object associated with Pi_cat A
substitution σ : Δ → Γ  ↦ functor
A substituted along σ   ↦ Pullback_catd A σ
ordinary type B         ↦ Const_catd Γ B, when the comparison is justified
```

This is a design experiment, not yet a selected universal encoding. It must be
tested against:

- dependent extension and lookup;
- weakening by an unused variable;
- substitution and composition;
- exchange only where dependency permits it;
- contraction only with the required diagonal/reindexing data;
- an effectively nondependent family;
- at least one case that must remain displayed rather than collapse.

The experiment must say whether a result is judgmental in the active kernel,
proof-time comparable, available by an explicit theorem/path, or unavailable.

### 5. Ordinary/displayed bridge matrix

Maintain a matrix with at least these columns for every proposed bridge:

Owner sequences below use active Lambdapi spellings so the authority can be
relocated exactly. The machine-readable Core matrix uses semantic identifiers
and outermost-to-innermost owner paths.

| Consumer | Uniform displayed route | Optimized ordinary route | Authority class | Positive evidence | Required non-collapse |
| --- | --- | --- | --- | --- | --- |
| Classify a displayed family over `Γ` | `τ(Obj(Catd_cat Γ))`, definitionally `τ(Catd Γ)` | `τ(Functor Γ Cat_cat)`, definitionally `τ(Obj(Functor_cat Γ Cat_cat))` | runtime reduction at the classifier | `Catd Γ ≔ Obj(Catd_cat Γ)` and `Obj(Catd_cat Γ) ↪ Obj(Functor_cat Γ Cat_cat)`; Core declaration/checker and oracle acceptance | The category head `Catd_cat Γ` remains stable; only its object classifier reduces. |
| Reindex an arbitrary family `E` along `σ : Δ → Γ` | `@Pullback_catd Δ Γ E σ` | `@comp_fapp0 Cat_cat Δ Γ Cat_cat E σ` | proof-time unification | warning-enabled `eq_refl` owner probe through the active `comp_fapp0 ≡ Pullback_catd` unification rule | The paired `assertnot` succeeds: arbitrary semantic composition does not runtime-fold to the stable pullback head. |
| Reindex a constant family | `@Pullback_catd Δ Γ (@Const_catd Γ B) σ` | `@Const_catd Δ B` | runtime reduction | generated conversion assertion accepted through the owning `Pullback_catd(Const_catd …)` rule | Only the constant specialization collapses; no rule identifies an arbitrary pulled-back family with a constant family. |
| Present a general section category | `@Pi_cat Γ E` | `@Functord_cat Γ (@Const_catd Γ Terminal_cat) E` | proof-time unification | warning-enabled category-level `eq_refl` owner probe | The paired `assertnot` succeeds; `Pi_cat` remains the stable section facade and does not runtime-fold to `Functord_cat`. |
| View constant-family sections as ordinary functors | `@Pi_cat Γ (@Const_catd Γ B)`; terms have `τ(Obj(…))` | `Functor_cat Γ B`; terms have `τ(Functor Γ B)` | proof-time unification | generated `eq_refl` comparison and a constant section checked at the ordinary functor type by Lambdapi | Generated `assertnot` succeeds, and the structural TypeScript checker rejects treating the two Core types as structurally equal before TSK-2. |
| Keep an arbitrary dependent section genuinely displayed | `τ(Obj(@Pi_cat Γ E))` | none unless `E` is authority-equated with a constant family | intentional distinction | the displayed section checks through persistent Core contexts | A generated attempt to type the arbitrary section as `τ(Functor Γ B)` is rejected. |

Do not optimize a constant family to an ordinary term until both routes have
a recorded comparison. “TypeScript can detect nondependence” is not itself a
kernel equality.

## Reusable Generic Machinery Inventory

Each legacy mechanism must receive one of four dispositions before the old
category layer is removed: **port**, **reimplement**, **retain temporarily as
oracle**, or **delete**.

| Mechanism | Initial disposition | Required evidence |
| --- | --- | --- |
| Bidirectional `infer`/`check` organization | reimplement from the pattern | Expected-type and inferred-type tests over the new Core |
| Holes/metavariables and occurs check | reimplement behind per-session state | Scope escape, occurs, solution determinism, and error-location tests |
| Higher-order pattern unification | port only after Core binder representation stabilizes | Positive pattern cases and negative non-pattern boundary |
| Rewrite versus unification-rule separation | reimplement as explicit rule classes | Rule validation plus runtime/proof-time differential cases |
| Capture-avoiding substitution and shifting | reimplemented in ELAB-2A0 | Locally nameless binder, shadowing, dependent-type, escape, and ordered-composition tests are green |
| Proof-state traversal | retain as evidence, then reimplement generically | No dependency on old category node tags |
| Direct TypeScript constructors | port | Source-location and macro-expansion tests |
| Existing category constructors/rules | delete after replacement coverage is recorded | No compatibility requirement; retain only independently generic tests |
| Global mutable standard-library/rule setup | delete | New session-owned rule manifest and deterministic reset-free tests |
| Legacy parser | defer/delete | Revisit only after surface/core contracts stabilize |

The inventory is not an instruction to mechanically extract old files. Clean
reimplementation is preferred whenever extraction would preserve the stale
union, ambient global state, or old mathematical assumptions.

## Coverage And Stress Corpus

The coverage ledger is about semantic capabilities, not merely exported names.

| ID | Capability | Current status | Minimum positive/negative evidence |
| --- | --- | --- | --- |
| C-00 | Plicity independent of binder variation | complete in ELAB-0 | Metadata round trip |
| C-01 | `fapp0` implicit category recovery | complete in ELAB-0 | Exact explicit target and wrong functor/object category |
| C-02 | `fapp1_fapp0` capped arrow action | complete in ELAB-0 | Exact target and wrong source category |
| C-03 | `tapp1_fapp0` capped off-diagonal action | complete in ELAB-0 | Exact target and Lambdapi acceptance |
| C-04 | `tapp0_fapp0` diagonal component | complete in ELAB-1A | Exact owner slots, result classifier, wrong component object, and corrupted-target rejection |
| C-05 | `fapp1_func` full hom functor | complete in ELAB-1B | Exact first-class functor target, next-level reuse, evaluator conversion, and corrupted inner-endpoint rejection |
| C-06 | `tapp0_func` full component functor | complete in ELAB-1B | Exact first-class functor target and conversion to `tapp0_fapp0` |
| C-07 | `tapp1_func` full off-diagonal functor | complete in ELAB-1B | Exact first-class functor target and conversion to `tapp1_fapp0` |
| C-08 | Recursive action on a 2-cell | complete in ELAB-1B | Two hom levels use the same full schema; wrong inner endpoint is rejected at its span |
| C-09 | Partially applied `hom_int` | complete in ELAB-1C | Retained `B → Cat_cat` family, later object action, exact source-varying conversion, and wrong-base rejection |
| C-10 | Partially applied `hom_con_int` | complete in ELAB-1C | Retained `Op_cat(B) → Cat_cat` family, exact target-varying conversion, and reversal rejection |
| C-11 | Metavariable/implicit solving over Core | complete for the bounded structural fragment in ELAB-2A3B | Session isolation, contextual scope, occurs, deterministic-order, ambiguity, generic/owner implicit recovery, nested partial calls, and unresolved-meta rejection are green; conversion and higher-order inversion remain explicitly later capabilities |
| C-12 | Context extension and displayed type | complete for the bounded ELAB-2B interpretation | A context category, displayed-family declaration, local dependent section, and substitution pullback survive persistent Core contexts and the checker; reversed substitution is rejected; meta-level telescope substitution remains distinct from internal displayed reindexing. Structural weakening/exchange/contraction remain C-14 through C-16. |
| C-13 | Constant displayed family comparison | complete | Constant pullback reduces at runtime; constant sections check through the ordinary route only by active proof-time unification; the TypeScript structural checker and Lambdapi `assertnot` both preserve the required runtime non-collapse. |
| C-14 | Dependent weakening | missing/inventory required | Concrete elaboration consumer |
| C-15 | Dependency-respecting exchange | missing/inventory required | Permitted and forbidden telescope swaps |
| C-16 | Dependent contraction/diagonal | missing/inventory required | Reindexing data and invalid contraction negative |
| C-17 | TypeScript rule manifest/checker | partial: bounded structural Core checker complete in ELAB-2A3B; frozen rule manifest and evaluator missing | All owner signatures/applications, Pi/lambda checking, and structural negatives are green; manifest proposal/freeze, valid/malformed rules, and differential normal forms remain TSK-1A/1B/2/3 |
| C-18 | Source-mapped backend diagnostics | partial | Generated map exists; diagnostic remapping missing |
| C-19 | Legacy category-layer removal | blocked by replacement | Generic inventory and replacement gates green |

The first higher-dimensional corpus must exercise C-05 through C-10 before
declaring the grammar representative of v3.2.

## Implementation Ledger

Only one row should be marked **in progress** at a time in a single worktree.
Parallel alternatives belong on explicit experiment branches/worktrees and
must identify their common baseline.

| Slice | Status | Dependencies | Deliverable and exit criterion |
| --- | --- | --- | --- |
| PLAN-0 | complete | — | This living plan, Git protocol, synchronized handoff/SOP/index, and a green preparation validation. |
| ELAB-0 | complete wiring spike | — | Three capped/object owners lower to explicit target terms; TypeScript and opt-in Lambdapi positive/negative probes pass. |
| ELAB-1A | complete | ELAB-0 | Backend-neutral classifier/projection owner schemas and generic surface-operation lowering preserve the three ELAB-0 targets; a separate provenance-bearing Lambdapi catalog emits them plus `tapp0_fapp0`; focused exact-target, wrong-object, and positive/negative conformance probes pass. |
| ELAB-1B | complete | ELAB-1A | Variable operation telescopes, explicit full/capped/evaluator pairs, recursive object-category recovery, all three full owners, the recursive 2-cell stress case, wrong-inner-hom rejection, and bounded evaluator-conversion probes are green. |
| ELAB-1C | complete | ELAB-1B | Backend-neutral `hom_int`/`hom_con_int` constructors, category-former object decoding, two retained Hom-valued functors, exact variance conversions, wrong-base rejection, and a reversed-variance Lambdapi negative are green. |
| ELAB-2A | split | ELAB-1 schema stability | The former all-in-one scope/meta/checker tranche is split into ELAB-2A0 through ELAB-2A3B so each checkpoint owns one reviewable semantic claim. |
| ELAB-2A0 | complete | ELAB-1C | Locally nameless free/bound variables, alpha-invariant equality, capture-safe shift/substitution/instantiation, scope validation, canonical backend naming, and a Lambdapi-accepted dependent binder probe are green. |
| ELAB-2A1 | complete | ELAB-2A0 | Immutable ordered declarations and a persistent dependent local telescope validate at their owning depths; deterministic nearest lookup, type lifting, shadowing, abstraction, and source-located duplicate/unbound/scope negatives are green. |
| ELAB-2A2 | complete | ELAB-2A1 | Per-session contextual metavariables and ordered constraints have deterministic isolated identities, capture-safe spines, zonking, scope/occurs rejection, single assignment, explicit stuck/rejected outcomes, and backend-boundary evidence. |
| ELAB-2A3 | split | ELAB-2A2 | The checker tranche is split because Core first needs independently reviewable universe/generic-call syntax and dependent owner type signatures. |
| ELAB-2A3A | complete | ELAB-2A2 | Backend-neutral `TYPE`, generic plicity-bearing calls, a groupoid-universe owner, and a complete declarative dependent type-signature catalog for all 21 current owners pass every scope/session/backend traversal, catalog negative, and bounded Lambdapi consumer. |
| ELAB-2A3B | complete | ELAB-2A3A | A session-bound structural checker validates TYPE/KIND declaration levels, Pi/lambda/application judgments, all owner signatures and applications, dependent generic calls, catalog-driven implicit insertion, explicit ambiguity, and source-located negative boundaries; checked outputs pass Lambdapi. |
| ELAB-2B | complete | ELAB-2A3B | The 24-owner catalog includes the minimal displayed pullback, constant-family, and section-category owners; persistent context/checker consumers, authority-classified bridges, warning-enabled positive/non-collapse probes, and the H-01 recommendation are recorded and green. |
| ELAB-2C | human-gated / pending H-01 | ELAB-2B, reviewed D-007 | Exercise weakening, permitted/forbidden exchange, and contraction. Record missing displayed owners with consumer probes; do not yet assume kernel promotion. |
| KERNEL-DISPLAYED-1 | conditional | ELAB-2C failure evidence | If a concrete uniform elaboration consumer cannot be expressed, design and probe the smallest displayed structural owner package under the v3.2 SOP, including degeneration/comparison and non-collapse cases. Human review is required before promotion. |
| KERNEL-DISPLAYED-2 | conditional | reviewed KERNEL-DISPLAYED-1 | Promote only reviewed kernel changes with diagnostics, warning comparison, audits, catalogs, health, examples, and CI synchronized. |
| TSK-1 | split | ELAB-1 schema stability, ELAB-2A | The manifest tranche is split at H-03 so an implementation proposal cannot silently become the frozen trusted fragment. |
| TSK-1A | next / dependency-ready | ELAB-1 schema stability, ELAB-2A | Define immutable backend-neutral manifest vocabulary, inventory the smallest consumer-backed owner/rule candidates, reject malformed proposals, and record an exact H-03 recommendation without implementing evaluation. |
| TSK-1B | human-gated / pending H-03 | TSK-1A, reviewed fragment | Freeze the reviewed MVP signature/rule manifest and document the exact trusted-core boundary. |
| TSK-2 | pending | TSK-1B | Implement rule validation, weak-head evaluation, rewriting, proof-time unification/comparison classes, and deterministic diagnostics for the frozen fragment. |
| TSK-3 | pending | TSK-2 | Build positive, negative, conversion, malformed-rule, and higher-cell differential tests against Lambdapi for every common owner/rule. |
| MIGRATE-1 | pending | replacement inventory, TSK-2 | Port/reimplement still-useful generic proof/unification facilities and classify every legacy test. |
| MIGRATE-2 | pending | MIGRATE-1, replacement tests | Delete the old category-specific nodes, standard library, reductions, and obsolete category tests; retain no D0/D1 or legacy category compatibility API. |
| GRADUATE-1 | human gate | TSK-3, MIGRATE-2 | Review parity evidence, trust assumptions, subject reduction, termination/confluence scope, performance, and maintenance cost. Decide whether TypeScript is the authoritative deployed MVP kernel. |
| RELEASE-READY | pending | GRADUATE-1 | Documentation, manifests, examples, diagnostics, full repository checks, and explicit residual Lambdapi-conformance policy are synchronized. |

If a slice grows beyond one reviewable semantic claim, split it in this table
before continuing. Do not mark a row complete merely because its code compiles:
its tests, evidence, ledger entry, and proportional gates must all be current.

## Completed Slice: ELAB-1A

ELAB-1A introduced:

- `src/v3_2/schema.ts`, whose semantic owner catalog records classifier and
  capped-projection families, slot roles, plicity, operation constraints,
  result classifiers, and declarative lowering templates;
- `src/v3_2/lambdapi.ts`, the only layer that records active Lambdapi symbol
  spellings, module ownership, and relocatable source-section provenance;
- one generic surface-operation node and one schema interpreter, replacing
  the three owner-specific elaborator branches while preserving their exact
  serialized targets;
- the missing diagonal `tapp0_fapp0` component with its exact result
  classifier, source-located wrong-category rejection, positive Lambdapi
  consumer, and corrupted-target negative.

The schema evidence refines ELAB-1B: the current two-operand records are enough
for capped application, but full projections have variable telescopes.
`fapp1_func` needs a functor plus two endpoints, `tapp1_func` needs a transfor
plus two endpoints, and `tapp0_func` is parameterized by two functors and one
object rather than by a particular transfor. ELAB-1B must generalize operand
names/cardinality declaratively before adding those owners; it must not
reintroduce per-owner switch branches.

### Experiment ELAB-1A-SCHEMA

```text
Experiment ID: ELAB-1A-SCHEMA
Date and checkpoint: 2026-07-23 at 30394f9, before the ELAB-1A goal checkpoint
Question/hypothesis: the four capped ordinary projection forms can share one
  declarative backend-neutral operation schema, with Lambdapi owner spellings
  and active-source provenance confined to a conformance-backend catalog.
Authority and owner position inspected: emdash3_2.lp sections 3a and 6a at
  fapp0/fapp1_func/fapp1_fapp0 and tapp0_func/tapp0_fapp0/tapp1_func/
  tapp1_fapp0; matching diagnostics and the current SOP/Foundations/canonical
  syntax reports.
Current worktree/branch and baseline relationship:
  /home/user1/emdash1-elaborator-goal on goal/typescript-elaborator-v3.2;
  30394f9 descends from baseline a06433e.
Minimal positive consumer: exact Core and generated Lambdapi target for the
  diagonal component of eta : F => G at x, alongside unchanged ELAB-0 output.
Relevant negative/non-collapse consumer: reject a component object from a
  category different from the transfor source, at that object's source span;
  a deliberately corrupted explicit target remains rejected by Lambdapi.
Probe command and bounded result:
  ./scripts/pnpmw exec node --require ts-node/register --test
    tests/v3_2_elab0_tests.ts
    passed 9, skipped 3 opt-in probes.
  EMDASH_RUN_LAMBDAPI_PROBES=1 with the same command
    passed 12/12; the combined four-owner consumer was accepted and both
    deliberately corrupted explicit targets were rejected.
  ./scripts/pnpmw run check:ts
    passed 164 tests / 44 suites: 161 passed, 3 opt-in probes skipped.
  EMDASH_TYPECHECK_TIMEOUT=60s make -C emdash2 check
    passed the active kernel, four one-way extensions, and diagnostics.
  EMDASH_TYPECHECK_TIMEOUT=60s ./scripts/pnpmw run check:all
    passed the root gate; all 41 active Lambdapi kernel/example targets;
    39 formal infrastructure tests; 5 print registry tests; active-reference,
    report-header, book/evidence/typography/KaTeX checks; strict rule-LHS
    audit; and generated catalog freshness.
Warning/audit/catalog/health effects, if any: no Lambdapi declaration or rule
  changed; kernel warning/catalog/health inventories are unchanged.
Decision: accept. All four forms use the same generic operation interpreter;
  no owner-specific elaborator branch was required. Refine only the operand
  telescope cardinality in ELAB-1B.
Plan rows changed: D-013 and C-04 accepted/complete; ELAB-1A complete;
  ELAB-1B dependency-ready.
Remaining prerequisite or human review: none for this bounded slice.
```

## Completed Slice: ELAB-1B

ELAB-1B introduced:

- backend-neutral `Hom_cat`/`Transf_cat` category-former owners, the three full
  projection owners, and an explicit catalog relating each full owner to its
  capped owner through the ordinary object evaluator;
- declarative variable-cardinality operand telescopes for all seven current
  surface operations, still interpreted by one operation-generic elaborator;
- a recursive object-category view for rigid objects, hom arrows, and ordinary
  transfors, plus a direct TypeScript `homCategory(...)` context expression;
- first-class full functor results for `fapp1_func`, `tapp0_func`, and
  `tapp1_func`, with exact classifiers and deterministic Lambdapi bindings;
- deterministic conversion assertions and source-map entries for all three
  active projection betas.

The recursive corpus declares
`alpha : Hom_(Hom_A(x,y))(f,g)`, constructs
`fapp1_func (fapp1_func F x y) f g`, and applies the resulting ordinary
functor to `alpha`. The Core owner chain contains no `fapp2`. A `Hom_C(u,v)`
endpoint in the inner action is rejected at that endpoint's span, and the same
corruption is independently rejected by Lambdapi.

This stabilizes the projection schema enough for ELAB-1C. It does not by itself
settle the session/scope/metavariable design required by ELAB-2A; that slice
retains its Core-binder prerequisite.

### Experiment ELAB-1B-RECURSIVE-PROJECTIONS

```text
Experiment ID: ELAB-1B-RECURSIVE-PROJECTIONS
Date and checkpoint: 2026-07-23 at ELAB-1A checkpoint 386ee44
Question/hypothesis: variable declarative operand telescopes plus a recursive
  "object of category" view can express all three active full/capped pairs and
  the next hom action without an owner-specific branch or fapp2.
Authority and owner position inspected: emdash3_2.lp declarations and
  projection betas for Hom_cat, Transf_cat, fapp1_func/fapp1_fapp0,
  tapp0_func/tapp0_fapp0, and tapp1_func/tapp1_fapp0; matching diagnostics,
  SOP ownership invariants, Foundations, and canonical syntax.
Current worktree/branch and baseline relationship:
  /home/user1/emdash1-elaborator-goal on goal/typescript-elaborator-v3.2 at
  386ee44; descendant of baseline a06433e.
Minimal positive consumer: build fapp1_func(F,x,y), build its next hom action
  fapp1_func(fapp1_func(F,x,y),f,g), and apply that functor to alpha.
Relevant negative/non-collapse consumer: reject an inner endpoint whose
  object-category is not Hom_A(x,y), at that endpoint's source span.
Probe command and bounded result:
  node --require ts-node/register --test tests/v3_2_elab0_tests.ts
    passed 14, skipped 5 opt-in probes.
  EMDASH_RUN_LAMBDAPI_PROBES=1 with the same command
    passed 19/19; recursive and all three conversion assertions were accepted,
    while the corrupted recursive endpoint and both earlier corruptions were
    rejected.
  ./scripts/pnpmw run check:ts
    passed 171 tests / 44 suites: 166 passed, 5 opt-in probes skipped.
  EMDASH_TYPECHECK_TIMEOUT=60s make -C emdash2 check
    passed the active kernel, four one-way extensions, and diagnostics.
  EMDASH_TYPECHECK_TIMEOUT=60s ./scripts/pnpmw run check:all
    passed the root gate; all 41 active Lambdapi kernel/example targets;
    39 formal infrastructure tests; 5 print registry tests; active-reference,
    report-header, book/evidence/typography/KaTeX checks; strict rule-LHS
    audit; and generated catalog freshness.
Warning/audit/catalog/health effects, if any: no Lambdapi source changed; the
  existing three projection betas remain the sole runtime owners, and kernel
  warning/audit/catalog/health inventories are unchanged.
Decision: accept. Variable declarative telescopes and the recursive
  object-category view express every full/capped pair and the next hom action;
  every full owner remains an ordinary first-class functor; all evaluator
  connections have bounded conversion evidence.
Plan rows changed: D-014 accepted; C-05 through C-08 complete; ELAB-1B
  complete; ELAB-1C dependency-ready.
Remaining prerequisite or human review: none for this bounded slice.
```

## Completed Slice: ELAB-1C

ELAB-1C introduced:

- backend-neutral semantic owners and separate Lambdapi bindings for
  `Cat_cat`, `Op_cat`, `Catd_cat`, `hom_int`, and `hom_con_int`;
- generic surface operations for the two internal-Hom constructors, still
  lowered by the operation-schema interpreter without a constructor-specific
  elaborator branch;
- a category-former object decoder: generic `fapp0` now retains the strongest
  rigid Core type known for an object of `Cat_cat`, `Hom_cat`,
  `Transf_cat`, or `Catd_cat`;
- a deliberately narrow object-category comparison implementing
  `Obj(Op_cat A) ↪ Obj A` without treating opposite categories, Hom
  classifiers, or functor sources as globally equal;
- durable source- and target-varying consumers that retain `hom_int(F)[W]` as
  `B → Cat_cat` and `hom_con_int(F)[W]` as `Op_cat(B) → Cat_cat`, then use a
  second ordinary `fapp0`.

The generated probe checks the exact, distinct conversions
`hom_int(F)[W][b] ≡ Hom_A(W,Fb)` and
`hom_con_int(F)[W][b] ≡ Hom_A(Fb,W)`. A `C`-object supplied to the retained
`B → Cat_cat` family is rejected at that object's source span, and Lambdapi
independently rejects conversion of the target-varying route to the reversed
source-varying Hom category.

### Experiment ELAB-1C-PARTIAL-INTERNAL-HOM

```text
Experiment ID: ELAB-1C-PARTIAL-INTERNAL-HOM
Date and checkpoint: 2026-07-23 at ELAB-1B checkpoint 4e58e8e
Question/hypothesis: a generic object-of-category decoder for active category
  formers can retain an object of Catd_cat(K) as an ordinary K-to-Cat functor,
  allowing hom_int(F)[W][y] and hom_con_int(F)[W][b] to use two ordinary fapp0
  applications without a constructor-specific application branch.
Authority and owner position inspected: active declarations and rules for
  Op_cat/Obj(Op_cat), Cat_cat, Catd_cat/Obj(Catd_cat), hom_, hom_con, hom_int,
  hom_con_int, their full/capped represented-endpoint actions, matching checks,
  current SOP ownership invariants, Foundations, and canonical syntax.
Current worktree/branch and baseline relationship:
  /home/user1/emdash1-elaborator-goal on goal/typescript-elaborator-v3.2 at
  4e58e8e; descendant of baseline a06433e.
Minimal positive consumer: retain hom_int(F)[W] as B ⊢ Cat and
  hom_con_int(F)[W] as B^op ⊢ Cat, then project each at an object and confirm
  the exact Hom_A(W,F[y]) / Hom_A(F[b],W) normal form.
Relevant negative/non-collapse consumer: reject a later object from the wrong
  base at its source span and reject conversion of the hom_con_int projection
  to the source/target-reversed Hom category.
Probe command and bounded result:
  node --require ts-node/register --test tests/v3_2_elab1c_tests.ts
    passed 5, skipped 2 opt-in probes.
  EMDASH_RUN_LAMBDAPI_PROBES=1 with the same command
    passed 7/7; both retained families and exact variance conversions were
    accepted, while the source/target-reversed target conversion was rejected.
  ./scripts/pnpmw run check:ts
    passed 178 tests / 45 suites: 171 passed, 7 opt-in probes skipped.
  EMDASH_TYPECHECK_TIMEOUT=60s make -C emdash2 check
    passed the active kernel, four one-way extensions, and diagnostics.
  EMDASH_TYPECHECK_TIMEOUT=60s ./scripts/pnpmw run check:all
    passed the root gate; all 41 active Lambdapi kernel/example targets;
    39 formal infrastructure tests; 5 print registry tests; active-reference,
    report-header, book/evidence/typography/KaTeX checks; strict rule-LHS
    audit; and generated catalog freshness.
Warning/audit/catalog/health effects, if any: no Lambdapi source change is
  present; existing object-projection and variance-separated owners remain the
  runtime authorities.
Decision: accept. Objects of Catd_cat stay first-class ordinary functors in
  Core, opposite object membership is handled by an audited classifier-level
  comparison rather than an owner-specific operation exception, and both
  variance normal forms pass bounded Lambdapi evidence without collapsing.
Plan rows changed: D-015 accepted; C-09 and C-10 complete; ELAB-1C complete;
  the oversized ELAB-2A tranche split into ELAB-2A0 through ELAB-2A2, with
  ELAB-2A0 dependency-ready.
Remaining prerequisite or human review: none for this bounded slice.
```

## Completed Slice: ELAB-2A0

ELAB-2A0 introduced:

- a locally nameless Core boundary: named `reference` nodes are free
  declarations and a distinct `bound` node carries a nonnegative De Bruijn
  index;
- nonsemantic binder display hints, with plicity and variation retained as
  independent metadata;
- alpha-invariant structural equality and uniform capture-safe shift,
  substitution, nearest-binder instantiation, and scope validation across
  owner applications, Pi types, and lambdas;
- deterministic Lambdapi serialization that rejects dangling variables and
  generates canonical binder names reserved away from every free declaration
  and backend owner name;
- durable cases for shadowing, dependent binder types, ordered telescope
  instantiation, same-spelled free/bound separation, mode mismatch, invalid
  indices, downward escape, and safe-integer overflow.

The legacy HOAS bodies, name-opening equality, mutable holes, and global fresh
counter remain isolated in the old prototype. No old term node or global state
was imported into the v3.2 Core.

### Experiment ELAB-2A0-LOCALLY-NAMELESS

```text
Experiment ID: ELAB-2A0-LOCALLY-NAMELESS
Date and checkpoint: 2026-07-23 at ELAB-1C checkpoint 60e5274
Question/hypothesis: separating named free declarations from De Bruijn-indexed
  bound occurrences makes alpha-equivalence structural and supports
  capture-safe shift/substitution without global fresh-name state, while the
  Lambdapi backend can generate deterministic readable binder names.
Authority and owner position inspected: the current v3_2 KernelExpression,
  binder modes, and Lambdapi serializer; active Lambdapi Pi/lambda syntax and
  ordered dependent telescopes; canonical-syntax telescope order; the legacy
  HOAS/name-opening equality, name-based substitution, global fresh counter,
  and their alpha/capture tests as non-authoritative implementation evidence.
Current worktree/branch and baseline relationship:
  /home/user1/emdash1-elaborator-goal on goal/typescript-elaborator-v3.2 at
  60e5274; descendant of baseline a06433e.
Minimal positive consumer: alpha-renamed nested Pi/lambda terms compare
  structurally, serialize identically with generated binder names, and a
  closed ordinary and dependent identity lambda are accepted by Lambdapi.
Relevant negative/non-collapse consumer: distinguish a same-spelled free
  declaration from bound index zero; reject a dangling or downward-escaping
  bound index; keep plicity/variation mismatch structurally unequal.
Probe command and bounded result:
  node --require ts-node/register --test tests/v3_2_core_binder_tests.ts
    passed 9, skipped 1 opt-in probe.
  EMDASH_RUN_LAMBDAPI_PROBES=1 with the same command
    passed 10/10; alpha-canonical ordinary and dependent identity binders were
    accepted by Lambdapi.
  EMDASH_RUN_LAMBDAPI_PROBES=1 over all three v3_2 focused files
    passed 36/36, including every earlier owner/conversion/negative probe.
  ./scripts/pnpmw run check:ts
    passed 188 tests / 46 suites: 180 passed, 8 opt-in probes skipped.
  EMDASH_TYPECHECK_TIMEOUT=60s make -C emdash2 check
    passed the active kernel, four one-way extensions, and diagnostics.
  EMDASH_TYPECHECK_TIMEOUT=60s ./scripts/pnpmw run check:all
    passed the root gate; all 41 active Lambdapi kernel/example targets;
    39 formal infrastructure tests; 5 print registry tests; active-reference,
    report-header, book/evidence/typography/KaTeX checks; strict rule-LHS
    audit; and generated catalog freshness.
Warning/audit/catalog/health effects, if any: no Lambdapi declaration or rule
  changed; this is a backend-neutral Core representation decision.
Decision: accept. Owner applications and dependent binder types traverse
  uniformly, names are unnecessary for bound identity, and canonical backend
  naming preserves closed terms. Plicity remains backend-visible; variation
  remains Core/elaboration metadata because active Lambdapi has no
  corresponding binder annotation.
Plan rows changed: D-016 accepted; capture-safe substitution inventory
  complete; ELAB-2A0 complete. ELAB-2A1 was narrowed to the immutable context
  claim, metavariables moved to ELAB-2A2, bidirectional checking moved to
  ELAB-2A3, and ELAB-2A1 is dependency-ready.
Remaining prerequisite or human review: none for this bounded slice.
```

## Completed Slice: ELAB-2A1

ELAB-2A1 introduced:

- an ordered `CoreDeclarationEnvironment` whose persistent extension validates
  every free declaration type at depth zero against only earlier declarations;
- a persistent `CoreContext` telescope storing local types at the depth where
  they are formed, with no ambient registry, fresh counter, or mutable legacy
  `Term` dependency;
- deterministic nearest-local lookup returning both the bound occurrence and
  its dependent type lifted beneath the binding itself and every newer local;
- explicit free-declaration lookup beneath local shadowing, plus retained
  plicity/variation modes and source provenance;
- telescope abstraction to nested Pi/lambda Core terms, with the dependent
  identity accepted by the Lambdapi conformance backend;
- source-located failures for duplicate declarations, forward/unknown free
  references, unbound uses, and declaration/local types that escape their
  owning depth.

The existing `SurfaceContext` remains the rigid ELAB-0/1 declaration adapter:
it resolves only earlier named surface dependencies and has no local telescope.
The legacy `Context` remains non-authoritative evidence: `extendCtx` prepends a
new array and `lookupCtx` selects its first matching name, but holes,
constraints, fresh counters, definitions, and rule registries are tied to
ambient mutable state. None of those legacy types or globals entered the new
Core context.

### Experiment ELAB-2A1-PERSISTENT-CONTEXT

```text
Experiment ID: ELAB-2A1-PERSISTENT-CONTEXT
Date and checkpoint: 2026-07-23 at ELAB-2A0 checkpoint e3bdf11
Question/hypothesis: an ordered free environment plus a locally nameless
  telescope can provide persistent extension, nearest-name shadowing, and
  correctly lifted dependent lookup types without importing legacy global
  state or identifying local and free occurrences.
Authority and owner position inspected: the ELAB-2A0 KernelExpression and
  scope operations; current SurfaceContext construction/dependency lookup;
  legacy Context/extendCtx/lookupCtx and global fresh/constraint stores as
  non-authoritative evidence; active Lambdapi dependent Pi/lambda syntax;
  canonical ordered telescope notation and the Foundations dependent-context
  reading.
Current worktree/branch and baseline relationship:
  /home/user1/emdash1-elaborator-goal on goal/typescript-elaborator-v3.2 at
  e3bdf11; descendant of baseline a06433e.
Minimal positive consumer: in A : Cat, x : Obj(A), lookup returns x at index
  zero with type Obj(A) lifted beneath x; after further extension older terms
  and types receive their exact new indices. Abstracting the telescope around
  x produces the closed dependent identity accepted by Lambdapi.
Relevant negative/non-collapse consumer: reject duplicate free declarations,
  forward/unknown free references, dangling declaration/local indices, and an
  unbound use at their originating spans; a same-named local resolves to a
  bound node while explicit declaration lookup still returns the distinct free
  reference.
Probe command and bounded result:
  node --require ts-node/register --test tests/v3_2_core_context_tests.ts
    passed 10, skipped 1 opt-in probe.
  EMDASH_RUN_LAMBDAPI_PROBES=1 with the same command
    passed 11/11; the context-abstracted dependent identity was accepted by
    Lambdapi.
  EMDASH_RUN_LAMBDAPI_PROBES=1 over all four v3_2 focused files
    passed 47/47, including every earlier owner/conversion/negative probe.
  ./scripts/pnpmw run check:ts
    passed 199 tests / 47 suites: 190 passed, 9 opt-in probes skipped.
  EMDASH_TYPECHECK_TIMEOUT=60s make -C emdash2 check
    passed the active kernel, four one-way extensions, and diagnostics.
  EMDASH_TYPECHECK_TIMEOUT=60s ./scripts/pnpmw run check:all
    passed the root gate; all 41 active Lambdapi kernel/example targets;
    39 formal infrastructure tests; 5 print registry tests; active-reference,
    report-header, book/evidence/typography/KaTeX checks; strict rule-LHS
    audit; and generated catalog freshness.
Warning/audit/catalog/health effects, if any: no Lambdapi declaration, rule,
  diagnostic, generated catalog, or health authority changed.
Decision: accept. A local binding type belongs to the scope immediately before
  that binding; lookup at index i therefore weakens it by i+1. Free names
  remain declaration identities even when surface-name lookup selects a
  shadowing local. Context extension is persistent and all mutable solving
  state remains deferred to a session boundary.
Plan rows changed: D-017 accepted; C-12 records the completed Core-telescope
  foundation but remains partial until displayed interpretation; ELAB-2A1
  complete and ELAB-2A2 dependency-ready.
Remaining prerequisite or human review: none for this bounded slice.
```

## Completed Slice: ELAB-2A2

ELAB-2A2 introduced:

- an explicit contextual Core `meta` occurrence carrying an opaque session
  token, a deterministic session-local ordinal, and a substitution spine whose
  entries are the current-scope images of the creation-scope De Bruijn
  indices;
- uniform meta-spine traversal in scope checking, structural equality,
  shifting, substitution, free-reference validation, and backend name
  collection, plus simultaneous contextual-spine instantiation that remains
  capture-safe beneath internal Pi/lambda binders;
- a `CoreElaborationSession` that owns the declaration environment, root
  context, meta/constraint counters, typed meta entries, optional
  single-assignment solutions, and ordered constraint entries without
  process-global reset state;
- deterministic transitive zonking, direct and transitive occurs checking,
  creation-scope solution validation, foreign-session rejection, and durable
  source-located diagnostic codes;
- a deliberately bounded constraint step: structural equality and canonical
  flex-rigid assignment solve, invalid assignments reject, distinct flex-flex
  equations remain ambiguous, and noncanonical or rigid equations remain
  stuck for the later checker/conversion layers;
- an explicit Lambdapi backend boundary that rejects every raw meta and emits
  only the result zonked through its owning session.

The legacy `Hole.ref`, global constraint array, global fresh counters, reset
requirements, name-based scope filters, and implicit flex-flex behavior were
used only as non-authoritative inventory evidence. None entered the new Core
or session API. ELAB-2A2 does not claim type-directed solving: checking a
candidate solution against a metavariable's stored type and inserting
implicits are ELAB-2A3 responsibilities.

### Experiment ELAB-2A2-CONTEXTUAL-METAS

```text
Experiment ID: ELAB-2A2-CONTEXTUAL-METAS
Date and checkpoint: 2026-07-23 at ELAB-2A1 checkpoint e75e293
Question/hypothesis: an opaque per-session identity plus an explicit De Bruijn
  substitution spine can make Core metavariables deterministic, isolated, and
  capture-safe under ordinary Core scope operations without mutable term
  references or global reset state.
Authority and owner position inspected: the ELAB-2A0 Core scope operations,
  ELAB-2A1 declaration/local contexts, current backend scope/serialization
  boundary, and the legacy Hole/ref/dereference/occurs/constraint/counter
  implementation only as non-authoritative evidence. No Lambdapi owner or
  runtime rule was changed.
Current worktree/branch and baseline relationship:
  /home/user1/emdash1-elaborator-goal on goal/typescript-elaborator-v3.2 at
  e75e293; descendant of baseline a06433e.
Minimal positive consumer: solve a contextual meta by its nearest local,
  weaken and substitute its occurrence, zonk through an internal lambda
  binder, and emit a separate solved closed meta as Lambdapi-accepted Cat_cat.
Relevant negative/non-collapse consumer: reject direct/transitive occurs
  cycles, a solution escaping its creation depth, and foreign-session access;
  retain distinct flex-flex, noncanonical contextual, and rigid equations as
  explicit stuck outcomes rather than choosing or collapsing them.
Probe command and bounded result:
  node --require ts-node/register --test tests/v3_2_core_session_tests.ts
    passed 13, skipped 1 opt-in Lambdapi probe.
  EMDASH_RUN_LAMBDAPI_PROBES=1 over all five v3_2 focused files
    passed 61/61, including every earlier owner/conversion/negative probe and
    the zonked-meta acceptance probe.
  ./scripts/pnpmw run check:ts
    passed 213 tests / 48 suites: 203 passed, 10 opt-in probes skipped.
  EMDASH_TYPECHECK_TIMEOUT=60s make -C emdash2 check
    passed the active kernel, four one-way extensions, and diagnostics.
  EMDASH_TYPECHECK_TIMEOUT=60s ./scripts/pnpmw run check:all
    passed the root gate; all 41 active Lambdapi kernel/example targets;
    39 formal infrastructure tests; 5 print registry tests; active-reference,
    report-header, book/evidence/typography/KaTeX checks; strict rule-LHS
    audit; and generated catalog freshness.
Warning/audit/catalog/health effects, if any: no Lambdapi declaration, rule,
  diagnostic, generated catalog, or health authority changed.
Decision: accept. Contextual spines make pre-solution scope transformations
  explicit; the session token prevents cross-session equality and solving;
  deterministic ordered retries solve newly rigid constraints without
  guessing flex-flex assignments. Keep higher-order inversion and conversion
  outside this bounded solver.
Plan rows changed: D-018 accepted; C-11 records the completed meta/constraint
  foundation but remains partial until implicit recovery; ELAB-2A2 complete
  and ELAB-2A3 dependency-ready.
Remaining prerequisite or human review: none for this bounded slice.
```

## Completed Slice: ELAB-2A3A

ELAB-2A3A introduced:

- a backend-neutral `universe` term and generic `call` term whose arguments
  retain plicity, with uniform structural equality, scope, shift,
  substitution, contextual-spine instantiation, free-reference traversal,
  meta ownership/zonking, and deterministic Lambdapi serialization;
- a semantic `groupoid-universe` owner, with the active `Grpd` spelling and
  authority section confined to the Lambdapi backend catalog;
- a small declarative signature language containing only the universe,
  references to earlier owner slots, and semantic owner applications;
- complete dependent slot and result signatures for all 21 current owners,
  including both internal-Hom constructors and every full/capped/evaluator
  projection;
- import-time and callable validation of exact owner coverage, slot count,
  name/plicity agreement, dependency order, and nested owner arity;
- uniform materialization of owner Pi telescopes and instantiation of any
  owner slot/result type, ready for checker-driven application without an
  owner-named type switch.

The Lambdapi oracle accepts a saturated application of every owner against its
generated dependent signature. It also accepts `Cat : TYPE` and a generic
category-polymorphic identity call. An exploratory arbitrary
`T : TYPE`-polymorphic identity crossed Lambdapi's `TYPE`/`KIND` boundary and
was rejected, so this slice deliberately represents the active universe sorts
without claiming Type-in-Type.

### Experiment ELAB-2A3A-CORE-SIGNATURES

```text
Experiment ID: ELAB-2A3A-CORE-SIGNATURES
Date and checkpoint: 2026-07-23 at ELAB-2A2 checkpoint 29f0395
Question/hypothesis: a minimal Core universe/call extension plus one
  declarative dependent signature catalog can type every current semantic
  owner uniformly and preserve enough plicity information for later implicit
  insertion, without moving Lambdapi names into the Core schema.
Authority and owner position inspected: active declarations for TYPE, Grpd,
  Cat, τ, Obj, Functor, Hom, Transf, Cat_cat, Op_cat, Hom_cat, Transf_cat,
  Catd_cat, hom_int, hom_con_int, and every fapp/tapp full or capped owner;
  the ELAB-2A0/1/2 Core/context/session boundaries; no Lambdapi declaration or
  rule changed.
Current worktree/branch and baseline relationship:
  /home/user1/emdash1-elaborator-goal on goal/typescript-elaborator-v3.2 at
  29f0395; descendant of baseline a06433e.
Minimal positive consumer: generate a declaration for every dependent slot,
  then check one saturated application of each of the 21 owners against its
  generated result type; separately apply a category-polymorphic identity
  through the generic call form. Lambdapi accepts both consumers.
Relevant negative/non-collapse consumer: reject missing/extra owners, plicity
  drift, a self/forward slot dependency, malformed nested owner arity, and
  wrong slot/result instantiation arity. Preserve the TYPE/KIND distinction:
  the accepted category-polymorphic consumer replaces, rather than weakens,
  the rejected arbitrary Type-in-Type exploratory consumer.
Probe command and bounded result:
  node --require ts-node/register --test tests/v3_2_core_signature_tests.ts
    passed 7, skipped 2 opt-in Lambdapi probes.
  EMDASH_RUN_LAMBDAPI_PROBES=1 with the same command
    passed 9/9; all 21 owner applications and the generic call were accepted.
  EMDASH_RUN_LAMBDAPI_PROBES=1 over all six v3_2 focused files
    passed 70/70, including every earlier owner/conversion/negative probe.
  ./scripts/pnpmw run check:ts
    passed 222 tests / 49 suites: 210 passed, 12 opt-in probes skipped.
  EMDASH_TYPECHECK_TIMEOUT=60s make -C emdash2 check
    passed the active kernel, four one-way extensions, and diagnostics.
  EMDASH_TYPECHECK_TIMEOUT=60s ./scripts/pnpmw run check:all
    passed the root gate; all 41 active Lambdapi kernel/example targets;
    39 formal infrastructure tests; 5 print registry tests; active-reference,
    report-header, book/evidence/typography/KaTeX checks; strict rule-LHS
    audit; and generated catalog freshness.
Warning/audit/catalog/health effects, if any: no Lambdapi declaration, rule,
  diagnostic, generated catalog, or health authority changed.
Decision: accept. Core stores universe and generic elimination separately
  from semantic-owner applications; the signature DSL is expressive enough
  for the entire current owner catalog and remains independently validated
  against its arity/plicity schema. Keep arbitrary TYPE polymorphism, type
  conversion, rule computation, and checker-driven meta solving outside this
  representation tranche.
Plan rows changed: D-019 accepted; C-11 records the complete signature/call
  foundation but remains partial until implicit recovery; ELAB-2A3A complete
  and ELAB-2A3B dependency-ready.
Remaining prerequisite or human review: none for this bounded slice.
```

## Completed Slice: ELAB-2A3B

ELAB-2A3B introduced:

- a `CoreChecker` bound to exactly one `CoreElaborationSession`, with complete
  public boundaries that revisit constraints, zonk terms and types, validate
  scope, and reject every residual meta or ambiguity;
- a checker-only `KIND` classification for `TYPE` and kind-level Pi families,
  preserving active Lambdapi's universe boundary without adding a serializable
  `KIND` Core term or accepting Type-in-Type;
- inference for universes, free declarations, De Bruijn locals, contextual
  metas, owner applications, generic calls, and Pi types, plus lambda checking
  against expected Pi types with exact plicity/variation preservation;
- De Bruijn-index context lookup and dependent result instantiation for Pi
  elimination;
- structural type-constraint decomposition across owner applications, calls,
  and binders, with only meta-vs-term leaves delegated to the ELAB-2A2 session
  and every rigid mismatch kept outside conversion;
- catalog-driven saturation of semantic owners and trigger-driven generic
  implicit insertion: an explicit argument inserts preceding implicit
  binders, while later implicit binders remain available to an outer partial
  call;
- source-located checker diagnostics for invalid declaration sorts,
  Type-in-Type, plicity/variation mismatch, rigid type mismatch, missing/extra
  owner arguments, non-functions, unresolved metas/constraints, and propagated
  occurs/scope rejection.

The checker validates all 21 owner declaration signatures and saturated
applications without an owner-named typing switch. It recovers `A` and `B`
from `F : Functor(A,B)` in `fapp0 F X`, recovers the category of a generic
dependent identity argument, and completes a nested partial call with two
separate implicit insertions. Checked generic and owner results are accepted
by the Lambdapi oracle.

### Experiment ELAB-2A3B-STRUCTURAL-CHECKER

```text
Experiment ID: ELAB-2A3B-STRUCTURAL-CHECKER
Date and checkpoint: 2026-07-23 at ELAB-2A3A checkpoint b2298da
Question/hypothesis: the locally nameless Core, dependent owner signatures,
  and contextual session are sufficient for a small bidirectional checker to
  recover ordinary implicits structurally, without evaluator rules,
  owner-specific typing branches, legacy holes, or global state.
Authority and owner position inspected: the active TYPE/KIND boundary and all
  21 current owner declarations; ELAB-2A0 shift/substitution, ELAB-2A1
  contexts, ELAB-2A2 sessions, ELAB-2A3A signatures, and the legacy
  infer/check/implicit organization only as non-authoritative implementation
  evidence. No Lambdapi declaration or rule changed.
Current worktree/branch and baseline relationship:
  /home/user1/emdash1-elaborator-goal on goal/typescript-elaborator-v3.2 at
  b2298da; descendant of baseline a06433e.
Minimal positive consumer: check a dependent category-polymorphic identity,
  infer a generic call that inserts its category, infer fapp0 from only F and
  X while inserting A and B, preserve and complete a nested partial call, and
  check every current owner signature/application uniformly. The two emitted
  implicit-application consumers are accepted by Lambdapi.
Relevant negative/non-collapse consumer: reject a Pi binder over TYPE, an
  invalid declaration type, wrong owner category, wrong plicity/variation,
  missing explicit owner argument, non-function call, unresolved inserted
  meta, flex-flex ambiguity, occurs assignment, and dangling bound index.
  No rewrite or definitional conversion is attempted for rigid mismatches.
Probe command and bounded result:
  node --require ts-node/register --test tests/v3_2_core_checker_tests.ts
    passed 12, skipped 1 opt-in Lambdapi probe.
  EMDASH_RUN_LAMBDAPI_PROBES=1 with the same command
    passed 13/13; checked generic identity and fapp0 outputs were accepted.
  EMDASH_RUN_LAMBDAPI_PROBES=1 over all seven v3_2 focused files
    passed 83/83, including every earlier owner/conversion/negative probe.
  ./scripts/pnpmw run check:ts
    passed 235 tests / 50 suites: 222 passed, 13 opt-in probes skipped.
  EMDASH_TYPECHECK_TIMEOUT=60s make -C emdash2 check
    passed the active kernel, four one-way extensions, and diagnostics.
  EMDASH_TYPECHECK_TIMEOUT=60s ./scripts/pnpmw run check:all
    passed the root gate; all 41 active Lambdapi kernel/example targets;
    39 formal infrastructure tests; 5 print registry tests; active-reference,
    report-header, book/evidence/typography/KaTeX checks; strict rule-LHS
    audit; and generated catalog freshness.
Warning/audit/catalog/health effects, if any: no Lambdapi declaration, rule,
  diagnostic, generated catalog, or health authority changed.
Decision: accept for the bounded structural fragment. Keep KIND out of
  serializable Core, saturate fixed owner applications, insert generic
  implicits only when application syntax crosses them, and preserve partial
  calls. Failed or ambiguous elaboration remains explicit; evaluator
  conversion and higher-order inversion remain TSK-2 work.
Plan rows changed: D-020 accepted; C-11 complete for the bounded structural
  fragment; C-17 partial; ELAB-2A3B complete and ELAB-2B dependency-ready.
Remaining prerequisite or human review: none for ELAB-2A3B.
```

## Completed Slice: ELAB-2B

ELAB-2B introduced:

- three and only three new semantic Core owners:
  `displayed-pullback`, `constant-displayed-family`, and `section-category`,
  with exact active plicities and dependent signatures; `Catd(K)` continues
  to use the D-015 object-classifier route through `Catd_cat(K)`;
- direct Core helpers for the type of a displayed family, internal displayed
  reindexing, constant families, section categories/types, and the ordinary
  functor type used only as a classified comparison route;
- a machine-readable bridge catalog whose owner paths and authority classes
  do not grant conversion powers to the structural checker;
- persistent-context consumers for a context category, displayed family,
  substitution, general section, constant section, and local dependent
  section, all checked through the same catalog-driven ELAB-2A3B path;
- an explicit test that meta-level De Bruijn telescope substitution does not
  construct or stand in for internal `Pullback_catd` reindexing;
- backend probe support for proof-time equality evidence, negative runtime
  conversion assertions, and warning-enabled runs with a bounded diagnostic
  buffer.

No `Sigma_cat`, `Functord_cat`, displayed structural owner, Lambdapi rule, or
TypeScript evaluator rule was added. The bounded context/type/term consumer
does not require those additions.

The H-01 recommendation is to select dependent-first as the canonical
elaboration representation for genuinely context-indexed types and terms,
while retaining ordinary types as an explicit route and optimizing a constant
family only through a recorded bridge. This is simpler for the observed
consumer because the checker uses one owner/signature path for general and
constant families; an ordinary-first representation would need a branch for
the general family and would still need displayed pullback. The recommendation
does not claim that constant sections runtime-collapse: the active comparison
is proof-time only, and both Core structural inequality and Lambdapi
`assertnot` preserve that boundary. D-007 therefore remains pending human
H-01 review, and ELAB-2C does not start meanwhile.

### Experiment ELAB-2B-DEPENDENT-FIRST-CONTEXT

```text
Experiment ID: ELAB-2B-DEPENDENT-FIRST-CONTEXT
Date and checkpoint: 2026-07-24 at ELAB-2A3B checkpoint 3cf4ac7
Question/hypothesis: the existing locally nameless Core, persistent contexts,
  structural checker, and the smallest active displayed owner set can express
  one dependent-first context/type/substitution/term route uniformly, while
  retaining the exact runtime/proof-time distinctions needed for an honest
  constant-family specialization.
Authority and owner position inspected: active Catd/Catd_cat declarations and
  classifier rules; Pullback_catd declaration, fibre/constant/identity/
  accumulation rules and semantic-composition unification bridge; Const_catd
  declaration and fibre/pullback rules; Pi_cat declaration, object/hom
  projections, terminal-source and constant-family unification bridges;
  current SOP, Foundations, canonical-syntax report, and active checks. No
  Lambdapi declaration or rule changed.
Current worktree/branch and baseline relationship:
  /home/user1/emdash1-elaborator-goal on goal/typescript-elaborator-v3.2 at
  3cf4ac7; descendant of baseline a06433e.
Minimal positive consumer: declare Γ and Δ as context categories, E as a
  displayed family over Γ, σ : Δ → Γ, and a section of E; infer
  Pullback_catd(E,σ) and Pi_cat(E) with both base categories recovered through
  the generic checker. Extend a persistent local telescope by a family and a
  section depending on its nearest De Bruijn occurrence. Also check a
  constant-family section at its ordinary functor type through the Lambdapi
  proof-time bridge.
Relevant negative/non-collapse consumer: reject σ with reversed source/target
  at its source span; keep meta-level Core substitution syntactically distinct
  from internal displayed reindexing; reject an arbitrary dependent section
  at an ordinary functor type; and accept assertnot for both general
  Pi/Functord and constant Pi/Functor runtime comparisons.
Probe command and bounded result:
  two temporary warning-enabled owner probes under emdash2/tmp/probes
    succeeded within 60s: one covered Catd, Pullback, Const, general Pi, and
    constant Pi routes; one covered semantic composition versus stable
    Pullback with paired eq_refl/assertnot evidence.
  EMDASH_RUN_LAMBDAPI_PROBES=1 focused ELAB-2B
    passed 10/10, including the warning-enabled positive bridge and the
    arbitrary-family rejection.
  EMDASH_RUN_LAMBDAPI_PROBES=1 over all eight v3_2 focused files
    passed 93/93.
  ./scripts/pnpmw run check:ts
    passed 245 tests / 51 suites: 231 passed, 14 opt-in probes skipped.
  EMDASH_TYPECHECK_TIMEOUT=60s make -C emdash2 check
    passed the active kernel, four one-way extensions, and diagnostics.
  EMDASH_TYPECHECK_TIMEOUT=60s ./scripts/pnpmw run check:all
    passed the root gate; all 41 active Lambdapi kernel/example targets;
    39 formal infrastructure tests; 5 print registry tests; active-reference,
    report-header, book/evidence/typography/KaTeX checks; strict rule-LHS
    audit; and generated catalog freshness.
Warning/audit/catalog/health effects, if any: warning-enabled probes reproduced
  the existing imported-kernel warning stream and introduced no tracked
  warning baseline, Lambdapi rule, audit, generated catalog, or health change.
Decision: accept the bounded implementation and recommend dependent-first for
  H-01. Keep D-007 awaiting human review, keep the TypeScript checker
  structural until TSK-2, and leave ELAB-2C gated.
Plan rows changed: D-007 recommended/H-01 pending; D-021 accepted; C-12 and
  C-13 complete for their bounded evidence; ELAB-2B complete; ELAB-2C gated;
  TSK-1 split at H-03 and independent TSK-1A dependency-ready.
Remaining prerequisite or human review: H-01 must review D-007 before
  ELAB-2C. It does not block TSK-1A.
```

## Immediate Slice: TSK-1A

Build a reviewable manifest proposal before asking H-03 to freeze it:

1. recover the active declarations and owning runtime/unification rules for
   the smallest consumer-backed candidate fragment already exercised by
   ELAB-0 through ELAB-2B; do not infer rule authority from TypeScript tests;
2. define immutable backend-neutral manifest records for signature membership,
   runtime reduction, proof-time comparison, provenance, and consumer
   coverage, without implementing matching or evaluation;
3. require complete owner references, unique rule identities, explicit
   authority classes, left/right scope validity, and deterministic manifest
   ordering; reject malformed, duplicate, unknown-owner, and cross-class
   proposals with focused diagnostics;
4. distinguish the proposed product fragment from the larger 24-owner
   conformance catalog and record every exclusion, especially rules or owners
   whose termination, confluence, subject reduction, or consumer need is not
   yet bounded;
5. exercise one representative runtime rule, one proof-time comparison, and
   one intentional non-collapse as data, then record the exact H-03
   recommendation and pass all earlier gates.

Do not call the proposal frozen before H-03, implement evaluator behavior
(TSK-2), import active Lambdapi spellings into backend-neutral Core, promote
kernel owners, or begin ELAB-2C while H-01 is pending.

## Human Review Gates

Record a concrete recommendation and evidence before requesting review:

| Gate | Earliest trigger | Question |
| --- | --- | --- |
| H-01 | ELAB-2B | Does the dependent-first encoding produce a simpler uniform elaborator than an ordinary-first Core with displayed forms only where needed? |
| H-02 | KERNEL-DISPLAYED-1 probe complete | What are the mathematically correct displayed weakening, exchange, and contraction owners, and which degenerations should compute, unify, or remain theorem-level? |
| H-03 | TSK-1A proposal complete | What exact owner/rule fragment is frozen as the MVP TypeScript kernel? |
| H-04 | TSK-2 | What termination, confluence, subject-reduction, and trusted-rule assumptions may the MVP claim? |
| H-05 | GRADUATE-1 | Is Lambdapi retained only as CI/reviewer oracle, or as an ongoing acceptance authority for selected declarations? |
| H-06 | after measured need | Is a textual grammar stable and valuable enough to support? |

A human gate blocks only the dependent slice. Record the prerequisite and
continue any independent dependency-ready work instead of guessing the
decision.

Current gate state: ELAB-2B has recorded a positive dependent-first H-01
recommendation, but H-01 remains awaiting human review and blocks ELAB-2C.
Independent TSK-1A is active; it must produce, not assume, the H-03 fragment
recommendation.

## Experiment Record Template

Append or link one record for an experiment that changes architecture:

```text
Experiment ID:
Date and checkpoint:
Question/hypothesis:
Authority and owner position inspected:
Current worktree/branch and baseline relationship:
Minimal positive consumer:
Relevant negative/non-collapse consumer:
Probe command and bounded result:
Warning/audit/catalog/health effects, if any:
Decision: accept / reject / refine / defer
Plan rows changed:
Remaining prerequisite or human review:
```

Temporary probes belong under ignored `emdash2/tmp/probes/` or another
explicit temporary location. Durable evidence belongs in focused tests,
diagnostics, examples, or the appropriate report.

## Validation Matrix

| Change | Minimum gate before checkpoint/handoff |
| --- | --- |
| Plan/docs only | `git diff --check`, relevant link/header checks, `check:ts`, bounded `make -C emdash2 check` |
| Root TypeScript behavior | focused tests, `./scripts/pnpmw run check:ts` |
| Common Core/Lambdapi owner | focused opt-in generated probes with timeout at most 60 seconds, then bounded kernel check |
| Root package/setup | `workspace:check`, root typecheck/tests, affected print checks |
| Lambdapi declaration/rule | owner-position probe; diagnostics; warning comparison; LHS/rule audits; catalog/health refresh; examples and full `make ci` as required by `emdash2/AGENTS.md` |
| Substantial cross-layer tranche | `./scripts/pnpmw run check:all` |
| Legacy deletion | all replacement-focused gates plus full repository check and explicit test-disposition ledger |

Record exact commands and outcomes in the completed slice or checkpoint
message. Never weaken a gate to make a checkpoint green.

### PLAN-0 preparation validation

Validated from the Git root on 2026-07-23:

```text
python3 emdash2/scripts/lint_report_headers.py
  passed; 10 active plan headers

local relative-Markdown-link audit
  passed; 30 links across the seven changed navigation/plan documents

git diff --check
  passed

./scripts/pnpmw run check:ts
  workspace contract, TypeScript, ESLint, and root tests passed
  159 tests / 44 suites: 157 passed, 2 opt-in probes skipped

EMDASH_TYPECHECK_TIMEOUT=60s make -C emdash2 check
  active kernel, extensions, and diagnostics passed

EMDASH_TYPECHECK_TIMEOUT=60s ./scripts/pnpmw run check:all
  root TypeScript gate passed
  41 active Lambdapi kernel/example files passed
  39 formal infrastructure tests and 5 print registry tests passed
  active-reference/report-header/book/evidence/typography/KaTeX checks passed
  strict rule-LHS audit and generated catalog freshness passed
```

No TypeScript source, test behavior, package/lockfile, Lambdapi declaration,
kernel rule, generated authority, branch, worktree, or commit was changed by
PLAN-0.

## Persistent `/goal` Launch Prompt

The following prompt is ready to use. It explicitly authorizes creating or
reusing one dedicated local goal branch/worktree and making local validated
checkpoint commits there; it does not authorize pushing, merging, publishing,
rewriting history, or deleting worktrees.

Before pasting it, start a new Codex session from the Git root, review and
trust the root project hook through `/hooks`, and verify the shared archive as
described in `PERSISTENT_GOAL_GIT_EXPERIMENTATION.md`.

```text
Kick off or continue implementing
docs/TYPESCRIPT_ELABORATOR_V3_2_MASTER_PLAN.md.

Treat it as the living master plan and decision ledger: determine the actual
current state from the active code, checks, plan status/ledger, and Git
worktree; then resume the in-progress slice or select the next
dependency-ready bounded slice according to the plan. Read and follow the root
AGENTS.md, the repository authority order, and, for every emdash2 change,
emdash2/AGENTS.md and the current v3.2 SOP. Perform the implementation—not
merely another general review—and keep the TypeScript kernel/elaborator,
Lambdapi diagnostics and probes, plan, and other affected authorities
synchronized.

The plan is revisable rather than immutable: correct, refine, split, reorder,
reject, or extend a slice when owner-position probes or implementation
evidence reveal a better architecture. Record the concrete evidence, changed
decision, dependencies, human-review status, and remaining work in the plan.
Preserve the distinction between the active Lambdapi mathematical
specification, the backend-neutral explicit Core, the candidate TypeScript
product kernel, and the optional Lambdapi conformance backend.

Commit a06433e57cba95e7d35f8577b7c71912862c3d25 is the
pre-implementation baseline for comparison and possible design backtracking
only. Work from the current state when it is that commit or a descendant,
including a temporary checkpoint descendant; do not reset to the baseline.
On every continuation, inspect staged and unstaged changes and
git worktree list, verify the baseline relationship, preserve unrelated work,
relocate symbols rather than relying on remembered lines, and run bounded
probes/checks and the proportional warning, audit, catalog, health, example,
and CI gates required by the SOP.

Use docs/PERSISTENT_GOAL_GIT_EXPERIMENTATION.md. Local checkpoint commits on
the dedicated goal branch are authorized for this objective after each
bounded tranche has passed its proportional gates and the living plan ledger
is synchronized. Inspect the exact staged diff and do not include unrelated
pre-existing work. Creating or reusing one dedicated local goal branch and
worktree is also authorized: first inspect existing names and worktrees; if
this worktree contains only plan-scoped preparation changes, create the goal
branch in place so those changes are preserved; if it is clean, a sibling
goal worktree may be created at the current descendant and bootstrapped.
Never move, stash, copy, or commit unrelated dirty work to establish the goal
worktree. Use new commits or explicitly recorded experiment branches for
backtracking; do not amend, rebase, reset away, or otherwise rewrite
checkpoints. Do not push, merge to main, publish, release, create a PR, delete
branches, or remove worktrees unless separately requested by the user.

Continue making safe, plan-scoped progress until every plan row is genuinely
complete, rejected with durable evidence, or deferred behind a concrete
recorded prerequisite or human decision. If evidence exposes a blocker or
invalidates a planned step, document the result and pursue any independent
dependency-ready work that remains in scope. A need for human mathematical
review blocks only the affected slice; never guess a rule or a
displayed-to-ordinary equality.
```
