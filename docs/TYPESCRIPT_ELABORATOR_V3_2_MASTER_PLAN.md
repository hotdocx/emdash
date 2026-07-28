# TypeScript Elaborator/Kernel For emdash v3.2 — Living Master Plan

Date: 2026-07-28
Plan-ID: TS-ELAB-V3.2
Depends-On: active emdash v3.2 authorities and the completed ELAB-0 wiring
slice
Supersedes: forward architecture and growth guidance in the ELAB-0 RFC and
handoff; preserves their historical evidence
Side-Task-Ledger: coverage, implementation, experiment, and human-review
ledgers in this file
Infinity-Codex-Origin: none; user-directed post-ELAB-0 review on 2026-07-23
Infinity-Codex-Decision-Responses: none; decisions are recorded inline
Human-Decision-Record: on 2026-07-24 the user approved H-01 dependent-first,
H-03/D-023, H-04/D-030, and H-05/D-039 exactly as proposed
Status: completed implementation ledger for the exact
`emdash-v3.2-mvp-1` release-ready profile; H-01, H-03, H-04, and H-05 are
resolved, every concrete slice is complete, and H-02/H-06 remain untriggered
conditional future gates
Continuation: the reviewed outer-LF and directed-DTT implementation is
recorded by
[`TYPESCRIPT_ELABORATOR_V3_2_DTT_LF_CONTINUATION_PLAN.md`](./TYPESCRIPT_ELABORATOR_V3_2_DTT_LF_CONTINUATION_PLAN.md);
forward systematic-transfer work is governed by
[`TYPESCRIPT_ELABORATOR_V3_2_SCALE_QUALIFICATION_PLAN.md`](./TYPESCRIPT_ELABORATOR_V3_2_SCALE_QUALIFICATION_PLAN.md);
the current dependent-demo and categorical-binder frontend critical path is
governed by
[`TYPESCRIPT_ELABORATOR_V3_2_USABILITY_PLAN.md`](./TYPESCRIPT_ELABORATOR_V3_2_USABILITY_PLAN.md);
the selected displayed-product and dependency-aware fibred-context
continuation is governed by
[`TYPESCRIPT_ELABORATOR_V3_2_FIBRED_CONTEXT_PLAN.md`](./TYPESCRIPT_ELABORATOR_V3_2_FIBRED_CONTEXT_PLAN.md);
the active general displayed contextual-abstraction continuation is governed
by
[`TYPESCRIPT_ELABORATOR_V3_2_DISPLAYED_BRACKET_PLAN.md`](./TYPESCRIPT_ELABORATOR_V3_2_DISPLAYED_BRACKET_PLAN.md);
this completed plan remains frozen historical evidence for the exact
`emdash-v3.2-mvp-1` profile
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
| D-007 | accepted; H-01 approved 2026-07-24 | Start the context/type/term design from displayed/dependent structure, then recover ordinary structure only through an authority-classified constant-family specialization. | ELAB-2B represents context, displayed type, substitution, and section uniformly through three new semantic owners and the existing checker. General families have no ordinary route; constant sections are only proof-time comparable with ordinary functors, so dependent-first avoids both eager nondependence detection and a false runtime collapse. The user approved the recorded dependent-first recommendation; ELAB-2C may proceed without changing the authority classes. |
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
| D-022 | accepted | Make a product rule proposal closed-world, deeply immutable, and backend-neutral. A semantic rule record carries an explicit authority class, scoped owner pattern, consumer coverage, and opaque evidence key; exact active names and source locations live in a separately complete conformance-backend binding. Do not port the legacy global rule registries or their RHS-only unification-variable behavior. | TSK-1A validates complete ordered owner coverage, dependency closure, unique rule/evidence identities, owner arity, variable scope, authority-specific shapes, and exact backend evidence coverage without matching or evaluation. It rejects malformed, duplicate, unknown-owner, scope-escaping, cross-class, and recommendation-drift proposals deterministically. |
| D-023 | accepted; H-03 approved 2026-07-24 | Freeze the dependency-closed 16-owner ordinary classifier/projection signature and exactly three generic full-to-capped runtime projection betas. Freeze no proof-time comparison rule yet. Keep the other eight current owners, the constant-section proof-time bridge, and its required runtime non-collapse as conformance evidence until their larger rule neighborhoods are bounded. | The user approved H-03/D-023 exactly as proposed. The ordinary subset covers ELAB-0/1B including recursive 2-cell action. Every excluded owner and rule family retains concrete consumer and open-risk evidence. The three active runtime rules, constant-section unification chain, and negative runtime probe have exact backend provenance. |
| D-024 | accepted | Preserve the immutable TSK-1A proposal as its pre-review audit record and publish a separate, content-hashed `emdash-v3.2-mvp-1` manifest for the reviewed product profile. Snapshot all 16 selected dependent signatures and three selected runtime rules; record implemented, frozen-but-deferred, and outside-kernel mechanisms explicitly. | TSK-1B rejects status, approval, owner order, signature, rule, trust-boundary, and content-hash drift. The general checker and Lambdapi backend remain conformance supersets; no evaluator, matcher, proof-time rule, or excluded owner gains product authority merely by being implemented or serializable. |
| D-025 | accepted | Represent meta-level dependent weakening, permitted adjacent exchange, and adjacent contraction as explicit source-to-target ambient De Bruijn index maps over persistent telescopes. Exchange may drop the older variable from the moved type only when unused; contraction requires the newer binder to have the structurally identical weakened type and matching mode. Transport every dependent suffix through the same map. | ELAB-2C maps preserve occurrence provenance beneath internal binders, exercise position-zero and nonzero dependent prefixes/suffixes, reject a forbidden swap at the exact dependency occurrence, reject type/mode-invalid diagonals, and emit three Lambdapi-accepted dependent consumers. They introduce no ordinary or displayed structural owner. |
| D-026 | accepted | Split TSK-2 into runtime compilation/validation (TSK-2A), deterministic matching and weak-head rewriting (TSK-2B), then definitional comparison, authority separation, and H-04 evidence (TSK-2C). Keep the H-03-reviewed `CORE_MVP_MANIFEST` byte-for-byte frozen while these mechanisms are candidate implementations; consume it as input and defer any revised implementation-status manifest to explicit review. | Pattern compilation, reduction, and comparison have distinct failure modes and trust claims. The existing content pin deliberately rejects changing the `mvp-1` trust boundary under the same revision. A compiled candidate can retain source-manifest identity and record termination/confluence/subject-reduction evidence without silently authorizing those claims. |
| D-027 | accepted | Compile reviewed rule variables to deterministic numeric slots and selected semantic owners to rigid backend-neutral heads. Accept a runtime rule only when it eliminates exactly one matching full projection through its evaluator, introduces the corresponding capped projection, does not duplicate any matched variable, and has a rigid discriminator from every other reviewed left pattern. Publish the immutable result as an H-04-pending candidate with evidence, not authorized metatheoretic claims. | TSK-2A compiles exactly three rules from `CORE_MVP_MANIFEST`, indexes all three beneath `functor-object`, rejects non-runtime authority, duplicate/unknown variables, excluded/arity-invalid owners, variable duplication, invalid projection decrease, and manifest drift, and records non-left-linearity plus the still-oracle-only subject-reduction boundary. |
| D-028 | accepted | Match compiled variables by numeric slot and repeated occurrences by provenance-insensitive structural Core equality; match rigid owners and schema plicity exactly. Permit executable rewriting only through the content-hashed `CORE_MVP_RUNTIME_PROGRAM`, in root-bucket and manifest order. Rebuild right patterns with schema plicity, preserve captured subtrees, derive introduced-node provenance from the redex span, and expose a head-only evaluator with a caller-supplied nonnegative safe-integer step bound. | All three reviewed heads rewrite deterministically to their exact capped forms. Repeated-variable, plicity, wrong-root, capped-form, and malformed-limit boundaries remain explicit. Zero fuel distinguishes a reducible head from an already normal one, and nested redexes are deliberately untouched. The existing structural checker cannot yet infer every full evaluator redex without the classifier conversion deferred to TSK-2C, so TSK-2B records exact elaborated result classifiers and bounded Lambdapi agreement without silently integrating conversion or claiming subject reduction. |
| D-029 | accepted | Define candidate equality as alpha-invariant structural Core equality closed under congruence and exactly the reviewed runtime head evaluator. Share one explicit reduction budget across both sides and every recursively compared child, preserve the first deterministic mismatch/exhaustion path, and let `CoreChecker` discharge a constraint only when that comparison returns equal. Use a fixed exported 256-step checker bound. Execute no proof-time comparison, intentional non-conversion evidence, excluded-owner rule, declaration unfolding, or generic-call beta. | TSK-2C1 compares all three rules symmetrically, shares fuel across nested redexes, reports rigid mismatch and limit paths, and makes the checker accept a reviewed conversion while continuing to reject the constant-section runtime non-conversion. Existing checker/meta tests remain green. The restricted comparison is a candidate implementation over the H-03 fragment, not a claim of complete dependent-type conversion. |
| D-030 | accepted; H-04 approved 2026-07-24 | Authorize a termination claim only for the exact three H-03 runtime rules on finite Core syntax: the global number of full projection owners strictly decreases because every rule removes one explicit full owner and duplicates no matched subtree. Authorize deterministic bounded evaluation/comparison and exactly those trusted rules. Withhold a general confluence claim: pairwise root discrimination is not a nested-critical-pair proof for non-left-linear patterns. Withhold a standalone TypeScript subject-reduction theorem: exact elaborated classifiers and bounded Lambdapi differential probes are evidence, but full-redex checking still needs active classifier computation outside the frozen runtime rules. Keep Lambdapi as the subject-reduction oracle. | The user approved H-04/D-030 exactly as proposed. TSK-2C2 records that decision in the distinct deep-frozen `CORE_RUNTIME_H04_REVIEW`: termination, bounded evaluation/comparison, and exactly three rules are authorized; confluence and TypeScript subject reduction remain withheld; Lambdapi remains the oracle. The H-03 manifest, candidate program, pre-review recommendation, and their `claimsAuthorized: false` history remain unchanged. |
| D-031 | accepted | Interpret TSK-3's common frozen fragment as exactly the 16 H-03-reviewed owners and three runtime rules, not the 24-owner conformance superset. Pin one immutable exit matrix. Give every common owner a positive judgment and a well-scoped negative result-type judgment over the same Core term in both engines; give every rule a positive conversion, well-typed near-miss non-conversion, and malformed candidate rejection; close with recursive functor-hom and native transfor-level higher-cell packages. Batch cases into bounded probes. | TSK-3A derives the exact owner/rule matrix from the reviewed manifest, rejects scope drift, and builds one deterministic owner corpus. The TypeScript checker and one Lambdapi `assert`/`assertnot` probe agree on all 16 positive and 16 negative owner judgments. Existing tests over all 24 owners remain useful conformance evidence but do not redefine product parity. |
| D-032 | accepted | For each TSK-3B row, use the exact reviewed redex/reduct as the positive pair. Form the negative pair by replacing only the redex's full-projection functor with a fresh rigid declaration of the identical classifier, and pair it with a malformed candidate whose left pattern erases that required full projection. Establish TypeScript well-typedness by the surface-elaborated redex plus checked same-classifier substitution; do not add the active classifier equations needed for standalone full-redex checker replay. Require zero-step TypeScript non-conversion and a Lambdapi `assertnot` over the same negative pair. | All three positive pairs convert in one TypeScript runtime step and in Lambdapi. All three substituted terms are irreducible and differ from their reducts at zero steps; Lambdapi accepts the corresponding non-conversions. The runtime compiler rejects the broadened candidates: two fail the mandatory full-projection decrease and the transfor-hom candidate first exposes its now-unbound `eta`. Direct Core-checker replay still encounters the H-04-recorded object-classifier equation boundary, so TSK-3B records the narrower substitution evidence and does not broaden trusted conversion or claim standalone subject reduction. |
| D-033 | accepted | Close the frozen TSK-3 matrix with exactly two higher-cell packages. Reuse the ordinary full/capped functor-hom schema recursively for the 2-cell package, and use the native transfor component/hom owners for the second package. Share nine positive typings, three exact wrong-endpoint negative typings, and three reviewed conversions between TypeScript surface elaboration/runtime comparison and one bounded Lambdapi probe. Publish a deep-frozen completion record tied to every scope row, while retaining the oracle until graduation. | The actual terms and types exercise every owner named by both package rows. The recursive conversion uses `projection.functor-hom.evaluate` at the next hom level without a new `fapp2`; the component and hom conversions use the other two reviewed rules. TypeScript rejects all three wrong operands at their source spans, and Lambdapi accepts the same corrupt Core terms as negative typing judgments. The completion status is only for the 16-owner H-03 frozen fragment: C-09/C-10 remain conformance evidence outside that denominator, no broader grammar-representativeness claim is made, and H-04 remains unchanged. |
| D-034 | accepted | Split MIGRATE-1 into four bounded claims: closed-world inventory plus generic proof-state inspection (MIGRATE-1A), locally nameless higher-order pattern solving (MIGRATE-1B), checked proof refinement (MIGRATE-1C), and a final replacement/readiness audit (MIGRATE-1D). Preserve only independently useful invariants; do not port generic beta/eta, dynamic user inductives/rules, the legacy parser, or category compatibility APIs through this migration. | `LEGACY_MIGRATION_INVENTORY` classifies all ten mechanisms, all thirteen root legacy source files, and all twenty-two loaded legacy test files, and rejects drift. Core-native proof inspection follows session solutions, reports only reachable metas and goal-type dependencies, records local depth/source provenance, and traverses only generic Core constructors. All four MIGRATE-1 slices are complete; physical deletion remains the separate MIGRATE-2 tranche. |
| D-035 | accepted | Solve only contextual Miller flex-rigid equations whose meta spine has its creation arity and consists of pairwise-distinct in-scope bound variables in a descendant context. Invert that spine by capture-safe ambient De Bruijn remapping, require a structural substitution round trip, and assign only through the existing canonical session solve. Keep non-variable and repeated spines plus unrelated context lineages stuck; reject omitted-local scope escape and occurs cycles; keep flex-flex ambiguous and the public direct-solve API canonical-only. | `invertCoreMetaPattern` is pure and has no assignment, checker, evaluator, or backend dependency. Session constraints solve weakened, exchanged, partially used, constant, nested-binder, and either-orientation occurrences; focused negatives distinguish stuck from rejected outcomes at source provenance. No generic beta/eta, ambient user-rule matching, runtime conversion, trusted rule, or H-04 claim is added. |
| D-036 | accepted | Represent an interactive proof by an immutable Core root plus reachable session-owned goal identities and their persistent creation contexts. `exact` uses the closed checker boundary and introduces no metas. `intro` preserves the syntactic Pi binder's full mode and creates one checked body goal. `apply` requires an inferable complete callee, exhausts its syntactic Pi telescope into ordered argument metas, then lets dependent result checking solve any determined arguments. Permit open results only through a dedicated checker refinement boundary, and make every tactic failure-atomic by restoring solutions, constraints, allocations, and ordinals. | `CoreProofRefiner` can solve exact goals, build and close an identity by intro/exact, expose explicit and implicit premises in order, and close a dependent application by unification. It rejects ill-typed exact terms, unresolved exact terms, non-Pi intro, non-function apply, unreachable goals, and a partially solved mismatching apply without changing the proof state. There is no mutable hole, global definition lookup, category-tag traversal, generic beta/eta, proof-time comparison rule, or Lambdapi backend dependency. |
| D-037 | accepted | Treat MIGRATE-1D as a frozen pre-deletion contract rather than physical deletion itself. Require every port/reimplementation mechanism to be covered by surviving v3.2 evidence, every delete mechanism to be explicitly ready, the thirteen-source/twenty-two-test/one-helper deletion graph to be closed, all direct and transitive consumers to be named, and every replacement-focused checkpoint gate to pass. MIGRATE-2 must rewrite consumers and remove the parser-only dependency without introducing a D0/D1 or legacy category compatibility barrel. | `LEGACY_MIGRATION_READINESS` pins all 36 deletion targets, the root runner and audit transitions, the standalone template API/example/documentation, `package.json`, the shared lockfile, the exact validation commands, and the retained Lambdapi authority boundary. Executable import-graph tests prove that `src/v3_2` and all v3.2 tests are legacy-independent; the only external direct importers are the root runner and template barrel, while the template app is the recorded transitive consumer. The audit discovered the previously implicit template rewrite and `parsimmon` cleanup before deletion rather than after breakage. |
| D-038 | accepted | Execute MIGRATE-2 as the exact D-037 cut: remove all 36 frozen targets, retain the MIGRATE-1D inventory/readiness records as historical audit inputs, and publish a distinct frozen completion result. Give browser consumers a narrow v3.2 product entry point containing the session/checker/Core path but excluding process-backed probes, differential harnesses, and migration APIs. Preserve the reviewed manifest hash while validating its canonical content directly, so the product checker has no Node-only crypto dependency. Rewrite—not emulate—the standalone example, remove `parsimmon` through pnpm, and retain no legacy compatibility API. | Every target is absent and every surviving import is audited against the deletion set. `src/v3_2/browser.ts` reaches the checker, session, runtime, and manifest with no `node:` import and cannot reach probe/differential/migration modules. Its focused consumer checks a category-polymorphic identity and session isolation; the standalone fixture passes strict TypeScript and a Vite production build. Manifest drift tests remain green with the same reviewed SHA-256 pin, the root runner loads only v3.2 suites, active/historical docs are labeled correctly, and `LEGACY_MIGRATION_COMPLETION` rejects deletion/edit/dependency/browser-boundary drift. |
| D-039 | accepted; H-05 approved 2026-07-24 | Graduate the TypeScript checker/evaluator as the authoritative deployed runtime kernel only for the exact content-pinned `emdash-v3.2-mvp-1` profile: sixteen owners and three H-04-authorized runtime rules, through the narrow browser API, with no production Lambdapi dependency. Retain Lambdapi as active mathematical specification, fixed-corpus CI and subject-reduction oracle, and an ongoing acceptance authority for five selected boundary changes: selected owner signatures; selected rule shape or authority; owner/rule promotion; termination, confluence, or subject-reduction claims; and shared-corpus backend bindings. Refactors, surface/diagnostic work, and packaging changes that preserve the frozen semantic/import boundaries need no new declaration-level authority review. | The user approved H-05/D-039 exactly as proposed. `CORE_MVP_GRADUATION_REVIEW` is the distinct deep-frozen GRADUATE-1B record: it snapshots the unchanged `authorityAuthorized: false` proposal, authorizes deployed TypeScript ownership only for the exact manifest identity, retains every approved Lambdapi role and trigger, forbids production runtime coupling, and preserves all H-04 theorem non-claims. It authorizes no additional owner/rule or performance SLA, does not declare RELEASE-READY, and names that tranche as the next slice. |
| D-040 | accepted | Split RELEASE-READY into source-mapped conformance diagnostics (RELEASE-1A), mandatory shared-fragment oracle wiring plus documentation/example/policy synchronization (RELEASE-1B), and a final drift-checked release-completion record with performance-claim scope and full gates (RELEASE-1C). Start with C-18 because diagnostic parsing is an implementation boundary independent of the approved acceptance policy. | Lambdapi diagnostics have an observed `[probe-path:line:start-end]` location form, while `SerializedProbe.sourceMap` already owns exact generated statement lines and original spans. RELEASE-1A can therefore preserve raw diagnostics, map only the exact temporary probe path and exact statement line, expose structured mappings, and prepend source-facing annotations without changing Core, the browser runtime, or any mathematical authority. CI policy and release claims remain separate reviewable changes. |
| D-041 | accepted | Keep `check:ts` as the Lambdapi-independent development baseline, add a separate 60-second `check:conformance` over the exact three TSK-3 shared-corpus suites with every oracle process enabled, and make that command mandatory inside `check:all`. Freeze the post-graduation policy separately from the historical TSK-3 completion and H-05 review. Expose only the already-frozen MVP manifest through the Node-free browser barrel; keep policy, probes, and differential harnesses outside it. | `CORE_MVP_RELEASE_POLICY` pins the H-05 profile, 16/3/2 corpus dimensions, three exact test files, required oracle roles and five triggers, synchronized public artifacts, diagnostic state, parser/review-gate state, and all theorem/performance non-claims. Package-script drift and public-document/example drift are executable failures. The mandatory command passes 19 tests / 3 suites with three actual Lambdapi processes and no skips in 3.5 seconds; the standalone TypeScript/Vite consumer remains green and shows `CORE_MVP_MANIFEST.revision`. |
| D-042 | accepted | Declare RELEASE-READY only for the exact H-05 profile after all 21 capability rows, RELEASE-1A diagnostics, RELEASE-1B policy, browser packaging, and the complete repository gate are green. Treat KERNEL-DISPLAYED-1/2 and H-02 as conditional on the absent displayed-owner failure, and H-06 as conditional on measured parser need; they are not release blockers. Treat the 256-step comparison limit as an operation budget, authorize no wall-clock/latency/throughput/scale promise, and require representative measurement plus separate review before a future performance claim. | `CORE_MVP_RELEASE_COMPLETION` is a new deep-frozen RELEASE-1C record rather than a mutation of the non-ready graduation/policy history. It pins zero release blockers, both untriggered future gates, eight out-of-profile capabilities/claims, the retained Lambdapi policy, exact H-04 claim ceiling, all final validation commands, and `releaseReady: true` with no next slice. Tests derive all 21 completed capability rows and final release-ledger state from this plan and keep the completion artifact outside the browser barrel. |

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
| Proof-state traversal/refinement | reimplemented through MIGRATE-1C | Generic reachable-goal traversal plus failure-atomic checked exact/intro/apply, with no old category tags or mutable global holes |
| Direct TypeScript constructors | port | Source-location and macro-expansion tests |
| Existing category constructors/rules | delete after replacement coverage is recorded | No compatibility requirement; retain only independently generic tests |
| Global mutable standard-library/rule setup | delete | New session-owned rule manifest and deterministic reset-free tests |
| Legacy parser | defer/delete | Revisit only after surface/core contracts stabilize |

The inventory is not an instruction to mechanically extract old files. Clean
reimplementation is preferred whenever extraction would preserve the stale
union, ambient global state, or old mathematical assumptions.

MIGRATE-1A makes that inventory executable in
`LEGACY_MIGRATION_INVENTORY`. Its closed-world source ledger covers all
thirteen root `src/*.ts` files outside `src/v3_2/`; its test ledger covers
every non-v3.2 side-effect import in `tests/main_tests.ts` in runner order.
Replacement paths must exist, the whole record is deeply frozen, and any
content or coverage drift is rejected.

MIGRATE-1D advances that inventory to `ready-for-physical-deletion` and
publishes `LEGACY_MIGRATION_READINESS`. The latter pins the same thirteen
source files and twenty-two tests plus the now-legacy-only `tests/utils.ts`.
Its executable import audit closes their relative dependency graph, proves
the v3.2 implementation and tests do not import it, and records every required
runner, standalone-template, audit-lifecycle, package-manifest, and lockfile
edit. The old parser is ready to delete without replacement; H-06 applies
only if measured need later justifies a new v3.2 grammar.

MIGRATE-2 retains those pre-deletion records and adds
`LEGACY_MIGRATION_COMPLETION`. The completion record derives all 36 removed
paths and all required edits from the frozen readiness artifact, records the
removed parser dependency and browser entry point, states that no
compatibility API survives, and makes GRADUATE-1 the next boundary.

| Legacy test file | Disposition | Retained invariant or boundary |
| --- | --- | --- |
| `equality_tests.ts` | split then delete | Structural alpha equality is replaced; generic beta/eta stay outside H-04. |
| `dependent_types_tests.ts` | split then delete | Keep dependent Pi checking/implicit recovery, not the legacy Vec declarations. |
| `error_reporting_tests.ts` | replace then delete | Core context/session/checker tests cover unbound, mismatch, non-function, occurs, and source diagnostics. |
| `rewrite_rules_tests.ts` | split then delete | Keep immutable typed rule validation and bounded evaluation, not a global user-rule registry. |
| `rewrite_rules_tests2.ts` | delete without port | It adds no invariant beyond the preceding rewrite corpus. |
| `inductive_types.ts` | delete without port | Dynamic Nat/Bool/List declarations and user rules are outside the frozen MVP. |
| `equality_inductive_type_family.ts` | delete without port | Its Eq/J encoding is not the active v3.2 equality authority. |
| `elaboration_options_tests.ts` | delete without port | The legacy `normalizeResultTerm` compatibility option is not retained. |
| `higher_order_unification_tests.ts` | replace then delete | MIGRATE-1B replaces distinct-local-spine flex-rigid cases and occurs/scope/non-pattern negatives over contextual Core. |
| `higher_order_pattern_matching_tests.ts` | defer then delete | MIGRATE-1B records the relevant meta-pattern negatives; ambient higher-order user rewrite matching is not selected. |
| `implicit_args_tests.ts` | split then delete | Generic implicit recovery/ambiguity/occurs are replaced; dynamic injectivity flags are deleted. |
| `church_encoding_tests.ts` | split then delete | Direct dependent Pi/lambda construction is replaced; the encoding is not a compatibility corpus. |
| `church_encoding_implicit_tests.ts` | split then delete | Direct implicit Pi/lambda recovery is replaced; the encoding is not retained. |
| `let_binding_tests.ts` | defer then delete | Shadowing/substitution evidence is covered, but no reviewed Core `Let` node is selected. |
| `phase1_tests.ts` | delete without port | `MkCat` and `ComposeMorph` are obsolete category APIs. |
| `kernel_implicits_tests.ts` | replace then delete | Schema-driven owner recovery/clash tests replace the stale slot table. |
| `functorial_elaboration.ts` | delete without port | The old `MkFunctorTerm` proof/coherence contract is explicitly rejected. |
| `proof_mode_tests.ts` | replace then delete | MIGRATE-1A/1C replace goal inspection and checked exact/intro/apply over session-local Core. |
| `emdash2_functor_transfor_tests.ts` | replace then delete | Current owner/binder/differential corpora replace stale category spellings and reductions. |
| `emdash2_homd_curry_alias_tests.ts` | split then delete | Keep binder modes/internal-Hom variance, not the alias API. |
| `emdash2_internalized_category_layer_tests.ts` | replace then delete | Current recursive category recovery and owner typing replace this layer. |
| `parser_tests.ts` | defer then delete | Delete the old grammar; a new v3.2 parser requires H-06. |

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
| C-11 | Metavariable/implicit solving over Core | complete for the bounded structural and Miller-pattern fragments through MIGRATE-1B | Session isolation, contextual scope, deterministic order, generic/owner implicit recovery, and nested partial calls remain green. Flex-rigid constraints now invert distinct contextual variables through weakening, exchange, partial use, and internal binders; non-variable, repeated, scope-escaping, occurs, flex-flex, and unrelated-lineage boundaries remain explicit. No general higher-order unification is claimed. |
| C-12 | Context extension and displayed type | complete for the bounded ELAB-2B interpretation | A context category, displayed-family declaration, local dependent section, and substitution pullback survive persistent Core contexts and the checker; reversed substitution is rejected; meta-level telescope substitution remains distinct from internal displayed reindexing. Structural weakening/exchange/contraction remain C-14 through C-16. |
| C-13 | Constant displayed family comparison | complete | Constant pullback reduces at runtime; constant sections check through the ordinary route only by active proof-time unification; the TypeScript structural checker and Lambdapi `assertnot` both preserve the required runtime non-collapse. |
| C-14 | Dependent weakening | complete for meta-level telescopes in ELAB-2C | An unused dependent-context extension maps prior terms/types into the deeper scope; the checked section consumer and generated Lambdapi abstraction pass without an internal structural owner. |
| C-15 | Dependency-respecting exchange | complete for meta-level telescopes in ELAB-2C | Adjacent swaps at zero and nonzero positions transport dependent suffixes; a newer type that uses the older binder is rejected at that occurrence. |
| C-16 | Dependent contraction/diagonal | complete for structurally equal telescope binders in ELAB-2C | The explicit non-injective index map transports a dependent suffix and identifies both duplicate occurrences; unequal types, unequal modes, and invalid positions are rejected. Definitional type comparison remains TSK-2 work. |
| C-17 | TypeScript rule manifest/checker | complete for the reviewed MVP fragment | The exact 16-owner/three-rule product profile compiles and executes through deterministic numeric-slot matching, manifest-ordered root buckets, explicit step limits, structural congruence, and checker conversion. H-04 authorizes termination, bounded evaluation/comparison, and exactly those three runtime rules. Proof-time/non-conversion evidence, excluded owners, unfolding, and generic beta remain non-executable; general confluence and standalone TypeScript subject reduction remain withheld. |
| C-18 | Source-mapped backend diagnostics | complete | Every serialized declaration/assertion/conversion kind has an exact generated-line entry. Lambdapi location headers for the exact temporary probe path now map to structured original spans and source-facing diagnostics while preserving unmodified raw output; ANSI, relative/absolute path, duplicate, imported-authority, comment/blank, and unmapped-line boundaries are covered. |
| C-19 | Legacy category-layer removal | complete | The exact thirteen legacy sources, twenty-two obsolete tests, and one helper are deleted. The root runner, standalone browser fixture, package manifest/lockfile, and audit lifecycle are migrated; every forbidden import and absent target is checked; no D0/D1, mutable-global reset, legacy parser, or category compatibility barrel remains. |
| C-20 | Frozen-fragment differential parity | complete | The manifest-derived 16-owner corpus, all three runtime rows, and both higher-cell packages have shared TypeScript/Lambdapi positive, negative, and conversion outcomes. The drift-checked completion record retains Lambdapi as required oracle until graduation and does not promote conformance-only C-09/C-10 owners. |

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
| ELAB-2C | complete; H-01 approved | ELAB-2B, reviewed D-007 | Capture-safe ambient index maps implement weakening, dependency-permitted exchange, and structurally justified contraction over persistent dependent telescopes. Positive, negative, nonzero-position, checker, and Lambdapi consumers are green; no displayed-owner failure or H-02 trigger was found. |
| KERNEL-DISPLAYED-1 | conditional | ELAB-2C failure evidence | If a concrete uniform elaboration consumer cannot be expressed, design and probe the smallest displayed structural owner package under the v3.2 SOP, including degeneration/comparison and non-collapse cases. Human review is required before promotion. |
| KERNEL-DISPLAYED-2 | conditional | reviewed KERNEL-DISPLAYED-1 | Promote only reviewed kernel changes with diagnostics, warning comparison, audits, catalogs, health, examples, and CI synchronized. |
| TSK-1 | split | ELAB-1 schema stability, ELAB-2A | The manifest tranche is split at H-03 so an implementation proposal cannot silently become the frozen trusted fragment. |
| TSK-1A | complete | ELAB-1 schema stability, ELAB-2A | Immutable backend-neutral manifest vocabulary, exact 16/8 owner partition, three runtime candidates, proof-time/non-collapse evidence, focused malformed rejection, complete backend provenance, and an exact H-03 recommendation are green; no evaluator or freeze was implemented. |
| TSK-1B | complete; H-03 approved | TSK-1A, reviewed fragment | The separate `emdash-v3.2-mvp-1` product manifest snapshots the reviewed 16 signatures and three runtime rules, pins their full boundary by content hash, rejects review/profile drift, and records implemented, deferred, and outside-kernel mechanisms without evaluating a rule. |
| TSK-2 | complete | TSK-1B | The evaluator tranche is split at compilation, reduction, comparison, and H-04 review boundaries so the H-03 manifest remains immutable and each trusted mechanism and claim receives independent malformed, determinism, and drift evidence. |
| TSK-2A | complete | TSK-1B | Exactly the three reviewed runtime rules compile into an immutable, backend-neutral, manifest-identity-bearing candidate program. Numeric slots, selected owners/arity, projection decrease, variable nonduplication, pairwise rigid discrimination, malformed rejection, deterministic rebuilding, and an explicit H-04-pending evidence boundary are green. |
| TSK-2B | complete | TSK-2A | Deterministic first-order matching, one-step product-program rewriting, and explicitly bounded head evaluation are green for all three reviewed rules. Repeated-variable, plicity, wrong-root, capped-form, nested-redex, invalid-bound, zero-fuel, exact-classifier, and Lambdapi differential consumers preserve the conversion/authority boundary. |
| TSK-2C | complete; split at H-04 | TSK-2B | Candidate comparison and the reviewed metatheory boundary remain separate so implementation evidence cannot silently authorize its own trust claims. |
| TSK-2C1 | complete | TSK-2B | Structural-plus-runtime congruence with global fuel, deterministic diagnostics, checker integration, strict termination measure, explicit authority negatives, and the immutable D-030 recommendation are green. |
| TSK-2C2 | complete; H-04 approved | TSK-2C1, reviewed D-030 | The distinct drift-checked H-04 review artifact authorizes only the approved termination/mechanism/rule boundary, preserves both withheld claims and the Lambdapi oracle, and leaves the H-03 manifest and candidate history unchanged. |
| TSK-3 | complete | TSK-2 | Differential parity is split into exact owner judgments, rule boundaries, and higher-cell closure so every claim uses one shared TypeScript/Lambdapi corpus and a bounded oracle probe. |
| TSK-3A | complete | TSK-2 | The immutable manifest-derived exit matrix covers exactly 16 owners, three rules, and two higher-cell packages. One shared owner corpus passes 16 positive and 16 negative result-type judgments in both TypeScript and Lambdapi; matrix drift is rejected. |
| TSK-3B | complete | TSK-3A | Each reviewed rule now has one shared redex/reduct conversion, a rigid same-classifier near-miss rejected by both conversion engines, and a broadened malformed candidate paired directly with that oracle-side absence witness. The known standalone classifier-computation gap remains explicit rather than becoming an unreviewed checker rule. |
| TSK-3C | complete | TSK-3B | The two exact packages share nine positive typings, three wrong-endpoint negatives, and three higher-level conversions between TypeScript and Lambdapi. Actual owner occurrence, recursive ordinary-schema reuse, completion drift, and the retained oracle policy are checked without broadening H-04. |
| MIGRATE-1 | complete | replacement inventory, TSK-2 | Independently useful proof/unification facilities are reimplemented, every legacy source/test is classified, and an exact surviving-evidence/import-consumer/package boundary is frozen before deletion. |
| MIGRATE-1A | complete | TSK-3 | The deep-frozen inventory covers ten mechanisms, thirteen root legacy source files, and all twenty-two loaded legacy tests. Generic proof inspection follows session solutions and goal-type dependencies through every Core container without old category tags or global state. |
| MIGRATE-1B | complete | MIGRATE-1A, stable Core binders | Pure capture-safe inversion and session assignment cover the contextual Miller flex-rigid fragment in both orientations. Weakening, exchange, partial use, constants, and nested binders pass; non-variable, repeated, escaping, occurs, flex-flex, unrelated-lineage, and direct-solve boundaries are explicit without runtime conversion. |
| MIGRATE-1C | complete | MIGRATE-1B, proof-state inspection | Reachable session goals retain their creation contexts; exact, intro, and exhaustive-Pi apply are checker-validated and failure-atomic. Complete, dependent, plicity, source-error, unreachable, and rollback consumers are green without mutable holes or global lookup. |
| MIGRATE-1D | complete | MIGRATE-1B, MIGRATE-1C | The completed mechanism/test dispositions, 36-target deletion graph, surviving replacement evidence, isolated v3.2 graph, direct/transitive consumers, package cleanup, audit transitions, full gate list, and retained Lambdapi boundary are deep-frozen and drift-checked. |
| MIGRATE-2 | complete | MIGRATE-1, replacement tests | All 36 frozen legacy targets are absent; every recorded runner/template/audit/package edge is migrated; the narrow browser product path is Node-free and build-validated; no D0/D1 or legacy category compatibility API remains. |
| GRADUATE-1 | complete | TSK-3, MIGRATE-2 | The graduation recommendation and its human authorization remain separate so evidence cannot authorize its own product/trust boundary. |
| GRADUATE-1A | complete; recommendation published | TSK-3, MIGRATE-2 | The drift-checked D-039 proposal reviews parity, H-04 claims, bounded operations, browser deployment, maintenance cost, performance non-claims, residual work, and the exact ongoing Lambdapi acceptance triggers. It grants no authority before H-05. |
| GRADUATE-1B | complete; H-05 approved | GRADUATE-1A, reviewed D-039 | The distinct immutable review artifact records the exact approval, deployed profile, retained Lambdapi roles/triggers, forbidden runtime dependency, H-04 non-claims, and remaining release boundary without rewriting the proposal. |
| RELEASE-READY | complete | GRADUATE-1B | The exact `emdash-v3.2-mvp-1` profile has source-mapped diagnostics, mandatory bounded conformance, synchronized public policy/example/manifest identity, explicit residual and performance boundaries, green browser packaging, and full repository validation. |
| RELEASE-1A | complete | GRADUATE-1B | C-18 preserves raw Lambdapi output while mapping exact temporary-probe diagnostic locations back to structured source spans and source-facing text. Synthetic ANSI/relative/absolute/duplicate/unmapped cases and one bounded real failure are green without touching the browser runtime. |
| RELEASE-1B | complete | RELEASE-1A | `check:conformance` enables every oracle process in the exact TSK-3 owner/rule/higher-cell suites under one 60-second bound, and `check:all` requires it. A drift-checked policy binds the approved profile and retained Lambdapi roles to package scripts, public docs, browser manifest identity, and the standalone example without introducing runtime coupling. |
| RELEASE-1C | complete | RELEASE-1B | The distinct frozen completion record validates all predecessor boundaries, records zero blockers, preserves conditional future gates and explicit exclusions, scopes the 256-step operation budget without a performance SLA, pins final commands, and closes RELEASE-READY only for the exact approved profile. |

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
`assertnot` preserve that boundary. D-007 therefore remained pending at the
ELAB-2B checkpoint; the user approved H-01 dependent-first on 2026-07-24, so
ELAB-2C may now proceed without changing that boundary.

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
Decision at this checkpoint: accept the bounded implementation and recommend
  dependent-first for H-01. Keep the TypeScript checker structural until
  TSK-2 and leave ELAB-2C gated pending review. H-01 was subsequently approved
  by the user on 2026-07-24.
Plan rows changed at this checkpoint: D-007 recommended/H-01 pending; D-021
  accepted; C-12 and C-13 complete for their bounded evidence; ELAB-2B
  complete; ELAB-2C gated; TSK-1 split at H-03 and independent TSK-1A
  dependency-ready.
Remaining prerequisite or human review at this checkpoint: H-01 review of
  D-007, subsequently resolved on 2026-07-24.
```

## Completed Slice: TSK-1A

TSK-1A introduced:

- `src/v3_2/manifest.ts`, containing a deeply immutable, closed-world proposal
  vocabulary for signature membership, runtime reduction, proof-time
  comparison, intentional non-conversion, semantic provenance keys, consumer
  coverage, explicit owner/rule-family exclusions, and H-03 recommendations;
- a complete ordered partition of the 24-owner conformance catalog into a
  dependency-closed 16-owner ordinary classifier/projection candidate and
  eight conformance-only owners with concrete consumers, reasons, and open
  risks;
- exactly three candidate runtime rules: evaluation of the full ordinary
  functor hom action, full transfor component, and full off-diagonal transfor
  hom action to their capped projections;
- one constant-section proof-time comparison and the paired intentional
  runtime non-conversion as non-executable data, preserving the ELAB-2B
  authority boundary;
- validation of proposal status, complete owner coverage, catalog order,
  signature dependency closure, consumer references, rule/evidence identity,
  owner arity, declared-variable use, runtime right-side scope, authority
  shape, candidate-owner membership, exclusion order, and exact
  recommendation synchronization;
- `LAMBDAPI_V32_RULE_EVIDENCE_BINDINGS`, which keeps active spellings, source
  sections, owning runtime/unification declarations, and the durable negative
  probe out of backend-neutral Core while requiring one complete binding for
  every semantic evidence key;
- `tests/v3_2_manifest_tests.ts`, with positive manifest/provenance checks and
  focused unknown, duplicate, incomplete, reordered, dependency-escaping,
  malformed-arity, unbound-variable, runtime-RHS/proof-consequence scope,
  cross-class, excluded-owner, recommendation-drift, and backend-binding
  negatives.

The H-03 recommendation is exact:

```text
Status: proposal-awaiting-h03 (not frozen)

Candidate signature owners (16):
  groupoid-universe, category-universe, decode, object-classifier,
  functor-classifier, hom-classifier, transfor-classifier, hom-category,
  transfor-category, functor-object, functor-hom-full,
  functor-hom-capped, transfor-component-full,
  transfor-component-capped, transfor-hom-full, transfor-hom-capped

Candidate runtime rules (3):
  projection.functor-hom.evaluate
  projection.transfor-component.evaluate
  projection.transfor-hom.evaluate

Candidate proof-time rules:
  none

Conformance-only owner extensions (8):
  category-of-categories, opposite-category,
  displayed-category-category, internal-hom-source, internal-hom-target,
  displayed-pullback, constant-displayed-family, section-category

Required conformance boundary:
  comparison.constant-section is proof-time evidence only;
  nonconversion.constant-section.runtime must continue to hold.
```

This boundary is smaller than the elaborator/conformance catalog by design.
The ordinary subset already owns the recursive 2-cell consumer and its three
generic projection betas. The category-of-categories, opposite/internal-hom, and
displayed/dependent extensions have useful checked consumers, but their
runtime and proof-time neighborhoods include rules whose complete need,
termination, confluence, or subject-reduction scope has not been bounded.
The closed-world default excludes every active rule not named in the proposal;
serializability never implies product-kernel membership.

The legacy TypeScript engine was inspected only for generic evidence. Its
rewrite and unification rules live in ambient mutable registries; rewrite-rule
registration catches and logs some failures instead of establishing an
immutable manifest, and unification rules may create fresh holes for variables
appearing only in consequences. TSK-1A therefore cleanly reimplements the
proposal boundary and rejects runtime RHS scope escape instead of extracting
that machinery or extending its stale category theory.

No evaluator, matcher, proof-time solver, rule freeze, kernel declaration,
kernel rule, warning baseline, generated catalog, package setup, or old
category-layer deletion changed in this slice.

### Experiment TSK-1A-CLOSED-WORLD-MANIFEST

```text
Experiment ID: TSK-1A-CLOSED-WORLD-MANIFEST
Date and checkpoint: 2026-07-24 at ELAB-2B checkpoint 0f176cb
Question/hypothesis: a small, dependency-closed product signature and its exact
  first runtime rules can be proposed as immutable backend-neutral data while
  preserving proof-time and non-conversion evidence outside the executable
  fragment and without implementing evaluation.
Authority and owner position inspected: active declarations and dependent
  signatures for all 24 semantic owners; the three generic full-to-capped
  projection beta rules; the Cat_cat hom presentation of ordinary functor
  categories; the constant-section Pi/Functor unification rule; the durable
  ELAB-2B assertnot probe; current SOP, Foundations, canonical-syntax report,
  active plan, and legacy generic rewrite/unification implementation. No
  Lambdapi declaration or rule changed.
Branch/worktree and baseline: goal/typescript-elaborator-v3.2 in
  /home/user1/emdash1-elaborator-goal at 0f176cb before the experiment;
  descendant of baseline a06433e.
Minimal positive consumer: encode the three active generic projection betas as
  scoped semantic owner patterns over the 16-owner ordinary subset, with one
  proof-time constant-section comparison and one paired runtime non-conversion
  retained as conformance evidence.
Relevant negative/non-collapse consumer: reject unknown or duplicate owners,
  incomplete/reordered catalogs, signature dependencies on excluded owners,
  duplicate/noncanonical/reordered rule IDs, unknown or wrong-arity owner
  patterns, undeclared, runtime-RHS-only, and proof-consequence-only variables,
  cross-class executable records, candidate rules using excluded owners,
  recommendation drift, and missing/unknown/cross-class backend provenance.
  Keep the constant-section category pair proof-time comparable but not
  runtime convertible.
Probe command and bounded result:
  timeout 60s env EMDASH_RUN_LAMBDAPI_PROBES=1 node --require
    ts-node/register --test tests/v3_2_core_binder_tests.ts
    tests/v3_2_core_checker_tests.ts tests/v3_2_core_context_tests.ts
    tests/v3_2_core_session_tests.ts tests/v3_2_core_signature_tests.ts
    tests/v3_2_dependent_context_tests.ts tests/v3_2_elab0_tests.ts
    tests/v3_2_elab1c_tests.ts tests/v3_2_manifest_tests.ts
  passed 110 tests in 9 suites, including every opt-in Lambdapi probe.
Observed result: the 16-owner subset is signature-dependency-closed; the three
  runtime patterns refer only to selected owners; proof-time and non-conversion
  records remain non-executable; all malformed cases fail with focused stable
  codes; exact backend evidence coverage validates separately.
Unexpected result or failure: none. The active proof-time category comparison
  needs both the Cat_cat hom presentation rule and the Pi/constant unification
  rule, so its backend evidence binding records both source owners rather than
  pretending the semantic Core pattern is a backend spelling.
TypeScript consequence: add an immutable proposal schema and validation only.
  Do not connect these records to CoreChecker or a reducer before TSK-1B/2.
Lambdapi consequence: retain exact declarations and the ELAB-2B negative probe
  as conformance provenance only; make no kernel change.
Warning/audit/catalog/health effects, if any: no Lambdapi source or generated
  authority changed, so no warning baseline, rule audit, catalog, or health
  artifact changed. The bounded kernel gate remained green.
Decision at this checkpoint: accept D-022 and recommend D-023 for H-03. Do
  not call the proposal frozen and do not begin TSK-2. H-03 was subsequently
  approved exactly as proposed on 2026-07-24.
Plan rows changed at this checkpoint: D-022 accepted; D-023
  recommended/H-03 pending; C-17 proposal complete but freeze/evaluator
  pending; TSK-1A complete; TSK-1B human-gated.
Remaining prerequisite or human review at this checkpoint: H-03 review of the
  exact 16-owner/three-runtime-rule fragment, subsequently resolved on
  2026-07-24. H-01 was resolved on the same date.
```

### TSK-1A validation

Validated on the exact TSK-1A worktree diff:

```text
node --require ts-node/register --test tests/v3_2_manifest_tests.ts
  passed 17 tests / 1 suite

timeout 60s env EMDASH_RUN_LAMBDAPI_PROBES=1 node --require
  ts-node/register --test tests/v3_2_core_binder_tests.ts
  tests/v3_2_core_checker_tests.ts tests/v3_2_core_context_tests.ts
  tests/v3_2_core_session_tests.ts tests/v3_2_core_signature_tests.ts
  tests/v3_2_dependent_context_tests.ts tests/v3_2_elab0_tests.ts
  tests/v3_2_elab1c_tests.ts tests/v3_2_manifest_tests.ts
  passed 110 tests / 9 suites with no skips

./scripts/pnpmw run check:ts
  workspace contract, TypeScript, ESLint, and root tests passed
  262 tests / 52 suites: 248 passed, 14 opt-in probes skipped

EMDASH_TYPECHECK_TIMEOUT=60s make -C emdash2 check
  active kernel, extensions, and diagnostics passed

EMDASH_TYPECHECK_TIMEOUT=60s ./scripts/pnpmw run check:all
  root TypeScript gate passed with the same 262-test result
  41 active Lambdapi kernel/example files passed
  39 formal infrastructure tests and 5 print registry tests passed
  active-reference/report-header/book/evidence/typography/KaTeX checks passed
  strict rule-LHS audit and generated catalog freshness passed

git diff --check
  passed
```

## Completed Slice: TSK-1B

The user approved H-03/D-023 exactly as proposed on 2026-07-24. TSK-1B
therefore introduced:

- `CORE_MVP_MANIFEST`, a distinct `frozen-reviewed` product profile at
  revision `emdash-v3.2-mvp-1`; the pre-review
  `CORE_MVP_MANIFEST_PROPOSAL` remains immutable audit evidence and is not the
  product-kernel input;
- independent deep-frozen snapshots of the exact 16 reviewed dependent owner
  signatures rather than mutable references to the 24-owner conformance
  catalog;
- independent snapshots of exactly the three reviewed runtime projection
  rules, with no proof-time rule or conformance-evidence record entering the
  executable profile;
- an exact H-03 approval record and a SHA-256 content pin covering status,
  revision, approval, signatures, rules, and the trust boundary, so a source
  change cannot silently retain the `mvp-1` identity;
- a machine-readable trust boundary. Core scope/substitution, structural
  signature checking, and closed-world manifest-structure validation are
  implemented shared kernel mechanisms. Runtime pattern compilation,
  executable-rule validation, weak-head evaluation, definitional comparison,
  and proof-time comparison remain frozen-but-deferred TSK-2 work. Surface
  elaboration, metavariables/constraints, conformance-only signatures and
  evidence, and the Lambdapi backend remain outside the trusted product
  kernel;
- focused rejection of status/revision, review decision, owner order,
  signature, rule, trust-boundary, and content-hash drift.

The general structural checker still accepts the full elaborator/conformance
catalog, and the Lambdapi backend still serializes it. Those are intentional
supersets: implementation or serializability does not grant product
membership. TSK-2 must consume `CORE_MVP_MANIFEST`, not the historical
proposal or the ambient 24-owner catalog, when it compiles and executes
rules.

The user also approved H-01 dependent-first on 2026-07-24. That decision does
not add displayed owners or proof-time bridges to this H-03 profile; it makes
ELAB-2C dependency-ready under the existing authority classifications.

No matcher, evaluator, definitional comparison, proof-time solver, Lambdapi
declaration/rule, warning baseline, generated catalog, package setup, or old
category-layer code changed in TSK-1B.

### Experiment TSK-1B-REVIEWED-FREEZE

```text
Experiment ID: TSK-1B-REVIEWED-FREEZE
Date and checkpoint: 2026-07-24 at TSK-1A checkpoint 829257c
Question/hypothesis: the exact H-03-approved proposal can become a durable
  closed-world product profile without mutating the historical proposal,
  importing backend spellings, or prematurely implementing rule execution.
Authority and owner position inspected: the current 24-owner arity and
  dependent-signature catalogs; all three active full-to-capped projection
  betas; constant-section proof-time/non-collapse evidence; active kernel,
  checks, SOP, Foundations, canonical-syntax report, handoff, and living plan.
  No Lambdapi declaration or rule changed.
Current worktree/branch and baseline relationship:
  /home/user1/emdash1-elaborator-goal on
  goal/typescript-elaborator-v3.2 at 829257c before the experiment;
  descendant of baseline a06433e.
Minimal positive consumer: validate and deep-freeze a separate product
  manifest containing independent snapshots of the reviewed 16 signatures
  and three runtime rules, exact H-03 approval metadata, and the explicit
  trusted-core boundary.
Relevant negative/non-collapse consumer: reject altered freeze status or
  approval, missing/reordered owners, changed signature structure, changed
  rule data, expanded/deleted boundary mechanisms, and an unreviewed content
  hash. Keep constant-section proof-time comparison and runtime
  non-conversion as conformance evidence outside the frozen rule list.
Observed result: the product profile contains exactly the approved data, has
  no backend spelling or source path, and is independently deeply frozen.
  Its SHA-256 content pin is
  28834e9c0361b98e9f14f66f02aac8f59900a98b9c8c1ce1c62ae0e5396f8ff0.
Unexpected result or failure: deriving snapshots from the live catalogs was
  runtime-immutable but would have allowed a later source revision to drift
  under the same `mvp-1` name. The content pin was added before broader
  validation so any such change requires an explicit reviewed revision.
TypeScript consequence: product-kernel work now has one exact reviewed
  manifest input. TSK-2 must compile/validate that input and must not infer
  product authority from the broader checker or backend catalogs.
Lambdapi consequence: retain all existing source evidence as conformance
  provenance only; make no kernel change.
Warning/audit/catalog/health effects, if any: no Lambdapi source or generated
  authority changed, so no warning baseline, audit, catalog, or health
  artifact changed.
Decision: accept D-024 and complete TSK-1B. Keep the three runtime rule
  declarations frozen but non-executable until TSK-2.
Plan rows changed: D-007 and D-023 accepted after user review; D-024 accepted;
  C-17 records the completed freeze but remains partial for evaluation;
  TSK-1B complete; ELAB-2C selected next; TSK-2 dependency-ready.
Remaining prerequisite or human review: none for ELAB-2C or TSK-2. H-02 is
  triggered only by concrete ELAB-2C failure evidence; H-04 remains at TSK-2.
```

### TSK-1B validation

Validated on the exact TSK-1B worktree diff:

```text
node --require ts-node/register --test tests/v3_2_manifest_tests.ts
  passed 26 tests / 2 suites

timeout 60s env EMDASH_RUN_LAMBDAPI_PROBES=1 node --require
  ts-node/register --test tests/v3_2_core_binder_tests.ts
  tests/v3_2_core_checker_tests.ts tests/v3_2_core_context_tests.ts
  tests/v3_2_core_session_tests.ts tests/v3_2_core_signature_tests.ts
  tests/v3_2_dependent_context_tests.ts tests/v3_2_elab0_tests.ts
  tests/v3_2_elab1c_tests.ts tests/v3_2_manifest_tests.ts
  passed 119 tests / 10 suites with no skips

./scripts/pnpmw run check:ts
  workspace contract, TypeScript, ESLint, and root tests passed
  271 tests / 53 suites: 257 passed, 14 opt-in probes skipped

EMDASH_TYPECHECK_TIMEOUT=60s make -C emdash2 check
  active kernel, extensions, and diagnostics passed

EMDASH_TYPECHECK_TIMEOUT=60s ./scripts/pnpmw run check:all
  root TypeScript gate passed with the same 271-test result
  41 active Lambdapi kernel/example files passed
  39 formal infrastructure tests and 5 print registry tests passed
  active-reference/report-header/book/evidence/typography/KaTeX checks passed
  strict rule-LHS audit and generated catalog freshness passed

git diff --check
  passed
```

## Completed Slice: ELAB-2C

ELAB-2C resolves the bounded structural part of the dependent-first context
experiment at the meta-level telescope layer selected by D-008:

- `kernelRemapAmbientIndices` maps a source ambient De Bruijn scope into a
  target scope while preserving occurrence provenance beneath internal
  binders. Permutations express exchange, repeated images express contraction,
  and a deeper target expresses weakening. A `null` image is a checked claim
  that the corresponding source variable is unused; encountering it reports
  the exact dropped occurrence instead of capturing it;
- `CoreTelescopeStructuralMap` records the immutable source context, rebuilt
  target context, exact nearest-first ambient index map, operation kind, and
  checked expression transport;
- weakening extends a persistent telescope by one unused nearest binder and
  shifts every prior ambient image into the target;
- adjacent exchange first removes the older variable from the newer binder's
  type. It succeeds only when that variable is absent, then permutes every
  later dependent binding type through the same map;
- adjacent contraction requires matching binder modes and requires the newer
  type to be structurally identical to the older type weakened into the newer
  owning scope. It then transports every later dependent binding type through
  an explicit non-injective diagonal map;
- invalid positions, dependency-forbidden exchange, unequal contraction
  types, and unequal contraction modes have distinct source-located context
  diagnostics.

The focused corpus exercises zero and nonzero structural positions, dependent
prefixes and suffixes, mapping beneath an internal lambda, checker inference
after each transport, persistence of the source context, and exact negative
provenance. A generated probe abstracts the weakened, exchanged, and
contracted dependent section consumers and all three are accepted by
Lambdapi with warnings enabled.

The active ordinary structural owners remain the stable
`Const_func_func`, `sym_func_func`, and `diag_func_func` declarations in
section 17c of `emdash2/emdash3_2.lp`. ELAB-2C does not use them: they are
internal ordinary categorical functors, not meta-level context operations.
The serialized ELAB-2C consumers contain none of those heads and introduce no
`Pullback_catd`. No concrete consumer failed, so there is no missing displayed
owner to record, no owner-position failure probe to promote, and H-02 is not
triggered. Displayed structural logic remains at the active SOP's deferred
boundary.

No Lambdapi declaration/rule, Core owner schema/signature/manifest, evaluator,
proof-time comparison, warning baseline, generated catalog, package setup, or
legacy category layer changed in ELAB-2C.

### Experiment ELAB-2C-DEPENDENT-TELESCOPE-STRUCTURE

```text
Experiment ID: ELAB-2C-DEPENDENT-TELESCOPE-STRUCTURE
Date and checkpoint: 2026-07-24 at TSK-1B checkpoint 3879c66
Question/hypothesis: dependent weakening, dependency-permitted exchange, and
  structurally justified contraction can be implemented uniformly as
  meta-level telescope maps, without confusing them with ordinary structural
  functors or inventing displayed kernel owners.
Authority and owner position inspected: active kernel and checks; section 17c
  ordinary owners Const_func_func, sym_func_func, and diag_func_func; the
  active SOP deferred displayed-structural boundary; Foundations' separation
  of ordinary weakening from const_section_func; D-007 through D-010 and
  C-14 through C-16 in this plan. No Lambdapi owner or rule changed.
Current worktree/branch and baseline relationship:
  /home/user1/emdash1-elaborator-goal on
  goal/typescript-elaborator-v3.2 at 3879c66 before the experiment;
  descendant of baseline a06433e.
Minimal positive consumer: transport a genuinely displayed section through
  an unused extension, an allowed adjacent swap with a dependent suffix, and
  a diagonal identifying two equal displayed-family binders; recheck each
  transported term and abstract all three into Lambdapi assertions.
Relevant negative/non-collapse consumer: reject an adjacent swap at the bound
  occurrence proving that the newer type depends on the older binder; reject
  contraction with unequal type or binder mode; reject invalid positions;
  verify that generated consumers contain no ordinary structural owner and
  no displayed pullback.
Observed result: nearest-first maps [1,2], [0,2,1], and [0,1,1] implement the
  primary weakening, exchange, and contraction consumers. Nonzero-position
  variants preserve dependent prefixes and suffixes. All checker and
  warning-enabled Lambdapi consumers pass.
Unexpected result or failure: none. The concrete consumers required no
  displayed structural owner, so an owner-position failure probe would invent
  rather than diagnose a kernel need.
TypeScript consequence: accept D-025 and expose a generic provenance-
  preserving ambient index-map primitive plus three persistent telescope
  operations. Keep contraction equality structural until TSK-2 supplies the
  reviewed conversion boundary.
Lambdapi consequence: retain the ordinary structural owners as separate
  internal operations and leave displayed structural logic deferred.
Warning/audit/catalog/health effects, if any: the generated ELAB-2C consumer
  passed with warnings enabled. No Lambdapi source or generated authority
  changed, so no warning baseline, rule audit, catalog, or health artifact
  changed.
Decision: accept D-025 and complete ELAB-2C without triggering
  KERNEL-DISPLAYED-1 or H-02.
Plan rows changed: D-025 accepted; C-14 through C-16 complete for the bounded
  meta-level telescope capability; ELAB-2C complete; TSK-2 selected next.
Remaining prerequisite or human review: none for TSK-2. H-02 remains
  conditional on a future concrete displayed-owner failure; H-04 remains the
  review gate reached by TSK-2.
```

### ELAB-2C validation

Validated on the exact ELAB-2C worktree diff:

```text
node --require ts-node/register --test
  tests/v3_2_telescope_structural_tests.ts
  passed 10 tests / 1 suite: 9 passed, 1 opt-in probe skipped

EMDASH_RUN_LAMBDAPI_PROBES=1 node --require ts-node/register --test
  tests/v3_2_telescope_structural_tests.ts
  passed 10 tests / 1 suite with no skips

EMDASH_RUN_LAMBDAPI_PROBES=1 node --require ts-node/register --test
  tests/v3_2_core_binder_tests.ts tests/v3_2_core_checker_tests.ts
  tests/v3_2_core_context_tests.ts tests/v3_2_core_session_tests.ts
  tests/v3_2_core_signature_tests.ts tests/v3_2_dependent_context_tests.ts
  tests/v3_2_elab0_tests.ts tests/v3_2_elab1c_tests.ts
  tests/v3_2_manifest_tests.ts tests/v3_2_telescope_structural_tests.ts
  passed 129 tests / 11 suites with no skips

./scripts/pnpmw run check:ts
  workspace contract, TypeScript, ESLint, and root tests passed
  281 tests / 54 suites: 266 passed, 15 opt-in probes skipped

EMDASH_TYPECHECK_TIMEOUT=60s make -C emdash2 check
  active kernel, extensions, and diagnostics passed

EMDASH_TYPECHECK_TIMEOUT=60s ./scripts/pnpmw run check:all
  root TypeScript gate passed with the same 281-test result
  41 active Lambdapi kernel/example files passed
  39 formal infrastructure tests and 5 print registry tests passed
  active-reference/report-header/book/evidence/typography/KaTeX checks passed
  strict rule-LHS audit and generated catalog freshness passed

git diff --check
  passed
```

## Completed Slice: TSK-2A

TSK-2A compiles the exact H-03-reviewed runtime fragment without yet matching
or rewriting a Core term:

- `compileCoreMvpRuntime` first revalidates the complete content-hashed
  `CORE_MVP_MANIFEST`; a changed status, approval, signature, rule, trust
  boundary, or hash is rejected before executable compilation;
- each textual rule variable becomes a deterministic numeric slot, and each
  owner application becomes a rigid semantic `CoreOwnerId` node. Compilation
  rechecks selected-owner membership and arity rather than relying only on the
  earlier manifest pass;
- every compiled rule carries a local safety certificate identifying its
  projection pair, evaluator owner, eliminated full owner, introduced capped
  owner, exact one-owner decrease, and left/right variable multiplicities;
- right-side multiplicities may not exceed left-side multiplicities, so a
  rewrite cannot duplicate a matched subterm;
- a conservative pairwise comparison requires a rigid disagreement between
  every pair of reviewed left patterns. All three rules remain indexed, in
  manifest order, beneath their common `functor-object` root;
- `compileCoreRuntimeRuleCandidate` exposes the same shape checks for
  diagnostics and future review without granting a candidate rule product
  membership. Only the full manifest compiler creates a runtime program;
- the deeply immutable program retains the exact manifest revision and
  content hash and is explicitly marked `candidate-awaiting-h04`.

The compiled evidence records that all three rules remove one explicit full
projection without variable duplication and have pairwise rigid root-pattern
discriminators. It also records that the rules are not left-linear, and that
subject reduction is currently supported only by the reviewed Lambdapi
provenance. `claimsAuthorized` remains false. These are inputs to H-04, not
premature termination, confluence, or subject-reduction claims.

The approved `emdash-v3.2-mvp-1` manifest remains byte-for-byte unchanged and
continues to describe runtime pattern compilation as deferred at the H-03
checkpoint. TSK-2A is a candidate implementation consuming that artifact; a
new implementation-status manifest revision requires separate review. No
matcher, rewrite step, evaluator, definitional comparison, proof-time engine,
checker conversion, Lambdapi declaration/rule, or backend spelling was added.

### Experiment TSK-2A-REVIEWED-RUNTIME-COMPILATION

```text
Experiment ID: TSK-2A-REVIEWED-RUNTIME-COMPILATION
Date and checkpoint: 2026-07-24 at ELAB-2C checkpoint 53d39a5
Question/hypothesis: the three H-03-reviewed projection betas can compile into
  a deterministic executable-shape program while the mvp-1 manifest and H-04
  trust claims remain unchanged.
Authority and owner position inspected: CORE_MVP_MANIFEST and its exact three
  runtime patterns; PROJECTION_PAIR_SCHEMAS; the active fapp0/full-to-capped
  Lambdapi owner rules and their already reviewed evidence bindings; TSK-1A,
  TSK-1B, D-022 through D-024, and the D-026 split. No Lambdapi source changed.
Current worktree/branch and baseline relationship:
  /home/user1/emdash1-elaborator-goal on
  goal/typescript-elaborator-v3.2 at 53d39a5 before the experiment;
  descendant of baseline a06433e.
Minimal positive consumer: compile all 16 selected owners and exactly three
  runtime rules into one immutable candidate carrying manifest identity,
  numeric slots, root buckets, projection-pair certificates, and pending H-04
  evidence.
Relevant negative/non-collapse consumer: reject manifest status/rule drift,
  non-runtime authority, duplicate or unknown variables, conformance-only or
  arity-invalid owners, right-side variable duplication, and a rule that does
  not eliminate exactly one matching full projection. Compile no proof-time
  or intentional non-conversion evidence.
Observed result: all three runtime rules compile under functor-object in
  manifest order. Each removes its matching full owner, introduces its capped
  owner, and reduces every variable multiplicity. Pairwise left comparisons
  find rigid discriminators.
Unexpected result or failure: the rules are intentionally non-left-linear
  because category, endpoint, functor, and transfor variables recur to enforce
  exact owner relationships. Root-pattern discrimination alone is therefore
  not a confluence proof; the candidate records this explicitly for H-04.
TypeScript consequence: accept D-027 and use the immutable compiled program
  as TSK-2B input. Keep the standalone candidate compiler non-authorizing.
Lambdapi consequence: retain the existing evidence bindings as the only
  subject-reduction evidence at this checkpoint; make no source or rule
  change.
Warning/audit/catalog/health effects, if any: no Lambdapi source or generated
  authority changed, so no warning baseline, rule audit, catalog, or health
  artifact changed.
Decision: accept D-027, complete TSK-2A, and make TSK-2B dependency-ready.
Plan rows changed: D-026 and D-027 accepted; C-17 records runtime compilation;
  TSK-2 is split; TSK-2A complete; TSK-2B selected next; H-04 remains at the
  TSK-2C exit.
Remaining prerequisite or human review: none for TSK-2B. H-04 is not yet
  triggered.
```

### TSK-2A validation

Validated on the exact TSK-2A worktree diff:

```text
node --require ts-node/register --test tests/v3_2_runtime_tests.ts
  passed 8 tests / 1 suite with no skips

EMDASH_RUN_LAMBDAPI_PROBES=1 node --require ts-node/register --test
  tests/v3_2_core_binder_tests.ts tests/v3_2_core_checker_tests.ts
  tests/v3_2_core_context_tests.ts tests/v3_2_core_session_tests.ts
  tests/v3_2_core_signature_tests.ts tests/v3_2_dependent_context_tests.ts
  tests/v3_2_elab0_tests.ts tests/v3_2_elab1c_tests.ts
  tests/v3_2_manifest_tests.ts tests/v3_2_runtime_tests.ts
  tests/v3_2_telescope_structural_tests.ts
  passed 137 tests / 12 suites with no skips

./scripts/pnpmw run check:ts
  workspace contract, TypeScript, ESLint, and root tests passed
  289 tests / 55 suites: 274 passed, 15 opt-in probes skipped

EMDASH_TYPECHECK_TIMEOUT=60s make -C emdash2 check
  active kernel, extensions, and diagnostics passed

EMDASH_TYPECHECK_TIMEOUT=60s ./scripts/pnpmw run check:all
  root TypeScript gate passed with the same 289-test result
  41 active Lambdapi kernel/example files passed
  39 formal infrastructure tests and 5 print registry tests passed
  active-reference/report-header/book/evidence/typography/KaTeX checks passed
  strict rule-LHS audit and generated catalog freshness passed

git diff --check
  passed
```

## Completed Slice: TSK-2B

TSK-2B executes the compiled H-03 runtime fragment without broadening its
authority or yet making runtime reduction part of checker conversion:

- `coreRuntimeMatchRule` binds numeric variable slots in deterministic pattern
  order. Repeated occurrences use alpha-invariant `kernelExpressionEquals`, so
  provenance and binder hints are nonsemantic while owners, plicity, binder
  modes, free names, De Bruijn indices, and meta-session identity remain
  significant;
- rigid pattern nodes require the exact semantic owner, arity, and catalog
  plicity. TSK-2B also strengthens candidate compilation so every declared
  variable must be bound on the left before matching can succeed;
- `coreRuntimeRewriteHead` obtains candidates only from the immutable
  `CORE_MVP_RUNTIME_PROGRAM` root bucket and manifest order. The public
  single-rule matcher remains a non-authorizing structural diagnostic; there
  is no API that executes an arbitrary candidate program;
- right-pattern reconstruction goes back through `kernelApplication`, which
  restores catalog plicity. Captured variable subtrees are reused exactly,
  while introduced owner nodes carry derived provenance at the original
  redex span;
- `coreRuntimeWeakHead` repeatedly applies only reviewed root rewrites under a
  caller-supplied nonnegative safe-integer step bound. It returns a frozen,
  ordered trace and distinguishes `weak-head-normal` from
  `step-limit-exceeded`; zero fuel therefore still reports whether a reviewed
  next step exists;
- weak-head evaluation is deliberately head-only in this slice. It does not
  recursively normalize arguments, add generic-call beta, unfold
  declarations, or execute proof-time/conformance evidence.

All three reviewed full-to-capped heads reduce to the independently elaborated
capped Core form and retain the same exact elaborated result classifier.
Repeated-variable disagreement, malformed plicity, wrong roots, capped forms,
nested redexes, and invalid/zero step bounds have focused negative coverage.
A single bounded generated probe confirms all three TypeScript reducts against
the active Lambdapi conversions.

The structural `CoreChecker` is intentionally unchanged. Direct inference of
some full evaluator redexes still reaches classifier equations such as the
active object-of-hom-category computation; forcing that equation into the
structural checker during TSK-2B would silently begin the TSK-2C conversion
design. Subject-reduction evidence therefore remains the exact elaborated
classifier plus Lambdapi oracle result, not an authorized H-04 claim.

`CORE_MVP_MANIFEST` and its content hash remain unchanged. No proof-time rule,
intentional non-conversion evidence, excluded owner, Lambdapi source, backend
spelling, recursive normalizer, definitional comparison, or checker
conversion became executable.

### Experiment TSK-2B-DETERMINISTIC-HEAD-REWRITING

```text
Experiment ID: TSK-2B-DETERMINISTIC-HEAD-REWRITING
Date and checkpoint: 2026-07-24 at TSK-2A checkpoint a9771be
Question/hypothesis: the exact compiled three-rule program can match and
  reduce all reviewed heads deterministically under an explicit bound without
  granting executable authority to proof-time/conformance evidence or
  prematurely integrating definitional comparison.
Authority and owner position inspected: CORE_MVP_RUNTIME_PROGRAM, the exact
  H-03 manifest patterns, Core structural equality and application
  constructors, all three projection-pair schemas, the existing ELAB-1B
  full/capped surface consumers, and their active Lambdapi conversions. No
  Lambdapi source changed.
Current worktree/branch and baseline relationship:
  /home/user1/emdash1-elaborator-goal on
  goal/typescript-elaborator-v3.2 at a9771be before the experiment;
  descendant of baseline a06433e.
Minimal positive consumer: elaborate each full projection functor, apply it
  through functor-object, bind its compiled numeric slots, rewrite to the
  corresponding capped owner, preserve the exact result classifier, and
  reach weak-head normal form in one recorded step.
Relevant negative/non-collapse consumer: reject inconsistent repeated
  functor data and malformed plicity; leave wrong roots, already-capped
  forms, and nested redexes unchanged; distinguish zero-fuel exhaustion from
  zero-step normality; reject negative, fractional, and unsafe bounds; expose
  no proof-time or conformance rule to the executable program.
Observed result: each reviewed head selects its manifest-order rule, rebuilds
  the exact capped Core form, preserves captured subtrees and redex-span
  provenance, and stops after one step. All three generated conversions pass
  the bounded Lambdapi oracle together.
Unexpected result or failure: direct structural-checker inference of a full
  evaluator redex reaches the object-of-hom-category classifier computation
  that the structural checker intentionally does not yet know. Treating that
  as a TSK-2B failure would conflate rewriting with TSK-2C conversion.
TypeScript consequence: accept D-028; keep the evaluator head-only and
  product-program-only, record exact elaborated classifier equality now, and
  make checker conversion/definitional comparison the next slice.
Lambdapi consequence: retain the existing three runtime conversions as the
  current differential and subject-reduction oracle; make no declaration or
  rule change.
Warning/audit/catalog/health effects, if any: no Lambdapi source or generated
  authority changed, so no warning baseline, rule audit, catalog, or health
  artifact changed.
Decision: accept D-028, complete TSK-2B, and make TSK-2C dependency-ready.
Plan rows changed: D-028 accepted; C-17 records matching/head evaluation;
  TSK-2B complete; TSK-2C selected next with H-04 still at its exit.
Remaining prerequisite or human review: none for TSK-2C implementation.
  H-04 is not triggered until the TSK-2C recommendation is complete.
```

### TSK-2B validation

Validated on the exact TSK-2B worktree diff:

```text
node --require ts-node/register --test
  tests/v3_2_runtime_tests.ts tests/v3_2_runtime_rewrite_tests.ts
  passed 16 tests and skipped the 1 opt-in differential probe

EMDASH_RUN_LAMBDAPI_PROBES=1 node --require ts-node/register --test
  tests/v3_2_*_tests.ts
  passed 146 tests / 13 suites with no skips

./scripts/pnpmw run check:ts
  workspace contract, TypeScript, ESLint, and root tests passed
  298 tests / 56 suites: 282 passed, 16 opt-in probes skipped

EMDASH_TYPECHECK_TIMEOUT=60s make -C emdash2 check
  active kernel, extensions, and diagnostics passed

EMDASH_TYPECHECK_TIMEOUT=60s ./scripts/pnpmw run check:all
  root TypeScript gate passed with the same 298-test result
  41 active Lambdapi kernel/example files passed
  39 formal infrastructure tests and 5 print registry tests passed
  active-reference/report-header/book/evidence/typography/KaTeX checks passed
  strict rule-LHS audit and generated catalog freshness passed

git diff --check
  passed
```

## Completed Pre-Review Slice: TSK-2C1

TSK-2C1 adds candidate definitional comparison and prepares, but does not
approve, the H-04 trusted-rule boundary:

- `coreRuntimeDefinitionalCompare` first uses alpha-invariant structural Core
  equality, then the exact reviewed runtime head evaluator, then congruence
  over owner applications, generic calls, Pi/lambda binder types, and bodies;
- one caller-supplied nonnegative safe-integer budget is shared in a fixed
  left-before-right, outer-before-inner order across the entire comparison.
  Results are `equal`, `not-equal` with the first rigid mismatch path, or
  `step-limit-exceeded` with the side, path, current expression, and next
  reviewed rule;
- the `CoreChecker` constraint boundary uses the same comparison with an
  exported fixed 256-step limit. It accepts only an `equal` result, reports a
  deterministic `CONVERSION_STEP_LIMIT`, and otherwise retains the existing
  meta solving and rigid plicity/mode/type diagnostics;
- comparison uses only `CORE_MVP_RUNTIME_PROGRAM`. The constant-section
  proof-time comparison, its intentional runtime non-conversion, excluded
  owner rules, declaration unfolding, and generic-call beta all remain
  non-executable and have focused comparison/checker negatives;
- `coreRuntimeFullProjectionCount` supplies the termination measure. Every
  rule removes one explicit full owner, and right-side variable multiplicity
  never exceeds left-side multiplicity. The global count therefore strictly
  decreases by at least one; a non-left-linear match may discard additional
  copies of a captured full projection;
- `CORE_RUNTIME_H04_RECOMMENDATION` is a deep-frozen, drift-checked
  `proposed-awaiting-h04` artifact tied to the exact H-03 manifest revision,
  content hash, and three runtime rule IDs. It keeps `claimsAuthorized: false`.

The comparison is intentionally the closure of structural equality under the
reviewed runtime fragment, not a claim of complete dependent-type conversion.
In particular, generic beta is not silently inferred from the already
implemented substitution primitive, and proof-time unification evidence is
not reclassified as runtime equality.

The executable H-04 evidence supports this exact recommendation:

1. authorize termination for the exact three H-03 runtime rules on finite
   Core syntax via the strict full-projection-count measure;
2. authorize the deterministic, explicitly bounded evaluator/comparator and
   exactly those three trusted runtime rules;
3. withhold a general confluence claim. Pairwise rigid root discrimination is
   useful evidence, but the patterns are non-left-linear and nested critical
   pairs have not been closed;
4. withhold a standalone TypeScript subject-reduction theorem. All three
   reducts have exact independently elaborated result classifiers and pass
   bounded Lambdapi differential conversions, but direct checking of a full
   redex can require active classifier computation not selected by H-03.
   Lambdapi therefore remains the subject-reduction oracle.

Approval of D-030 must produce a distinct reviewed claim artifact in
TSK-2C2. It must not rewrite `CORE_MVP_MANIFEST`, retroactively change the
TSK-2A candidate program, or turn either withheld claim into an authorization.

### Experiment TSK-2C1-CONVERSION-AND-H04-BOUNDARY

```text
Experiment ID: TSK-2C1-CONVERSION-AND-H04-BOUNDARY
Date and checkpoint: 2026-07-24 at TSK-2B checkpoint aa79285
Question/hypothesis: structural equality can be closed under exactly the
  reviewed runtime program and integrated into checker constraints with one
  deterministic bound, while executable authority and the H-04
  metatheoretic claims remain separately reviewable.
Authority and owner position inspected: the exact H-03 manifest/program; Core
  equality, application/call/binder forms, and checker constraint
  decomposition; all three active Lambdapi projection betas and their
  evidence bindings; the constant-section proof-time/non-conversion pair;
  the broader active capped-owner rule neighborhood. No Lambdapi source
  changed.
Current worktree/branch and baseline relationship:
  /home/user1/emdash1-elaborator-goal on
  goal/typescript-elaborator-v3.2 at aa79285 before the experiment;
  descendant of baseline a06433e.
Minimal positive consumer: compare each full evaluator redex with its capped
  reduct in both directions, compare two nested redexes under one shared
  budget, and make CoreChecker discharge an otherwise structurally unequal
  type constraint containing a reviewed conversion.
Relevant negative/non-collapse consumer: report a stable free-name mismatch
  and invalid/exhausted budget; reject the constant-section runtime
  non-conversion through both comparison and checker; do not reduce a generic
  lambda call; keep proof-time and excluded rules out of the runtime program.
Observed result: all three conversions compare in one step, nested congruence
  consumes globally ordered fuel, the checker accepts the reviewed
  conversion, and every authority negative remains zero-step non-equality.
  Standard substitutions lower the global full-owner count by one.
Unexpected result or failure: the first measure wording said every rewrite
  lowers the global count exactly once. A repeated left variable may itself
  capture a full projection and occur fewer times on the right, so the real
  theorem is strict decrease by at least one. A focused repeated-subterm
  consumer lowers the count from four to one. Also, direct checker inference
  of the full evaluator consumer needs active object/classifier computation
  outside the frozen three-rule program, so TypeScript subject reduction is
  not yet an internal theorem.
TypeScript consequence: accept D-029, split TSK-2C at H-04, integrate only
  equality results into the checker, and publish D-030 as an immutable
  pre-review recommendation with confluence and TypeScript subject reduction
  explicitly withheld.
Lambdapi consequence: retain the existing active conversions as the
  subject-reduction oracle and do not promote any additional active rule into
  the H-03 product fragment.
Warning/audit/catalog/health effects, if any: no Lambdapi source or generated
  authority changed, so no warning baseline, rule audit, catalog, or health
  artifact changed.
Decision: accept D-029; propose D-030 for H-04; complete TSK-2C1 and block
  only TSK-2C2 on that review.
Plan rows changed: D-029 accepted; D-030 proposed/H-04 pending; C-17
  candidate-complete through comparison; TSK-2C split; TSK-2C1 complete;
  TSK-2C2 blocked by H-04.
Remaining prerequisite or human review: H-04 must approve, reject, or refine
  D-030 before a reviewed claims artifact can complete TSK-2C2.
```

### TSK-2C1 validation

Validated on the exact TSK-2C1 worktree diff:

```text
node --require ts-node/register --test tests/v3_2_conversion_tests.ts
  passed 10 tests / 1 suite with no skips

EMDASH_RUN_LAMBDAPI_PROBES=1 node --require ts-node/register --test
  tests/v3_2_*_tests.ts
  passed 156 tests / 14 suites with no skips

./scripts/pnpmw run check:ts
  workspace contract, TypeScript, ESLint, and root tests passed
  308 tests / 57 suites: 292 passed, 16 opt-in probes skipped

EMDASH_TYPECHECK_TIMEOUT=60s make -C emdash2 check
  active kernel, extensions, and diagnostics passed

EMDASH_TYPECHECK_TIMEOUT=60s ./scripts/pnpmw run check:all
  root TypeScript gate passed with the same 308-test result
  41 active Lambdapi kernel/example files passed
  39 formal infrastructure tests and 5 print registry tests passed
  active-reference/report-header/book/evidence/typography/KaTeX checks passed
  strict rule-LHS audit and generated catalog freshness passed

git diff --check
  passed
```

## Completed Review Slice: TSK-2C2

The user approved H-04/D-030 exactly as proposed on 2026-07-24. TSK-2C2
records that decision without rewriting any pre-review or H-03 artifact:

- `CORE_RUNTIME_H04_REVIEW` is a distinct deep-frozen
  `reviewed-approved` artifact with the exact H-04 gate, D-030 decision,
  approval wording, and review date;
- it snapshots the immutable `CORE_RUNTIME_H04_RECOMMENDATION` rather than
  mutating it. The snapshot and original both retain
  `claimsAuthorized: false` as historical pre-review evidence;
- it authorizes termination only for the exact three-rule fragment,
  deterministic bounded evaluation/comparison, and the exact H-03 runtime
  rule IDs;
- it preserves general confluence and standalone TypeScript subject reduction
  as withheld, and records Lambdapi as the subject-reduction oracle;
- proof-time comparison, the intentional runtime non-conversion, excluded
  owner rules, declaration unfolding, generic-call beta, and every additional
  runtime rule remain outside the authorization;
- validation rejects approval, recommendation, rule-set, excluded-mechanism,
  oracle, or claim-boundary drift. The H-03 manifest content hash and the
  candidate runtime program remain byte-for-byte unchanged.

This completes TSK-2. It does not graduate the TypeScript kernel, broaden the
MVP fragment, or trigger H-05; TSK-3 differential parity is now the next
dependency-ready slice.

### TSK-2C2 validation

Validated on the exact TSK-2C2 worktree diff:

```text
node --require ts-node/register --test
  tests/v3_2_metatheory_review_tests.ts
  passed 6 tests / 1 suite with no skips

EMDASH_RUN_LAMBDAPI_PROBES=1 node --require ts-node/register --test
  tests/v3_2_*_tests.ts
  passed 162 tests / 15 suites with no skips

./scripts/pnpmw run check:ts
  workspace contract, TypeScript, ESLint, and root tests passed
  314 tests / 58 suites: 298 passed, 16 opt-in probes skipped

EMDASH_TYPECHECK_TIMEOUT=60s make -C emdash2 check
  active kernel, extensions, and diagnostics passed

EMDASH_TYPECHECK_TIMEOUT=60s ./scripts/pnpmw run check:all
  root TypeScript gate passed with the same 314-test result
  41 active Lambdapi kernel/example files passed
  39 formal infrastructure tests and 5 print registry tests passed
  active-reference/report-header/book/evidence/typography/KaTeX checks passed
  strict rule-LHS audit and generated catalog freshness passed

git diff --check
  passed
```

## Completed Slice: TSK-3A

TSK-3A turns the broad parity row into an exact, reviewable exit matrix and
closes its owner-level tranche:

- `CORE_MVP_DIFFERENTIAL_SCOPE` derives the common fragment from the
  content-hashed H-03 manifest: exactly 16 owners and three runtime rules. It
  separately names the recursive functor-hom 2-cell and native transfor-level
  higher-cell packages and rejects any owner, rule, requirement, order, or
  manifest-identity drift;
- `buildCoreMvpOwnerDifferentialCorpus` constructs one deterministic Core
  declaration environment and one saturated term/result type per reviewed
  owner. The TypeScript checker and Lambdapi therefore consume the same terms
  rather than parallel hand-written examples;
- every owner has one exact positive judgment and one deliberately wrong but
  well-scoped result-type judgment. TypeScript accepts all 16 positives and
  rejects all 16 negatives with `TYPE_MISMATCH`;
- the probe vocabulary now serializes negative typing judgments as
  `assertnot ⊢ term : type`. One bounded Lambdapi invocation accepts the same
  16 positive assertions and 16 negative assertions;
- the existing all-24-owner signature probes remain valuable backend
  conformance evidence. They do not expand the frozen TypeScript product
  fragment or TSK-3 parity denominator.

### Experiment TSK-3A-SHARED-OWNER-CORPUS

```text
Experiment ID: TSK-3A-SHARED-OWNER-CORPUS
Date and checkpoint: 2026-07-24 at TSK-2 completion checkpoint 38ffc49
Question/hypothesis: the exact H-03 owner set can share one generated Core
  corpus between the TypeScript checker and Lambdapi, including batched
  negative typing judgments, without treating the eight conformance-only
  owners as product members.
Authority and owner position inspected: CORE_MVP_MANIFEST and its content
  hash; all selected declarative owner signatures and plicities; active
  Lambdapi owner bindings; KernelProbe assertion serialization. No Lambdapi
  declaration or rule changed.
Current worktree/branch and baseline relationship:
  /home/user1/emdash1-elaborator-goal on
  goal/typescript-elaborator-v3.2 at 38ffc49 before the experiment;
  descendant of baseline a06433e.
Minimal positive consumer: generate and infer one saturated application of
  each of the 16 reviewed owners, then submit those exact terms/result types
  as one Lambdapi probe.
Relevant negative/non-collapse consumer: check each identical term against
  one declared but deliberately wrong result type. TypeScript must report a
  rigid TYPE_MISMATCH and Lambdapi must accept the corresponding
  `assertnot ⊢ term : type`.
Observed result: both engines agree on all 16 positives and 16 negatives in
  manifest order; the combined Lambdapi probe completes in about two seconds.
Unexpected result or failure: none. The pre-existing all-owner TypeScript and
  Lambdapi tests used separate corpora and included all 24 catalog owners, so
  they were conformance coverage rather than a pinned product-parity matrix.
TypeScript consequence: accept D-031; add the immutable exit matrix, shared
  owner-corpus builder, and negative-typing probe form; split TSK-3 into
  owner, rule, and higher-cell tranches.
Lambdapi consequence: retain the active kernel as the oracle; make no source,
  rule, warning, audit, catalog, or health change.
Decision: accept.
Plan rows changed: D-031 accepted; C-20 partial with owner matrix complete;
  TSK-3 split; TSK-3A complete; TSK-3B dependency-ready.
Remaining prerequisite or human review: none for TSK-3B.
```

### TSK-3A validation

Validated on the exact TSK-3A worktree diff:

```text
EMDASH_RUN_LAMBDAPI_PROBES=1 node --require ts-node/register --test
  tests/v3_2_differential_owner_tests.ts
  passed 6 tests / 1 suite with no skips

EMDASH_RUN_LAMBDAPI_PROBES=1 node --require ts-node/register --test
  tests/v3_2_*_tests.ts
  passed 168 tests / 16 suites with no skips

./scripts/pnpmw run check:ts
  workspace contract, TypeScript, ESLint, and root tests passed
  320 tests / 59 suites: 303 passed, 17 opt-in probes skipped

EMDASH_TYPECHECK_TIMEOUT=60s make -C emdash2 check
  active kernel, extensions, and diagnostics passed

EMDASH_TYPECHECK_TIMEOUT=60s ./scripts/pnpmw run check:all
  root TypeScript gate passed with the same 320-test result
  41 active Lambdapi kernel/example files passed
  39 formal infrastructure tests and 5 print registry tests passed
  active-reference/report-header/book/evidence/typography/KaTeX checks passed
  strict rule-LHS audit and generated catalog freshness passed

git diff --check
  passed
```

## Completed Slice: TSK-3B

TSK-3B closes every rule row in the frozen differential matrix without
broadening the H-04 trust boundary:

- `buildCoreMvpRuleDifferentialCorpus` derives exactly three rows, in reviewed
  manifest/runtime-program order. Each positive row gives the TypeScript
  comparator and Lambdapi the same Core redex/reduct pair;
- every positive pair rewrites by its exact reviewed rule in one TypeScript
  step. One batched Lambdapi probe accepts the same three conversions;
- each negative row substitutes a fresh rigid functor of the exact full
  projection classifier into the surface-elaborated redex. The TypeScript
  declaration environment validates that classifier, the recorded
  same-classifier substitution preserves the elaborated result classifier,
  the term is runtime-irreducible, and comparison with the reduct is a
  zero-step non-conversion. Lambdapi accepts the same three `assertnot`
  judgments;
- the paired malformed candidate replaces the required full projection in
  the corresponding manifest left pattern with a fresh variable. That is the
  broader rule which would cover the negative witness: the runtime compiler
  rejects two candidates for losing the mandatory projection decrease and
  rejects the transfor-hom row even earlier because removing its full owner
  leaves `eta` unbound;
- direct standalone checker inference of the evaluator applications still
  requires the active object-classifier equations recorded at H-04. TSK-3B
  therefore retains Lambdapi as subject-reduction oracle and records
  surface-elaboration plus same-classifier substitution evidence rather than
  silently adding a new trusted conversion.

### Experiment TSK-3B-SHARED-RULE-BOUNDARY

```text
Experiment ID: TSK-3B-SHARED-RULE-BOUNDARY
Date and checkpoint: 2026-07-24 at TSK-3A checkpoint cf3e8c4
Question/hypothesis: every reviewed runtime row can share one positive
  conversion and one well-typed negative conversion pair between TypeScript
  and Lambdapi, while a malformed broadened rule is rejected without adding
  classifier computation or expanding H-04.
Authority and owner position inspected: CORE_MVP_DIFFERENTIAL_SCOPE,
  CORE_MVP_MANIFEST, CORE_MVP_RUNTIME_PROGRAM, surface elaboration and Core
  classifier materialization, runtime comparison, KernelProbe conversion
  serialization, and the active Lambdapi projection rules. No Lambdapi source
  or rule changed.
Current worktree/branch and baseline relationship:
  /home/user1/emdash1-elaborator-goal on
  goal/typescript-elaborator-v3.2 at cf3e8c4 before the experiment;
  descendant of baseline a06433e.
Minimal positive consumer: elaborate the exact three full-projection
  evaluator redexes and capped reducts, compare each pair in one TypeScript
  step, and submit those same pairs as Lambdapi conversions.
Relevant negative/non-collapse consumer: replace only the full-projection
  functor with a fresh rigid declaration of the identical classifier. Require
  TypeScript to leave it irreducible and report zero-step non-conversion with
  the capped reduct; require Lambdapi to accept the same `assertnot`.
Malformed-candidate consumer: erase the required full projection from each
  corresponding manifest left pattern. Require candidate compilation to fail
  and pair that failure with the exact negative oracle witness which the
  broadened rule would otherwise cover.
Observed result: TypeScript and Lambdapi agree on all three conversions and
  all three non-conversions. TypeScript rejects all three broadened candidate
  rules. The combined Lambdapi probe completes in about two seconds.
Unexpected result or failure: direct CoreChecker inference of both the
  positive and substituted evaluator heads reaches the already-recorded
  hom/transfor-classifier versus object-classifier boundary. The capped
  reducts infer normally. This is the exact standalone subject-reduction gap
  withheld by H-04, not evidence for adding a fourth runtime rule.
TypeScript consequence: accept D-032; publish the shared rule corpus and its
  explicit same-classifier substitution evidence, retain the checker
  boundary, and complete TSK-3B.
Lambdapi consequence: retain the active kernel as subject-reduction and
  non-conversion oracle; make no declaration, rule, warning, audit, catalog,
  or health change.
Decision: accept.
Plan rows changed: D-032 accepted; C-20 partial with owner and rule matrices
  complete; TSK-3B complete; TSK-3C dependency-ready.
Remaining prerequisite or human review: none for TSK-3C.
```

### TSK-3B validation

Validated on the exact TSK-3B worktree diff:

```text
EMDASH_RUN_LAMBDAPI_PROBES=1 node --require ts-node/register --test
  tests/v3_2_differential_rule_tests.ts
  passed 6 tests / 1 suite with no skips

EMDASH_RUN_LAMBDAPI_PROBES=1 node --require ts-node/register --test
  tests/v3_2_*_tests.ts
  passed 174 tests / 17 suites with no skips

./scripts/pnpmw run check:ts
  workspace contract, TypeScript, ESLint, and root tests passed
  326 tests / 60 suites: 308 passed, 18 opt-in probes skipped

EMDASH_TYPECHECK_TIMEOUT=60s make -C emdash2 check
  active kernel, extensions, and diagnostics passed

EMDASH_TYPECHECK_TIMEOUT=60s ./scripts/pnpmw run check:all
  root TypeScript gate passed with the same 326-test result
  41 active Lambdapi kernel/example files passed
  39 formal infrastructure tests and 5 print registry tests passed
  active-reference/report-header/book/evidence/typography/KaTeX checks passed
  strict rule-LHS audit and generated catalog freshness passed

git diff --check
  passed
```

## Completed Slice: TSK-3C

TSK-3C closes the last rows of the exact H-03 differential matrix:

- `buildCoreMvpHigherCellDifferentialCorpus` publishes the two required
  packages in frozen scope order. Their actual Core terms and types contain
  every owner named by the corresponding matrix row;
- the recursive package builds the second hom action by applying
  `functor-hom-full` to an already full hom-action functor, then evaluates it
  on a 2-cell. TypeScript and Lambdapi both use
  `projection.functor-hom.evaluate` at this next hom level; no `fapp2` or
  dimension-specific Core node exists;
- the native transfor package covers both the full/capped component level and
  the full/capped hom level. Its two evaluator pairs use exactly the other
  reviewed runtime rules;
- nine surface-elaborated positive typings, three source-located
  wrong-endpoint negatives, and three one-step conversions are shared with
  one bounded Lambdapi probe. The negative Core terms differ from their valid
  full projections at exactly the rejected endpoint slot;
- `CORE_MVP_DIFFERENTIAL_COMPLETION` is a deep-frozen, drift-checked record of
  every owner, rule, and higher-cell requirement and its TSK-3 evidence. Its
  oracle policy remains `required-until-graduation`;
- completion is deliberately scoped to the 16-owner H-03 product fragment.
  The internal-Hom C-09/C-10 consumers remain green conformance evidence, but
  their excluded owners are not promoted and this slice does not declare the
  broader surface grammar representative.

### Experiment TSK-3C-HIGHER-CELL-CLOSURE

```text
Experiment ID: TSK-3C-HIGHER-CELL-CLOSURE
Date and checkpoint: 2026-07-24 at TSK-3B checkpoint 69a16dd
Question/hypothesis: the frozen fragment's higher-cell rows can close by
  recursively reusing the reviewed ordinary projection schemas, with shared
  TypeScript/Lambdapi positive, endpoint-negative, and conversion judgments,
  without adding a dimension-specific owner or broadening H-04.
Authority and owner position inspected: CORE_MVP_DIFFERENTIAL_SCOPE,
  CORE_MVP_MANIFEST and runtime program; the active recursive
  `fapp1_func` consumer; native `tapp0_func`/`tapp1_func` consumers; surface
  object-category recovery; and the three active Lambdapi projection rules.
  No Lambdapi declaration or rule changed.
Current worktree/branch and baseline relationship:
  /home/user1/emdash1-elaborator-goal on
  goal/typescript-elaborator-v3.2 at 69a16dd before the experiment;
  descendant of baseline a06433e.
Minimal positive consumer: type the recursive full hom-action functor, its
  evaluation on alpha, the corresponding capped action, and all full/redex/
  capped component and hom terms for an ordinary transfor.
Relevant negative/non-collapse consumer: substitute a C-hom as the recursive
  inner target, a C-object as the component index, and a C-object as the
  transfor-hom target. TypeScript must reject each surface operand at its
  source span; Lambdapi must accept `assertnot` for the corresponding corrupt
  Core typing judgment.
Probe command and bounded result: one probe with nine positive typings, three
  negative typings, and three conversions completes in about two seconds.
Observed result: both engines accept every positive and conversion and reject
  every wrong endpoint. The recursive conversion is an ordinary rule-0 step
  at a nested hom category, and the corpus contains no `fapp2`.
Unexpected result or failure: none. The standalone classifier-computation
  limitation recorded by H-04 remains outside this surface-elaboration
  evidence and was not converted into a new runtime rule.
TypeScript consequence: accept D-033; add the shared higher-cell corpus and
  the frozen completion record; complete C-20 and TSK-3.
Lambdapi consequence: retain the active kernel as oracle until H-05; make no
  declaration, rule, warning, audit, catalog, or health change.
Decision: accept.
Plan rows changed: D-033 accepted; C-20 complete; TSK-3/3C complete;
  MIGRATE-1 dependency-ready.
Remaining prerequisite or human review: none for MIGRATE-1. H-05 remains at
  GRADUATE-1 after migration.
```

### TSK-3C validation

Validated on the exact TSK-3C worktree diff:

```text
EMDASH_RUN_LAMBDAPI_PROBES=1 node --require ts-node/register --test
  tests/v3_2_differential_higher_cell_tests.ts
  passed 7 tests / 1 suite with no skips

EMDASH_RUN_LAMBDAPI_PROBES=1 node --require ts-node/register --test
  tests/v3_2_*_tests.ts
  passed 181 tests / 18 suites with no skips

./scripts/pnpmw run check:ts
  workspace contract, TypeScript, ESLint, and root tests passed
  333 tests / 61 suites: 314 passed, 19 opt-in probes skipped

EMDASH_TYPECHECK_TIMEOUT=60s make -C emdash2 check
  active kernel, extensions, and diagnostics passed

EMDASH_TYPECHECK_TIMEOUT=60s ./scripts/pnpmw run check:all
  root TypeScript gate passed with the same 333-test result
  41 active Lambdapi kernel/example files passed
  39 formal infrastructure tests and 5 print registry tests passed
  active-reference/report-header/book/evidence/typography/KaTeX checks passed
  strict rule-LHS audit and generated catalog freshness passed

git diff --check
  passed
```

## Completed Slice: MIGRATE-1A

MIGRATE-1A establishes the deletion ledger and replaces the first retained
generic proof facility:

- `LEGACY_MIGRATION_INVENTORY` is a deeply frozen, drift-checked record of all
  ten generic-mechanism decisions, every one of the thirteen legacy root
  source files, and all twenty-two legacy test files loaded by the runner;
- tests derive the actual root source set and legacy runner imports from the
  worktree, require exact closed-world equality with the inventory, and
  require every claimed replacement test to exist;
- `inspectCoreProofState` zonks through solved session metas and walks
  applications, generic calls, Pi/lambda binder types and bodies, and
  contextual meta spines uniformly. It reports only reachable unsolved goals,
  expands goal-type dependencies once, counts repeated occurrences, and
  retains creation depth plus declaration/occurrence provenance;
- the inspector has no legacy `Term`, category-node switch, global definition
  traversal, mutable hole reference, reset contract, or Lambdapi emitter
  dependency. Its diagnostic formatter intentionally supports raw metas
  without making them backend syntax;
- proof refinement is not silently included. Checked `exact`, `intro`, and
  `apply` remain MIGRATE-1C, after the separately bounded MIGRATE-1B
  higher-order pattern solver.

### Experiment MIGRATE-1A-INVENTORY-PROOF-STATE

```text
Experiment ID: MIGRATE-1A-INVENTORY-PROOF-STATE
Date and checkpoint: 2026-07-24 at TSK-3C checkpoint 1f58808
Question/hypothesis: every legacy source/test can receive an explicit
  non-compatibility disposition, and useful goal inspection can be
  reimplemented over generic Core/session structure without retaining any
  old category tag or global mutable proof state.
Authority and owner position inspected: the reusable-machinery table and
  C-19/MIGRATE rows in this plan; all root src/*.ts modules; every non-v3.2
  test imported by tests/main_tests.ts; legacy proof traversal/tactics; the
  locally nameless Core and session meta APIs. No Lambdapi owner changed.
Current worktree/branch and baseline relationship:
  /home/user1/emdash1-elaborator-goal on
  goal/typescript-elaborator-v3.2 at 1f58808 before the experiment;
  descendant of baseline a06433e.
Minimal positive consumer: discover metas through a Pi binder type, generic
  call callee/arguments, and semantic-owner arguments; follow a solved wrapper
  to its remaining goal; report a local contextual goal and a meta dependency
  in its type.
Relevant negative/non-collapse consumer: omit an unrelated session meta from
  the proof state and reject a foreign-session meta at its original source.
  Do not execute generic beta/eta, proof-time comparisons, or a tactic.
Probe command and bounded result: the two focused MIGRATE-1A suites pass
  10 tests / 2 suites with no skips.
Observed result: the source/test sets exactly match the inventory; replacement
  paths exist; inventory drift is rejected; reachable goal order, repeated
  occurrence counts, dependency expansion, local depth, source reporting,
  completion, and session isolation all pass.
Unexpected result or failure: none. The legacy displayed-owner traversal case
  was evidence for generic child traversal, not authority to port its node
  tags.
TypeScript consequence: accept D-034; complete MIGRATE-1A; make the stabilized
  Core-binder higher-order pattern fragment MIGRATE-1B next.
Lambdapi consequence: none. Keep the existing oracle policy; add no owner,
  rule, comparison, probe, or backend dependency.
Decision: accept.
Plan rows changed: D-034 accepted; C-19 partial; MIGRATE-1 split;
  MIGRATE-1A complete; MIGRATE-1B dependency-ready.
Remaining prerequisite or human review: none for MIGRATE-1B. H-05 and H-06
  remain at their recorded later triggers.
```

### MIGRATE-1A validation

Validated on the exact MIGRATE-1A worktree diff:

```text
node --require ts-node/register --test
  tests/v3_2_migration_inventory_tests.ts
  tests/v3_2_proof_state_tests.ts
  passed 10 tests / 2 suites with no skips

node --require ts-node/register --test tests/v3_2_*_tests.ts
  passed 191 tests / 20 suites: 172 passed, 19 opt-in probes skipped

./scripts/pnpmw run check:ts
  workspace contract, TypeScript, ESLint, and root tests passed
  343 tests / 63 suites: 324 passed, 19 opt-in probes skipped

EMDASH_TYPECHECK_TIMEOUT=60s make -C emdash2 check
  active kernel, extensions, and diagnostics passed

EMDASH_TYPECHECK_TIMEOUT=60s ./scripts/pnpmw run check:all
  root TypeScript gate passed with the same 343-test result
  41 active Lambdapi kernel/example files passed
  39 formal infrastructure tests and 5 print registry tests passed
  active-reference/report-header/book/evidence/typography/KaTeX checks passed
  strict rule-LHS audit and generated catalog freshness passed

git diff --check
  passed
```

## Completed Slice: MIGRATE-1B

MIGRATE-1B replaces the independently useful fragment of the legacy
higher-order unifier without retaining its names, HOAS terms, mutable holes,
or global constraint store:

- `invertCoreMetaPattern` accepts a contextual meta occurrence only when its
  spine has the creation arity and consists of distinct variables in the
  occurrence scope. It computes the inverse substitution with
  `kernelRemapAmbientIndices`, including beneath Pi/lambda binders, and checks
  that re-instantiating the solution reproduces the rigid term structurally;
- the session uses the pure inverse only for constraints in a persistent
  descendant of the meta's creation context. The existing canonical path
  remains the fast path, and every pattern assignment still passes through
  the canonical `solve` method for scope validation, zonking, single
  assignment, and occurs checking;
- weakening, exchange, constants, partial use of a two-variable spine, nested
  binders, and both flex-rigid orientations are green. A non-variable or
  repeated spine and an unrelated context lineage stay explicitly stuck;
  omitted-local dependence and occurs cycles are rejected at source
  provenance; flex-flex remains ambiguous;
- the public direct-solve API remains canonical-only. The new mechanism is
  elaboration state, not runtime reduction or ambient rewrite matching, and
  it changes neither the H-04 program nor any Lambdapi declaration or rule;
- `LEGACY_MIGRATION_INVENTORY` revision `MIGRATE-1B` now marks the pattern
  mechanism covered, points both relevant legacy corpora at the new Core
  evidence, and makes MIGRATE-1C the next slice.

### Experiment MIGRATE-1B-CONTEXTUAL-PATTERN-INVERSION

```text
Experiment ID: MIGRATE-1B-CONTEXTUAL-PATTERN-INVERSION
Date and checkpoint: 2026-07-24 at MIGRATE-1A checkpoint 3f6867a
Question/hypothesis: the useful flex-rigid fragment can be expressed as pure
  inversion of explicit contextual De Bruijn spines and assigned through the
  stabilized session, without porting name abstraction, mutable holes,
  generic beta/eta, or ambient user-rule matching.
Authority and owner position inspected: D-016/D-018/D-034 and C-11/C-19 in
  this plan; the locally nameless Core remap/instantiation operations; the
  persistent context and session APIs; legacy src/pattern.ts,
  src/unification.ts, higher_order_unification_tests.ts, and
  higher_order_pattern_matching_tests.ts. No Lambdapi owner or rule changed.
Current worktree/branch and baseline relationship:
  /home/user1/emdash1-elaborator-goal on
  goal/typescript-elaborator-v3.2 at 3f6867a before the experiment;
  descendant of baseline a06433e.
Minimal positive consumer: solve a meta created under x at the weakened
  occurrence ?m[#1] under x,y against f(#1), store f(#0), and verify that
  zonking the occurrence reconstructs the rigid side. Also cover exchange,
  partial dependency, constants, a nested lambda, and right orientation.
Relevant negative/non-collapse consumer: keep non-variable and repeated
  spines, flex-flex equations, and unrelated context lineages stuck; reject
  an omitted local and a recursive solution; retain canonical-only direct
  solve. Do not run an evaluator rule or emit an unresolved meta to Lambdapi.
Probe command and bounded result: the focused inventory and pattern suites
  pass 18 tests / 2 suites with no skips.
Observed result: every positive substitution round-trips; internal binders
  remain capture-safe; stuck versus rejected outcomes and their source
  provenance are deterministic; the machine inventory advances to
  MIGRATE-1B with MIGRATE-1C next.
Unexpected result or failure: none. The old session test's weakened
  occurrence was a valid Miller pattern, so its expected outcome was
  deliberately changed from noncanonical-stuck to pattern-assigned while its
  independent rigid-conversion constraint remains stuck.
TypeScript consequence: accept D-035; complete C-11 for the bounded
  structural/Miller fragment and MIGRATE-1B; make checked proof refinement
  MIGRATE-1C next.
Lambdapi consequence: none. Raw metas remain outside backend syntax; keep the
  active kernel as conformance authority and add no declaration, rule,
  comparison, warning, audit, catalog, or health change.
Decision: accept.
Plan rows changed: D-035 accepted; C-11 complete for the bounded pattern
  fragment; C-19 partial through MIGRATE-1B; MIGRATE-1B complete;
  MIGRATE-1C dependency-ready.
Remaining prerequisite or human review: none for MIGRATE-1C. H-05 and H-06
  remain at their recorded later triggers.
```

### MIGRATE-1B validation

Validated on the exact MIGRATE-1B worktree diff:

```text
node --require ts-node/register --test
  tests/v3_2_migration_inventory_tests.ts
  tests/v3_2_pattern_unification_tests.ts
  passed 18 tests / 2 suites with no skips

node --require ts-node/register --test tests/v3_2_*_tests.ts
  passed 204 tests / 21 suites: 185 passed, 19 opt-in probes skipped

./scripts/pnpmw run check:ts
  workspace contract, TypeScript, ESLint, and root tests passed
  356 tests / 64 suites: 337 passed, 19 opt-in probes skipped

EMDASH_TYPECHECK_TIMEOUT=60s make -C emdash2 check
  active kernel, extensions, and diagnostics passed

EMDASH_TYPECHECK_TIMEOUT=60s ./scripts/pnpmw run check:all
  root TypeScript gate passed with the same 356-test result
  41 active Lambdapi kernel/example files passed
  39 formal infrastructure tests and 5 print registry tests passed
  active-reference/report-header/book/evidence/typography/KaTeX checks passed
  strict rule-LHS audit and generated catalog freshness passed

git diff --check
  passed
```

## Completed Slice: MIGRATE-1C

MIGRATE-1C replaces the checked-refinement invariant of the legacy proof mode
without retaining its mutable holes, global lookup, or category-specific
traversal:

- each inspected goal now retains its immutable persistent creation context,
  so refinement does not recover binders by replaying or opening the proof
  term with dummy names;
- `CoreProofRefiner` accepts only a goal identity currently reachable from its
  immutable root. Solving remains in the owning `CoreElaborationSession`, and
  inspecting the same root after zonking yields the next proof state;
- `exact` checks a complete term through the ordinary closed checker boundary.
  `intro` requires a syntactic Pi, preserves its plicity and variation mode,
  extends the persistent context, creates one body goal, checks the resulting
  lambda, and only then assigns the parent;
- `apply` requires an inferable meta-free callee and exhausts its syntactic Pi
  telescope into ordered argument metas with the original plicities. The
  dedicated `checkRefinement` boundary still requires every constraint to
  solve, but permits those session-owned metas to remain in the checked call;
  dependent result checking can therefore solve determined arguments before
  the remaining goals are reported;
- refinement is synchronous and failure-atomic. A thrown checker or tactic
  error restores pre-existing solutions and constraint outcomes, removes new
  metas/constraints, and restores deterministic meta/constraint ordinals;
- focused negatives cover wrong-type and unresolved `exact`, non-Pi `intro`,
  non-function `apply`, an unreachable session meta, and an application that
  first solves an argument and then fails on a later rigid result component.
  None changes the proof state;
- `LEGACY_MIGRATION_INVENTORY` revision `MIGRATE-1C` marks proof traversal and
  refinement covered, points `proof_mode_tests.ts` at both Core replacement
  suites, and makes the final readiness audit MIGRATE-1D next.

### Experiment MIGRATE-1C-CHECKED-PROOF-REFINEMENT

```text
Experiment ID: MIGRATE-1C-CHECKED-PROOF-REFINEMENT
Date and checkpoint: 2026-07-24 at MIGRATE-1B checkpoint 3e48b97
Question/hypothesis: exact, intro, and apply can refine only reachable
  session-owned contextual goals through the Core checker while keeping the
  proof root immutable and making every rejected tactic failure-atomic,
  without retaining mutable holes, global definitions, or category cases.
Authority and owner position inspected: D-018/D-020/D-034/D-035 and C-11/C-19
  in this plan; Core context/session/checker and MIGRATE-1A proof inspection;
  legacy src/proof.ts and proof_mode_tests.ts. No Lambdapi owner or rule
  changed.
Current worktree/branch and baseline relationship:
  /home/user1/emdash1-elaborator-goal on
  goal/typescript-elaborator-v3.2 at 3e48b97 before the experiment;
  descendant of baseline a06433e.
Minimal positive consumer: check an exact proof of A; construct and close the
  identity A -> A by intro/exact while preserving a natural binder; apply a
  unary function and a mixed implicit/explicit function; apply
  d : (x:A) -> P(x) to goal P(z) and let result checking solve x := z.
Relevant negative/non-collapse consumer: reject a B-term for an A goal, an
  unresolved exact term, intro at A, apply of a non-function, an unrelated
  session meta, and an apply whose result first solves x := z and then
  mismatches z against a distinct rigid w. Verify no allocation, constraint,
  solution, or ordinal survives failure. Execute no proof-time product rule.
Probe command and bounded result: the inventory, proof-state, and refinement
  suites pass 21 tests / 3 suites with no skips.
Observed result: exact closes without new goals; intro exposes one contextual
  body goal; apply exposes ordered plicity-bearing premises; dependent
  checking can solve an argument and leave no goal; all failure cases preserve
  the prior proof state and deterministic next ordinal.
Unexpected result or failure: none. The legacy apply behavior of consuming
  every syntactic Pi binder was retained only as this explicit bounded tactic
  contract; no generic normalization or search was added.
TypeScript consequence: accept D-036; complete MIGRATE-1C; mark the proof
  mechanism covered and make the frozen replacement/readiness audit
  MIGRATE-1D next.
Lambdapi consequence: none. Completed proof terms still cross the existing
  checker/backend boundary; raw subgoal metas remain non-serializable. Add no
  declaration, rule, comparison, warning, audit, catalog, or health change.
Decision: accept.
Plan rows changed: D-036 accepted; C-19 partial through MIGRATE-1C;
  MIGRATE-1C complete; MIGRATE-1D dependency-ready.
Remaining prerequisite or human review: none for MIGRATE-1D. H-05 and H-06
  remain at their recorded later triggers.
```

### MIGRATE-1C validation

Validated on the exact MIGRATE-1C worktree diff:

```text
node --require ts-node/register --test
  tests/v3_2_migration_inventory_tests.ts
  tests/v3_2_proof_state_tests.ts
  tests/v3_2_proof_refinement_tests.ts
  passed 21 tests / 3 suites with no skips

node --require ts-node/register --test tests/v3_2_*_tests.ts
  passed 215 tests / 22 suites: 196 passed, 19 opt-in probes skipped

./scripts/pnpmw run check:ts
  workspace contract, TypeScript, ESLint, and root tests passed
  367 tests / 65 suites: 348 passed, 19 opt-in probes skipped

EMDASH_TYPECHECK_TIMEOUT=60s make -C emdash2 check
  active kernel, extensions, and diagnostics passed

EMDASH_TYPECHECK_TIMEOUT=60s ./scripts/pnpmw run check:all
  root TypeScript gate passed with the same 367-test result
  41 active Lambdapi kernel/example files passed
  39 formal infrastructure tests and 5 print registry tests passed
  active-reference/report-header/book/evidence/typography/KaTeX checks passed
  strict rule-LHS audit and generated catalog freshness passed

git diff --check
  passed
```

## Completed Slice: MIGRATE-1D

MIGRATE-1D turns the completed replacement work into an executable,
reviewable pre-deletion contract:

- `LEGACY_MIGRATION_INVENTORY` revision `MIGRATE-1D` marks every
  port/reimplementation mechanism covered by surviving v3.2 evidence and
  every deletion mechanism `ready-to-delete`; textual parsing remains an
  optional future H-06 product slice, not a prerequisite for deleting the old
  parser;
- `LEGACY_MIGRATION_READINESS` derives the exact thirteen-source and
  twenty-two-test deletion lists from that inventory, adds the legacy-only
  `tests/utils.ts`, and rejects any content, ordering, consumer, command, or
  authority-boundary drift;
- an executable relative-import graph proves that the old source graph closes
  over itself, every old test closes over the 36-file deletion set,
  `src/v3_2` imports only within `src/v3_2`, and no v3.2 test imports a
  deletion target;
- the only external direct legacy importers are `tests/main_tests.ts` and
  `emdash-template/src/emdash_api.ts`. The readiness record also captures the
  transitive template consumer `App.tsx`, its packaging README, both audit
  lifecycle transitions, and the parser-only `package.json`/`pnpm-lock.yaml`
  cleanup;
- the future template rewrite must expose a genuine v3.2 session-local
  example. It may not recreate the old globals, reset API, D0/D1 names, or a
  compatibility barrel;
- Lambdapi remains the executable specification and required conformance
  oracle through GRADUATE-1/H-05. MIGRATE-2 does not modify any active
  `emdash2` authority.

### Experiment MIGRATE-1D-PHYSICAL-DELETION-READINESS

```text
Experiment ID: MIGRATE-1D-PHYSICAL-DELETION-READINESS
Date and checkpoint: 2026-07-24 at MIGRATE-1C checkpoint 8eae126
Question/hypothesis: the legacy root engine can have an exact, closed, and
  reviewable physical-deletion boundary whose replacement evidence survives
  deletion and whose live direct/transitive consumers are all known before
  MIGRATE-2 starts.
Authority and owner position inspected: D-001/D-002/D-004/D-011/D-034 through
  D-036 and C-11/C-19 in this plan; the frozen product/runtime/differential
  artifacts; root package/test configuration; all root legacy source/test
  imports; and the standalone emdash-template consumer. No Lambdapi owner or
  rule changed.
Current worktree/branch and baseline relationship:
  /home/user1/emdash1-elaborator-goal on
  goal/typescript-elaborator-v3.2 at 8eae126 before the experiment;
  descendant of baseline a06433e.
Minimal positive consumer: derive the exact source/test deletion lists from
  the frozen inventory, add the sole legacy-only helper, prove all relative
  imports close, and prove the v3.2 source/test graph imports no deletion
  target.
Relevant negative/non-collapse consumer: reject changed deletion targets,
  missing consumer edits, disappearing replacement evidence, altered gate or
  authority text, an unrecorded direct importer, a v3.2-to-legacy import, or
  an attempted compatibility-barrel boundary.
Probe command and bounded result: the inventory/readiness/pattern/proof-state/
  proof-refinement suites pass 40 tests / 5 suites with no skips; all v3.2
  suites pass 221 tests / 23 suites, with 202 passed and 19 opt-in probes
  skipped.
Observed result: all 13 source files, 22 tests, and one helper form a closed
  deletion set. The root runner and template barrel are the only external
  direct importers. The template app is a transitive consumer, its README
  describes copying the old engine, and parsimmon is used only by the old
  parser.
Unexpected result or failure: the standalone template and parser-only package
  dependency were not explicit in the MIGRATE-1A file inventory. They are now
  mandatory MIGRATE-2 edits rather than post-deletion breakage.
TypeScript consequence: accept D-037; complete MIGRATE-1 and MIGRATE-1D; make
  physical deletion MIGRATE-2 dependency-ready next.
Lambdapi consequence: none. Keep every active authority, warning, rule, audit,
  catalog, health record, and conformance obligation unchanged.
Decision: accept.
Plan rows changed: D-037 accepted; C-19 replacement-ready through MIGRATE-1D;
  MIGRATE-1 and MIGRATE-1D complete; MIGRATE-2 dependency-ready.
Remaining prerequisite or human review: none for MIGRATE-2. H-05 remains at
  GRADUATE-1 after deletion; H-06 remains conditional on measured parser need.
```

### MIGRATE-1D validation

Validated on the exact MIGRATE-1D worktree diff:

```text
node --require ts-node/register --test
  tests/v3_2_migration_inventory_tests.ts
  tests/v3_2_migration_readiness_tests.ts
  tests/v3_2_pattern_unification_tests.ts
  tests/v3_2_proof_state_tests.ts
  tests/v3_2_proof_refinement_tests.ts
  passed 40 tests / 5 suites with no skips

node --require ts-node/register --test tests/v3_2_*_tests.ts
  passed 221 tests / 23 suites: 202 passed, 19 opt-in probes skipped

./scripts/pnpmw run check:ts
  workspace contract, TypeScript, ESLint, and root tests passed
  373 tests / 66 suites: 354 passed, 19 opt-in probes skipped

EMDASH_TYPECHECK_TIMEOUT=60s make -C emdash2 check
  active kernel, extensions, and diagnostics passed

EMDASH_TYPECHECK_TIMEOUT=60s ./scripts/pnpmw run check:all
  root TypeScript gate passed with the same 373-test result
  41 active Lambdapi kernel/example files passed
  39 formal infrastructure tests and 5 print registry tests passed
  active-reference/report-header/book/evidence/typography/KaTeX checks passed
  strict rule-LHS audit and generated catalog freshness passed

git diff --check
  passed
```

## Completed Slice: MIGRATE-2

MIGRATE-2 performs the reviewed physical cut without preserving the retired
API:

- all thirteen root legacy source modules, all twenty-two inventoried legacy
  tests, and the legacy-only test helper are deleted. The root runner now
  imports only v3.2 suites and has no global debug/reset setup;
- the frozen MIGRATE-1D inventory and readiness records remain as historical
  audit inputs. The distinct `LEGACY_MIGRATION_COMPLETION` record derives the
  36 deleted paths and eight completed edit paths from them, records
  `parsimmon` removal, rejects compatibility retention, and points to
  GRADUATE-1;
- `src/v3_2/browser.ts` is the narrow browser product entry point. Its
  transitive graph includes Core construction, session-local metas, checking,
  and reviewed runtime comparison but excludes migration ledgers,
  differential harnesses, and process/filesystem-backed probes;
- the reviewed manifest keeps the exact H-03 SHA-256 pin and now compares the
  complete canonical content directly instead of importing `node:crypto`.
  Existing status, approval, owner, signature, rule, trust-boundary, and hash
  drift tests remain green, while the checker/runtime dependency graph becomes
  browser-safe;
- the standalone template exports only that browser entry point. Its default
  program constructs and checks a category-polymorphic identity using a fresh
  `CoreElaborationSession`; no global definition, reset, parser, or legacy
  elaboration call remains. Strict template TypeScript and a Vite production
  build pass;
- `parsimmon` is removed from `package.json` and the shared lockfile through
  the pinned pnpm wrapper. The template packaging instructions now copy only
  the browser dependency tree, while the old README/report material is
  explicitly labeled historical;
- post-deletion tests reject any reappearing target, unresolved import to the
  deletion set, non-v3.2 root test, Node import reachable from the browser
  entry point, unrecorded fixture/package state, or D0/D1/legacy API surface.

### Experiment MIGRATE-2-PHYSICAL-CUT

```text
Experiment ID: MIGRATE-2-PHYSICAL-CUT
Date and checkpoint: 2026-07-24 at MIGRATE-1D checkpoint b7b6995
Question/hypothesis: the exact frozen 36-file legacy graph can be deleted,
  every recorded consumer/package edge can be rewritten to the v3.2 product
  path, and the resulting browser consumer can remain session-local and
  Node-free without weakening the reviewed manifest boundary.
Authority and owner position inspected: D-001/D-002/D-004/D-011/D-023/
  D-024/D-030/D-033/D-034/D-037 and C-17/C-19/C-20 in this plan; the complete
  MIGRATE-1 inventory/readiness records; root runner/package/lockfile; the
  standalone template; and the manifest/checker/runtime import graph. No
  Lambdapi declaration or rule changed.
Current worktree/branch and baseline relationship:
  /home/user1/emdash1-elaborator-goal on
  goal/typescript-elaborator-v3.2 at b7b6995 before the experiment;
  descendant of baseline a06433e.
Minimal positive consumer: import only src/v3_2/browser.ts, construct and
  checker-validate a category-polymorphic identity, serialize its exact term
  and type, create two isolated sessions, then strict-typecheck and
  production-build the same API through emdash-template.
Relevant negative/non-collapse consumer: assert all 36 targets absent; reject
  any import resolving to them, non-v3.2 root runner import, browser-reachable
  node: module, process-backed harness, old template symbol, compatibility
  barrel, parser dependency, changed completion record, or changed reviewed
  manifest content/hash.
Probe command and bounded result: the migration/browser/manifest/pattern/
  proof-state/proof-refinement suites pass 69 tests / 8 suites with no skips;
  all v3.2 suites pass 224 tests / 24 suites, with 205 passed and 19 opt-in
  probes skipped. The standalone template passes strict TypeScript and Vite
  transforms 48 modules into a production bundle.
Observed result: the deletion graph is gone, all surviving source resides
  under src/v3_2, the root runner loads only retained v3.2 tests, the browser
  graph reaches checker/session/runtime/manifest with no Node built-in, and
  the package/lockfile contain no parsimmon.
Unexpected result or failure: CoreChecker's reviewed runtime path reached the
  manifest's synchronous node:crypto hash recomputation, so the first strict
  browser check exposed a Node-only product dependency. Exact comparison with
  the already pinned canonical manifest content provides the same closed-world
  drift rejection without recomputing SHA-256 at runtime. isolatedModules also
  exposed one type-only re-export and one unused signature helper; both were
  corrected without changing Core behavior.
TypeScript consequence: accept D-038; complete C-19 and MIGRATE-2; publish the
  browser-safe product entry point and frozen migration-completion record.
Lambdapi consequence: none. Keep active authority, warnings, rules, audits,
  catalogs, health, and the required conformance-oracle policy unchanged
  through H-05.
Decision: accept.
Plan rows changed: D-038 accepted; C-19 complete; MIGRATE-2 complete;
  GRADUATE-1/H-05 next.
Remaining prerequisite or human review: GRADUATE-1 must publish and present
  the concrete H-05 recommendation before the user decides the deployed
  authority/oracle policy. H-06 remains conditional on measured parser need.
```

### MIGRATE-2 validation

Validated on the exact MIGRATE-2 worktree diff:

```text
node --require ts-node/register --test
  tests/v3_2_migration_inventory_tests.ts
  tests/v3_2_migration_readiness_tests.ts
  tests/v3_2_browser_api_tests.ts
  tests/v3_2_manifest_tests.ts
  tests/v3_2_pattern_unification_tests.ts
  tests/v3_2_proof_state_tests.ts
  tests/v3_2_proof_refinement_tests.ts
  passed 69 tests / 8 suites with no skips

node --require ts-node/register --test tests/v3_2_*_tests.ts
  passed 224 tests / 24 suites: 205 passed, 19 opt-in probes skipped

./scripts/pnpmw --dir emdash-template --ignore-workspace exec
  tsc --noEmit -p tsconfig.json
./scripts/pnpmw --dir emdash-template --ignore-workspace exec vite build
  strict TypeScript passed; Vite transformed 48 modules and built the
  production fixture

./scripts/pnpmw run check:ts
  workspace contract, TypeScript, ESLint, and root tests passed
  224 tests / 24 suites: 205 passed, 19 opt-in probes skipped

EMDASH_TYPECHECK_TIMEOUT=60s make -C emdash2 check
  active kernel, extensions, and diagnostics passed

EMDASH_TYPECHECK_TIMEOUT=60s ./scripts/pnpmw run check:all
  root TypeScript gate passed with the same 224-test result
  41 active Lambdapi kernel/example files passed
  39 formal infrastructure tests and 5 print registry tests passed
  active-reference/report-header/book/evidence/typography/KaTeX checks passed
  strict rule-LHS audit and generated catalog freshness passed

git diff --check
  passed
```

## Completed Slice: GRADUATE-1A

GRADUATE-1A freezes the evidence and recommendation that H-05 must review. It
does not graduate the TypeScript kernel by itself:

- `CORE_MVP_GRADUATION_RECOMMENDATION` pins D-039 to the exact
  `emdash-v3.2-mvp-1` revision, content hash, sixteen owners, three runtime
  rules, browser entry point, and absence of a production Lambdapi dependency;
- the recommendation derives its trust ceiling from the separately approved
  H-04 artifact. Exact-fragment termination, bounded comparison, and the three
  rules remain authorized; general confluence and standalone TypeScript
  subject reduction remain withheld;
- the evidence record requires the complete TSK-3 matrix—sixteen owner rows,
  three rule rows, two higher-cell packages, and no unclosed row—and the exact
  36-target MIGRATE-2 result;
- the operational review records the checker's fixed 256-step comparison
  bound and the strict browser typecheck/production build. It makes no
  latency, throughput, or scale claim; representative measurement is required
  before making one;
- retaining two implementations has a deliberately bounded maintenance cost.
  Lambdapi acceptance is required only for selected owner-signature,
  rule-shape/authority, profile-promotion, metatheory-claim, and shared-corpus
  binding changes. Boundary-preserving refactors, surface/diagnostic work, and
  packaging changes require normal gates but no new declaration-level
  authority decision;
- Lambdapi remains the active mathematical specification, frozen-corpus CI
  oracle, and subject-reduction oracle, but never becomes a per-term product
  checker or production runtime dependency;
- C-18 backend diagnostic remapping and release-policy synchronization remain
  RELEASE-READY work. Performance benchmarking gates a future performance
  claim, not this semantic-authority decision;
- validation rejects any manifest, evidence, authority-policy, claim,
  release-follow-up, or decision-question drift. `authorityAuthorized: false`
  ensures that only a distinct post-review GRADUATE-1B artifact can record
  approval.

### Experiment GRADUATE-1A-AUTHORITY-SPLIT

```text
Experiment ID: GRADUATE-1A-AUTHORITY-SPLIT
Date and checkpoint: 2026-07-24 at MIGRATE-2 checkpoint 5bcabd6
Question/hypothesis: can TypeScript own the deployed frozen MVP without
  falsely displacing Lambdapi where H-04 still relies on it?
Authority and owner position inspected: active v3.2 mathematical authority;
  H-03-reviewed manifest; H-04 review; all TSK-3 completion rows; MIGRATE-2
  product boundary; checker comparison limit; browser entry point.
Current worktree/branch and baseline relationship:
  goal/typescript-elaborator-v3.2 at descendant 5bcabd6 of baseline
  a06433e57cba95e7d35f8577b7c71912862c3d25
Minimal positive consumer: exact content-pinned sixteen-owner/three-rule
  TypeScript profile through src/v3_2/browser.ts, with completed shared
  TypeScript/Lambdapi parity and no production Lambdapi dependency.
Relevant negative/non-collapse consumer: reject any new owner/rule, altered
  signature/authority, broadened confluence or subject-reduction claim,
  ci-only Lambdapi policy, runtime Lambdapi dependency, or retroactive
  authorization of the proposal.
Probe command and bounded result: focused graduation/H-04/TSK-3/MIGRATE-2
  evidence passes 25 of 26 tests with only the opt-in Lambdapi row skipped;
  all three shared-fragment Lambdapi differential suites pass 19 tests with
  no skips;
  all v3.2 suites pass 231 tests / 25 suites, with 212 passed and 19 opt-in
  probes skipped; the bounded active kernel check and standalone browser
  typecheck/build pass.
Observed result: the deployed/runtime role can be separated cleanly from
  mathematical and selected-change acceptance. The existing evidence closes
  the exact frozen product matrix but does not eliminate H-04's theorem gap.
Unexpected result or failure: none. Performance evidence supports bounded,
  browser-buildable operation but no workload SLA, so the proposal explicitly
  withholds one instead of turning an unmeasured property into a graduation
  claim.
TypeScript consequence: propose D-039 and complete GRADUATE-1A; grant no
  deployed authority until a distinct reviewed artifact records H-05.
Lambdapi consequence: recommend retaining mathematical, fixed-corpus CI,
  subject-reduction, and five selected change-acceptance roles without a
  production runtime dependency.
Decision: propose D-039 for H-05 review.
Plan rows changed: D-039 proposed; C-18 scoped to RELEASE-READY;
  GRADUATE-1 split; GRADUATE-1A complete; GRADUATE-1B/H-05 next.
Remaining prerequisite or human review: the user must approve or revise
  H-05/D-039 before GRADUATE-1B or RELEASE-READY can proceed.
```

### GRADUATE-1A validation

Validated on the exact GRADUATE-1A worktree diff:

```text
node --require ts-node/register --test
  tests/v3_2_graduation_tests.ts
  tests/v3_2_metatheory_review_tests.ts
  tests/v3_2_differential_higher_cell_tests.ts
  tests/v3_2_migration_inventory_tests.ts
  passed 25 of 26 tests / 4 suites; only the opt-in Lambdapi row skipped

node --require ts-node/register --test tests/v3_2_*_tests.ts
  passed 231 tests / 25 suites: 212 passed, 19 opt-in probes skipped

EMDASH_RUN_LAMBDAPI_PROBES=1 node --require ts-node/register --test
  tests/v3_2_differential_owner_tests.ts
  tests/v3_2_differential_rule_tests.ts
  tests/v3_2_differential_higher_cell_tests.ts
  passed 19 tests / 3 suites with no skips

./scripts/pnpmw --dir emdash-template --ignore-workspace exec
  tsc --noEmit -p tsconfig.json
./scripts/pnpmw --dir emdash-template --ignore-workspace exec vite build
  strict TypeScript passed; Vite transformed 48 modules and built the
  production fixture

EMDASH_TYPECHECK_TIMEOUT=60s make -C emdash2 check
  active kernel, extensions, and diagnostics passed

./scripts/pnpmw run check:ts
  workspace contract, TypeScript, ESLint, and root tests passed
  231 tests / 25 suites: 212 passed, 19 opt-in probes skipped

EMDASH_TYPECHECK_TIMEOUT=60s ./scripts/pnpmw run check:all
  root TypeScript gate passed with the same 231-test result
  41 active Lambdapi kernel/example files passed
  39 formal infrastructure tests and 5 print registry tests passed
  active-reference/report-header/book/evidence/typography/KaTeX checks passed
  strict rule-LHS audit and generated catalog freshness passed

git diff --check
  passed
```

## Completed Slice: GRADUATE-1B

GRADUATE-1B records the user's approval without modifying the proposal that
was reviewed:

- `CORE_MVP_GRADUATION_REVIEW` snapshots
  `CORE_MVP_GRADUATION_RECOMMENDATION` as distinct immutable data, retaining
  its historical `authorityAuthorized: false` field;
- the separate approval is exactly H-05/D-039, `approved-as-proposed` on
  2026-07-24;
- TypeScript is now the authoritative deployed runtime checker/evaluator only
  for the content-pinned sixteen-owner/three-rule
  `emdash-v3.2-mvp-1` profile;
- Lambdapi remains the active mathematical specification, mandatory frozen
  corpus and subject-reduction oracle, and acceptance authority for the five
  reviewed semantic-boundary changes. It is forbidden as a production runtime
  dependency and is not a per-term product checker;
- general confluence and standalone TypeScript subject reduction remain
  withheld. No additional owner/rule, performance SLA, or RELEASE-READY claim
  is authorized;
- validation rejects approval, proposal, profile, oracle-role, acceptance
  trigger, theorem-claim, or release-state drift.

### GRADUATE-1B validation

Validated on the exact GRADUATE-1B worktree diff:

```text
node --require ts-node/register --test
  tests/v3_2_graduation_tests.ts
  tests/v3_2_graduation_review_tests.ts
  tests/v3_2_metatheory_review_tests.ts
  passed 19 tests / 3 suites with no skips

node --require ts-node/register --test tests/v3_2_*_tests.ts
  passed 237 tests / 26 suites: 218 passed, 19 opt-in probes skipped

EMDASH_TYPECHECK_TIMEOUT=60s make -C emdash2 check
  active kernel, extensions, and diagnostics passed

./scripts/pnpmw run check:ts
  workspace contract, TypeScript, ESLint, and root tests passed
  237 tests / 26 suites: 218 passed, 19 opt-in probes skipped

EMDASH_TYPECHECK_TIMEOUT=60s ./scripts/pnpmw run check:all
  root TypeScript gate passed with the same 237-test result
  41 active Lambdapi kernel/example files passed
  39 formal infrastructure tests and 5 print registry tests passed
  active-reference/report-header/book/evidence/typography/KaTeX checks passed
  strict rule-LHS audit and generated catalog freshness passed

git diff --check
  passed
```

## Completed Slice: RELEASE-1A

RELEASE-1A completes C-18 at the process-backed conformance boundary without
adding a Node dependency to the browser product:

- `LambdapiProbeResult.rawDiagnostics` preserves the exact stdout/stderr/spawn
  error concatenation that callers previously received;
- `remapLambdapiProbeDiagnostics` recognizes the observed
  `[path:line:start-end]` header after removing ANSI only for parsing. It maps
  only an explicitly supplied temporary probe path and an exact
  `ProbeSourceMapEntry.generatedLine`;
- imported-authority paths, same-basename paths, generated comments/blanks,
  and other unmapped lines remain raw. Duplicate headers produce one
  structured mapping rather than repeated source attribution;
- all six generated statement kinds carry their original `SourceSpan`,
  label, kind, and generated path/range in
  `ProbeSourceMappedDiagnostic`;
- `formatLambdapiProbeDiagnostics` places full source spans before the raw
  backend output. With no mapping it returns the raw text unchanged;
- `checkLambdapiProbe` accepts both the actual relative temporary path and its
  absolute path, returns structured mappings, and exposes the source-facing
  rendering through its existing `diagnostics` field;
- synthetic tests cover ANSI, relative/absolute paths, all statement kinds,
  deduplication, and non-attribution. A bounded real Lambdapi failure at
  generated line 8 maps to `fixtures/c18_surface.ts:42:7-42:19`.

### Experiment RELEASE-1A-DIAGNOSTIC-LOCATION

```text
Experiment ID: RELEASE-1A-DIAGNOSTIC-LOCATION
Date and checkpoint: 2026-07-24 at GRADUATE-1B checkpoint aeb5221
Question/hypothesis: does Lambdapi expose a stable generated location that can
  be mapped without guessing columns or attributing imported-kernel errors?
Authority and owner position inspected: process-backed conformance probe only;
  no mathematical owner or rule changed.
Current worktree/branch and baseline relationship:
  goal/typescript-elaborator-v3.2 at descendant aeb5221 of baseline
  a06433e57cba95e7d35f8577b7c71912862c3d25
Minimal positive consumer: a valid generated category declaration followed by
  an intentionally false `assert ⊢ c18_A : TYPE` at mapped generated line 8.
Relevant negative/non-collapse consumer: ANSI headers, imported
  emdash3_2.lp locations, a different probe.lp path, generated comment/blank
  lines, absent source-map rows, and duplicate locations.
Probe command and bounded result:
  EMDASH_RUN_LAMBDAPI_PROBES=1 node --require ts-node/register --test
  tests/v3_2_probe_diagnostic_tests.ts
  passes 4 tests / 1 suite with no skips; the observed assertion failure maps
  exactly and the checker stays within 30 seconds.
Observed result: warning-suppressed Lambdapi emits
  `[tmp/elab0-.../probe.lp:8:0-20] Assertion failed.`. Exact path/line matching
  is sufficient; generated columns are retained as backend evidence while the
  original full SourceSpan supplies the user-facing location.
Unexpected result or failure: ANSI starts with its own `[` control sequence,
  so parsing the unstripped stream first captured the color code as part of
  the path. Strip ANSI only into a parsing view while preserving raw output.
TypeScript consequence: accept D-040's RELEASE-1A split and complete C-18.
Lambdapi consequence: none; only diagnostics from the optional conformance
  process are interpreted.
Decision: accept.
Plan rows changed: C-18 complete; RELEASE-1A complete; RELEASE-1B next.
Remaining prerequisite or human review: none for RELEASE-1B.
```

### RELEASE-1A validation

Validated on the exact RELEASE-1A worktree diff:

```text
node --require ts-node/register --test
  tests/v3_2_probe_diagnostic_tests.ts
  tests/v3_2_elab0_tests.ts
  tests/v3_2_dependent_context_tests.ts
  passed 26 of 33 tests / 3 suites; seven opt-in probes skipped

EMDASH_RUN_LAMBDAPI_PROBES=1 node --require ts-node/register --test
  tests/v3_2_probe_diagnostic_tests.ts
  passed 4 tests / 1 suite with no skips

node --require ts-node/register --test tests/v3_2_*_tests.ts
  passed 241 tests / 27 suites: 221 passed, 20 opt-in probes skipped

./scripts/pnpmw run check:ts
  workspace contract, TypeScript, ESLint, and root tests passed
  241 tests / 27 suites: 221 passed, 20 opt-in probes skipped

EMDASH_TYPECHECK_TIMEOUT=60s make -C emdash2 check
  active kernel, extensions, and diagnostics passed

EMDASH_TYPECHECK_TIMEOUT=60s ./scripts/pnpmw run check:all
  root TypeScript gate passed with the same 241-test result
  41 active Lambdapi kernel/example files passed
  39 formal infrastructure tests and 5 print registry tests passed
  active-reference/report-header/book/evidence/typography/KaTeX checks passed
  strict rule-LHS audit and generated catalog freshness passed

git diff --check
  passed
```

## Completed Slice: RELEASE-1B

RELEASE-1B turns the H-05 oracle policy into a required repository boundary
without coupling the deployed checker to Lambdapi:

- `CORE_MVP_RELEASE_POLICY` is a distinct deep-frozen `RELEASE-1B` artifact.
  It validates the unchanged H-03 manifest, TSK-3 completion, and GRADUATE-1B
  approval before pinning the exact profile and retained oracle roles;
- the historical TSK-3 completion still says “required until graduation” and
  the H-05 review still says `releaseReady: false`. RELEASE-1B does not rewrite
  either record; its post-graduation policy requires the oracle going forward;
- `check:conformance` runs the exact owner, rule, and higher-cell differential
  suites with `EMDASH_RUN_LAMBDAPI_PROBES=1` under one 60-second process
  bound. `check:all` now requires that command between `check:ts` and the full
  Lambdapi workspace CI;
- executable drift checks bind the command bodies, three test files, 16/3/2
  corpus dimensions, three oracle processes, five acceptance triggers, and
  every synchronized public artifact;
- the browser barrel exports the already-reviewed `CORE_MVP_MANIFEST`, letting
  consumers observe `emdash-v3.2-mvp-1`, 16 owners, and three rules. It still
  exports no release policy, process probe, or differential harness and remains
  transitively Node-free;
- the root README, elaborator handoff, standalone README, and browser example
  now agree on deployed TypeScript authority, required Lambdapi roles, the
  absence of production coupling, withheld theorem/performance claims, and the
  unimplemented parser boundary;
- the standalone example prints the exact manifest revision before checking
  its category-polymorphic identity.

### Experiment RELEASE-1B-MANDATORY-ORACLE

```text
Experiment ID: RELEASE-1B-MANDATORY-ORACLE
Date and checkpoint: 2026-07-24 at RELEASE-1A checkpoint ac83635
Question/hypothesis: can the entire frozen shared corpus be mandatory in the
  repository gate within the 60-second SOP bound while the browser deployment
  remains Lambdapi- and Node-process-free?
Authority and owner position inspected: unchanged H-03 manifest, three H-04
  runtime rules, TSK-3 owner/rule/higher-cell corpus, and H-05 policy only; no
  mathematical declaration or rule changed.
Current worktree/branch and baseline relationship:
  goal/typescript-elaborator-v3.2 at descendant ac83635 of baseline
  a06433e57cba95e7d35f8577b7c71912862c3d25
Minimal positive consumer: the exact 19-test TSK-3 corpus with all three
  process-backed Lambdapi checks enabled, followed by the standalone Vite
  identity example reading CORE_MVP_MANIFEST.revision.
Relevant negative/non-collapse consumer: release-policy, package-script,
  documentation, corpus-dimension, browser-export, theorem-claim, and
  production-dependency drift; existing import traversal still rejects every
  Node/process-backed module from the browser graph.
Probe command and bounded result:
  ./scripts/pnpmw run check:conformance
  passes 19 tests / 3 suites with no skips and three actual Lambdapi processes
  in 3.5 seconds under the outer 60-second bound.
Observed result: the exact fixed corpus is comfortably bounded and requires no
  production runtime change. The standalone fixture still typechecks and Vite
  transforms 48 modules into a production build.
Unexpected result or failure: the first documentation harness used
  line-sensitive regular expressions, and one dynamic import omitted the
  NodeNext `.js` spelling. Whitespace-aware assertions plus the normal static
  TypeScript import fixed the harness without weakening its semantic checks.
TypeScript consequence: accept D-041; keep check:ts lightweight, make the
  explicit conformance command mandatory in check:all, and publish the frozen
  profile identity through the browser barrel.
Lambdapi consequence: retain the active sources unchanged as mandatory
  mathematical/fixed-corpus/subject-reduction evidence and selected-change
  acceptance authority.
Decision: accept.
Plan rows changed: D-041 accepted; RELEASE-1B complete; RELEASE-1C next.
Remaining prerequisite or human review: none for RELEASE-1C.
```

### RELEASE-1B validation

Validated on the exact RELEASE-1B worktree diff:

```text
node --require ts-node/register --test
  tests/v3_2_release_policy_tests.ts
  tests/v3_2_browser_api_tests.ts
  tests/v3_2_graduation_review_tests.ts
  passed 13 tests / 3 suites with no skips

./scripts/pnpmw run check:conformance
  passed 19 tests / 3 suites with three actual Lambdapi oracle processes,
  no skips, and a 3.5-second result under the 60-second outer bound

node --require ts-node/register --test tests/v3_2_*_tests.ts
  passed 246 tests / 28 suites: 226 passed, 20 opt-in probes skipped

./scripts/pnpmw --dir emdash-template --ignore-workspace exec
  tsc --noEmit -p tsconfig.json
./scripts/pnpmw --dir emdash-template --ignore-workspace exec vite build
  strict TypeScript passed; Vite transformed 48 modules and built the
  production fixture

./scripts/pnpmw run check:ts
  workspace contract, TypeScript, ESLint, and root tests passed
  246 tests / 28 suites: 226 passed, 20 opt-in probes skipped

EMDASH_TYPECHECK_TIMEOUT=60s make -C emdash2 check
  active kernel, extensions, and diagnostics passed

EMDASH_TYPECHECK_TIMEOUT=60s ./scripts/pnpmw run check:all
  root TypeScript gate passed with the same 246-test result
  mandatory conformance passed 19 tests / 3 suites with no skips
  41 active Lambdapi kernel/example files passed
  39 formal infrastructure tests and 5 print registry tests passed
  active-reference/report-header/book/evidence/typography/KaTeX checks passed
  strict rule-LHS audit and generated catalog freshness passed

git diff --check
  passed
```

## Completed Slice: RELEASE-1C

RELEASE-1C closes this plan's concrete implementation ledger while preserving
the exact scope and history that made the release claim reviewable:

- `CORE_MVP_RELEASE_COMPLETION` is a new deep-frozen record. It depends on but
  does not mutate the H-03 manifest, H-04 review, H-05 review, MIGRATE-2
  completion, or RELEASE-1B policy;
- it marks only `emdash-v3.2-mvp-1` release-ready, with the same content hash,
  sixteen owners, three runtime rules, browser entry point, and forbidden
  production Lambdapi dependency;
- all twenty-one C-00 through C-20 rows are complete. The only non-complete
  implementation-ledger alternatives are KERNEL-DISPLAYED-1/2, which remain
  conditional on a concrete displayed-owner failure that ELAB-2C did not
  produce;
- the release-blocker list is empty. H-02 remains conditional on that absent
  failure and H-06 remains conditional on measured textual-parser need;
- out-of-profile owner/rule promotion, proof-time execution, generic
  beta/eta/unfolding, general higher-order unification, a textual parser,
  general confluence, standalone TypeScript subject reduction, and a
  performance SLA remain explicit exclusions rather than hidden incomplete
  release work;
- the fixed checker comparison limit is 256 global runtime rewrite steps.
  This is an operation budget, not a wall-clock, latency, throughput, or scale
  guarantee. No benchmark is required for the current no-SLA release;
  representative workload measurement and separate review are required before
  any future performance claim;
- the final artifact pins every focused, conformance, browser, TypeScript,
  bounded-kernel, full-repository, and diff-check command. It stays outside the
  narrow browser API.

### Experiment RELEASE-1C-RESIDUAL-AUDIT

```text
Experiment ID: RELEASE-1C-RESIDUAL-AUDIT
Date and checkpoint: 2026-07-24 at RELEASE-1B checkpoint 9aa87a0
Question/hypothesis: after diagnostics and mandatory conformance are complete,
  does any concrete capability, implementation slice, authority decision,
  packaging obligation, or measured performance prerequisite still block the
  exact frozen profile from RELEASE-READY?
Authority and owner position inspected: C-00 through C-20; the full
  implementation ledger; H-02/H-06 triggers; H-03/H-04/H-05 artifacts;
  MIGRATE-2; RELEASE-1A/1B; checker limit; browser graph; and final commands.
Current worktree/branch and baseline relationship:
  goal/typescript-elaborator-v3.2 at descendant 9aa87a0 of baseline
  a06433e57cba95e7d35f8577b7c71912862c3d25
Minimal positive consumer: all 21 capability rows, exact 16-owner/three-rule
  manifest, mandatory 19-test oracle corpus, Node-free browser identity
  example, and final check:all gate.
Relevant negative/non-collapse consumer: historical records must remain
  non-ready; the browser must not export completion/policy/probes; no
  conditional gate, excluded mechanism, theorem non-claim, or performance
  non-claim may be silently converted into product scope.
Probe command and bounded result:
  focused completion/policy/browser tests pass 13 tests / 3 suites; the
  mandatory oracle passes 19 tests / 3 suites with no skips under 60 seconds;
  the complete TypeScript corpus passes 252 tests / 29 suites with 20 opt-in
  probes skipped; browser typecheck/build and bounded active kernel pass.
Observed result: every concrete ledger row and release criterion is complete.
  KERNEL-DISPLAYED-1/2, H-02, and H-06 are conditional and untriggered, not
  residual blockers. No performance claim exists that would require a current
  benchmark.
Unexpected result or failure: none. The residual audit found only deliberate
  frozen-profile exclusions and future-trigger policies already required by
  H-04/H-05.
TypeScript consequence: accept D-042 and publish the separate RELEASE-1C
  completion record with releaseReady true and no next slice.
Lambdapi consequence: no source or authority change; keep every D-039/D-041
  mathematical, mandatory-oracle, and selected-change role.
Decision: accept.
Plan rows changed: D-042 accepted; RELEASE-1C and RELEASE-READY complete;
  concrete implementation ledger exhausted.
Remaining prerequisite or human review: none for this exact profile. Future
  work begins only from a new request or an already recorded conditional/
  selected-change trigger.
```

### RELEASE-1C validation

Validated on the exact RELEASE-1C worktree diff:

```text
node --require ts-node/register --test
  tests/v3_2_release_completion_tests.ts
  tests/v3_2_release_policy_tests.ts
  tests/v3_2_browser_api_tests.ts
  passed 13 tests / 3 suites with no skips

./scripts/pnpmw run check:conformance
  passed 19 tests / 3 suites with three actual Lambdapi oracle processes,
  no skips, and the outer 60-second bound

node --require ts-node/register --test tests/v3_2_*_tests.ts
  passed 252 tests / 29 suites: 232 passed, 20 opt-in probes skipped

./scripts/pnpmw --dir emdash-template --ignore-workspace exec
  tsc --noEmit -p tsconfig.json
./scripts/pnpmw --dir emdash-template --ignore-workspace exec vite build
  strict TypeScript passed; Vite transformed 48 modules and built the
  production fixture

./scripts/pnpmw run check:ts
  workspace contract, TypeScript, ESLint, and root tests passed
  252 tests / 29 suites: 232 passed, 20 opt-in probes skipped

EMDASH_TYPECHECK_TIMEOUT=60s make -C emdash2 check
  active kernel, extensions, and diagnostics passed

EMDASH_TYPECHECK_TIMEOUT=60s ./scripts/pnpmw run check:all
  root TypeScript gate passed with the same 252-test result
  mandatory conformance passed 19 tests / 3 suites with no skips
  41 active Lambdapi kernel/example files passed
  39 formal infrastructure tests and 5 print registry tests passed
  active-reference/report-header/book/evidence/typography/KaTeX checks passed
  strict rule-LHS audit and generated catalog freshness passed

git diff --check
  passed
```

## Current Dependency State

The user resolved H-01, H-03, H-04, and H-05 on 2026-07-24, and their
dependent slices are complete:

- H-01 approved the recorded dependent-first D-007 recommendation, making
  ELAB-2C dependency-ready; ELAB-2C then completed without finding a displayed
  owner gap or triggering H-02;
- H-03 approved D-023 exactly as proposed, making TSK-1B dependency-ready;
- H-04 approved D-030 exactly as proposed; TSK-2C2 records the narrow reviewed
  boundary while leaving the pre-review artifacts unchanged;
- TSK-2 is complete. All TSK-2 mechanisms consume the reviewed
  `CORE_MVP_MANIFEST`, not the historical TSK-1A proposal;
- TSK-3 is complete for the exact frozen fragment; its historical completion
  record keeps Lambdapi required through H-05, and GRADUATE-1B now retains
  the approved oracle policy beyond that gate;
- MIGRATE-1A closes the source/test inventory and generic proof-inspection
  tranche; MIGRATE-1B closes the contextual Miller-pattern replacement
  tranche; MIGRATE-1C closes the checked, failure-atomic refinement tranche.
  MIGRATE-1D closes the replacement/readiness audit, including the template
  and parser-package edges. MIGRATE-2 deletes the exact frozen graph and
  migrates every consumer/package edge without a compatibility API;
- GRADUATE-1A freezes the D-039 recommendation without authorizing it.
  GRADUATE-1B records the exact approval without rewriting it. RELEASE-READY
  is split; RELEASE-1A completes C-18, RELEASE-1B makes fixed-corpus
  conformance mandatory and synchronizes public policy, and RELEASE-1C closes
  the exact-profile residual/performance/validation boundary.

No concrete dependency-ready slice remains in this plan. RELEASE-READY is
complete for `emdash-v3.2-mvp-1`. KERNEL-DISPLAYED-1/2, H-02, and H-06 remain
conditional future work and require their recorded trigger rather than
continuation by default.

None of these approvals promotes a recorded rule authority class. Do not guess a
displayed-to-ordinary runtime equality, promote the conformance-only owners,
or execute proof-time evidence as a product rule.

## Human Review Gates

Record a concrete recommendation and evidence before requesting review:

| Gate | Earliest trigger | Question |
| --- | --- | --- |
| H-01 | ELAB-2B | Does the dependent-first encoding produce a simpler uniform elaborator than an ordinary-first Core with displayed forms only where needed? |
| H-02 | KERNEL-DISPLAYED-1 probe complete | What are the mathematically correct displayed weakening, exchange, and contraction owners, and which degenerations should compute, unify, or remain theorem-level? |
| H-03 | TSK-1A proposal complete | What exact owner/rule fragment is frozen as the MVP TypeScript kernel? |
| H-04 | TSK-2C | What termination, confluence, subject-reduction, and trusted-rule assumptions may the MVP claim? |
| H-05 | GRADUATE-1A | Approve D-039: make TypeScript the deployed authority for exactly `emdash-v3.2-mvp-1`, with no Lambdapi production dependency, while retaining Lambdapi as mathematical specification, fixed-corpus CI/subject-reduction oracle, and acceptance authority for the five listed semantic-boundary changes? |
| H-06 | after measured need | Is a textual grammar stable and valuable enough to support? |

A human gate blocks only the dependent slice. Record the prerequisite and
continue any independent dependency-ready work instead of guessing the
decision.

Current gate state: H-01, H-03, H-04, and H-05 were approved by the user on
2026-07-24. ELAB-2C completed without triggering H-02, TSK-2 did not broaden
either withheld H-04 claim, and GRADUATE-1B records H-05 without broadening
the frozen profile. H-02 and H-06 remain untriggered future gates.

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
docs/TYPESCRIPT_ELABORATOR_V3_2_FIBRED_CONTEXT_PLAN.md, treating the linked
usability plan as its parent living ledger and this completed master plan as
frozen historical authority for emdash-v3.2-mvp-1.

Treat the usability file as the living active plan and decision ledger:
determine the actual
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

Follow the usability plan's accepted acquisition deferral and categorical
binder architecture. Preserve the completed generic scale infrastructure,
but do not recreate the removed canonical-symbol parser or make bulk
declaration transfer the immediate prerequisite for the runnable dependent
demo and functorial/natural/displayed frontend slices. Preserve completed
USABILITY-2A1's honest locally nameless indexed classifier and
natural/displayed section-eta witness. Preserve the completed,
non-authorizing USABILITY-GRADUATE-1 exact frontend-envelope proposal and its
separate exact
H-DTTLF-USABILITY-GRADUATE/D-DTTLF-USABILITY-002 reviewed approval. Treat the
architecture as settled only for outer LF, ordinary first-order bracket, and
direct-slot indexed section eta. Do not resume bulk transfer from that
approval or confuse its eta-only dependent coverage with general dependent
bracket abstraction, displayed structural completeness, bulk library
transfer, or parser/notation completion. Preserve the subsequent immutable
dependent-binder proposal, its separate exact
H-DTTLF-USABILITY-DEPENDENT/D-DTTLF-USABILITY-003 approval, and completed
generic `Catd_cat` section-composition witness. H-01/D-007 fixes the
dependent-first semantic interpretation and classified constant-family
bridge, not a requirement that ordinary and displayed TypeScript
representations or lowering algorithms be identical or separate. Reuse
shared scoping, dependency, application, or diagnostic machinery where
sound, but judge candidate factorizations by natural, scalable/generalizable,
authority-correct ordinary and displayed behavior. Preserve
USABILITY-DEPENDENT-1A's indexed first-order `FF[k](s[k])` lowering through
generic `comp_fapp0`, its minimal active TypeScript transfer closure, and its
fail-closed/live-conformance evidence. Do not infer general dependent bracket
abstraction, a new Lambdapi mathematical owner/rule, profile promotion,
parser/acquisition selection, or bulk-transfer resumption. Follow the
fibred-context sub-plan's corrected distinction between genuine dependency
edges and independent siblings, its dependency-graph implementation ledger,
its measured transparent-product transport gap, its total-category
pullback non-assumption, its zero-warning-delta two-rule product proposal
approved under D-DTTLF-USABILITY-004, and its asymmetric
pullback-totalization owner proposal approved under D-DTTLF-USABILITY-005.
Preserve the completed FIBRED-COMPREHENSION-1A audited one-owner/two-rule
kernel closure, generic TypeScript transfer, genuine dependent-chain
consumer, further-family reindexing, and runnable demo. Warning comparisons
are diagnostic rather than automatic design vetoes, and every prospective
primitive must first be checked against active kernel constructions and
Foundations. Preserve the completed FIBRED-PRODUCT-1A transparent family,
exact two-rule existing-owner kernel closure, generic five-signature/25-clause
TypeScript transfer, same-base discriminator, and first grouped-sibling
fibre/transport demo. D-DTTLF-USABILITY-006 is approved as proposed and
FIBRED-STRUCTURE-1A is complete after the required existing-owner/Foundation
audit and five-way full-file comparison. Preserve exactly its three
fixed-base displayed projection/pairing owners and eleven
point/full/capped/beta rules, necessary beta guards, generic
six-declaration/15-rule TypeScript transfer, transparent swap/diagonal, and
frontend canonical grouped-product reindexing. The raw whole-pullback
presentation remains non-convertible. Do not add a `Product_catd` head,
kernel reindexing equality, universe-level projection, global `Functord_cat`
product conversion, or infer the measured broader Sigma-introduction action,
profile promotion, parsing/bulk transfer, or a generic total pullback from
that bounded approval. FIBRED-BINDER-1 is now complete at its bounded
existing-authority boundary. Preserve its root-only callback-once direct
`displayedFunctorLambda`, identity/eta/finite-chain lowering, hidden
`k :^n K; a :^f E[k]` evidence, exact reuse of the SCALE-STRESS-2A
Sigma/Pi proof closure, runtime classifier non-conversion, and zero-new-
Lambdapi-mathematics result. FIBRED-TRANSFD-1 is also complete at its
bounded existing-authority boundary. Preserve its six-signature/seven-
runtime-rule/one-proof-rule generic transfer, coherent callback-once
`displayedTransforLambda`, `eta[x]`, `eta[x][u]`, and `eta[p][u]`
consumers, vertical composition, exact direct/ordinary/Sigma-Pi classifier
relations, root-only demo, green 767-test TypeScript and complete repository
gates, and zero-new-kernel-mathematics result. Do not
infer arbitrary pointwise coherence, a general `:^nd` bracket, whole
displayed laxity, or runtime direct/ordinary category collapse.
FIBRED-GROUPED-SEQUENTIAL-1 is complete at an existing-authority boundary.
Preserve its finite two-or-more-sibling dependency-directed API,
accumulated Sigma/pullback and left-associated transparent-product
presentations, checked sequential/grouped objects, stable `Product_pair`
emission, projection/component evidence, three-sibling scaling, and
dependency-edge rejection. It claims no total-category equality/equivalence
and adds no Sigma-projection arrow computation or kernel owner/rule. Its
776-test TypeScript and complete repository gates pass.
FIBRED-QUALIFICATION-REMAINDER-0 is complete and proves the remaining three
corpus cases against existing active authority. FIBRED-WEAKEN-REINDEX-1 is
now fully validated with a root-only successor profile, exact
closed-section `indexOf` weakening, displayed-functor hom-action reindexing,
point computation, direct-eta stability, negative gates, and a runnable demo.
Its transfer contains four existing signatures and six existing runtime
clauses: two explicitly counted source-prior prerequisites and four consumer
clauses. It adds no Lambdapi mathematical owner/rule. Preserve the runtime
object-classifier term join while keeping the category presentations
runtime-distinct and proof-compatible only through the existing
`stress.sigma-pi.uncurrying` rule. Its 785-test TypeScript and complete
repository gates pass, including all 19 live differential judgments, all 41
kernel/example health targets, the unchanged strict `0/47/29` LHS audit, and
catalog freshness.
FIBRED-DEPENDENT-TARGET-1 is now fully validated. Preserve its exact
ten-declaration/ten-runtime/one-proof existing-authority closure, eight-direct/
two-proof subject-validation partition, typed pattern-only `Pi_func`
wildcard, root-only internal-Pi target, eight-clause
`B[k,M] = Pi_cat(G[k],M)` computation, total-context eta, fail-closed
negatives, runnable demo, runtime/proof category non-collapse, and
zero-new-Lambdapi-mathematics result. Its 795-test TypeScript gate,
19-judgment mandatory conformance gate, and complete 41-file kernel CI pass.
Do not infer general `fd`/`nd` completion, arbitrary coherent-section
synthesis, parsing/bulk-transfer authority, or deployed-profile promotion.
FIBRED-GRADUATE-1's frozen root-only executable proposal is approved exactly
as proposed under the user's delegated unattended authority after no
immediate human answer preceded persistent continuation. Its separate
immutable review retains human supersession and records no successor
authority. The approved recommendation treats the dependency-aware
contextual-lowering and qualification-guided generic transfer architecture
as settled and mechanically scalable only for the demonstrated active-v3.2
existing-authority envelope. Its seven
representative closure rows cumulatively exercise 36 declaration, 69
runtime-rule, and three proof-rule slots through generic engines, while
separately recording the four mathematical owners and fifteen mathematical
runtime clauses added by the early product/comprehension/structure work.
These are overlapping slice-entry counts, not unique-library coverage or an
end-to-end throughput benchmark. The proposal keeps direct typed TypeScript
construction as the default, parsing optional, and explicitly withholds
general displayed brackets/coherence, missing arrow/total/groupoidal
mathematics, the remaining 70-root/83-extension closure, final notation,
metatheory, and browser/deployed promotion. The decision adds no semantic
authority and does not automatically select a successor. The proposal's
nine focused tests, root 804-test gate (758 active passes, 46 intentional
skips), unchanged 19-judgment live conformance gate, and complete 41-file
kernel CI all pass. The separate delegated review's nine focused tests, root
813-test gate (767 active passes, 46 intentional skips), and repeated
19-judgment conformance gate also pass. The
FIBRED-STRUCTURE-1A checkpoint remains
`4b532aac9d89ff54b761dd94f49c6eeb4f046b4d`; the synchronized binder
checkpoint is `698280f42c3c9c339ebc82a8cfb0df1d51838704`; the
FIBRED-TRANSFD-1 implementation checkpoint is
`4d26100378fae67ade72ad6c7295d2623fd1fc8f`; the
FIBRED-GROUPED-SEQUENTIAL-1 implementation checkpoint is
`4f173cec9336d41bac9a08563c3697e0fc657d66`; the
FIBRED-WEAKEN-REINDEX-1 implementation checkpoint is
`246481130ebf29a09d04b9b4337dbdb716484d43`; the
FIBRED-DEPENDENT-TARGET-1 implementation checkpoint is
`90b79b8b367f40993f788669b3c7823886111ea2`; the green
FIBRED-GRADUATE-1 proposal checkpoint is
`517e64e67a411412b0300f05f910b8eb25b5f395`; the green delegated-review
checkpoint is `b08c022fcbb8c70ad4349052cbf52a2fdbf77a71`.

The next proposed continuation is
docs/TYPESCRIPT_ELABORATOR_V3_2_DISPLAYED_BRACKET_PLAN.md. Its executable
DISPLAYED-BRACKET-0A proposal selects a generic first-order displayed
contextual compiler and freezes root-only DISPLAYED-BRACKET-1A for finite
independent sibling blocks. H-DTTLF-USABILITY-DISPLAYED-BRACKET-01/
D-DTTLF-USABILITY-009 is approved exactly as proposed by a separate
immutable delegated review with human supersession. The approved
DISPLAYED-BRACKET-1A implementation adds the root-only
`fibred-displayed-bracket-1` profile, one typed-pair construction-IR node,
and a compositional compiler for finite independent displayed sibling
blocks. Projection, exchange, contraction, mapped pairing, three-sibling
scaling, preserved one-slot cases, object/arrow computation, fail-closed
diagnostics, and a compact direct-TypeScript demo are focused-green. It uses
the last green weakening/reindexing transfer and deliberately does not join
the dependent-target profile: that join reproduced a pre-existing
two-closed-functor displayed-composition `TYPE_MISMATCH` and is an explicit
DISPLAYED-LIFTING-0A analysis item. The post-implementation review rejects
another parallel RawExpr/checker layer and confirms that internal bracket
abstraction already recurses through ordinary subexpressions: the exact
`lambda x :^f A. F x y0` witness lowers through identity, composition,
constant abstraction, pairing, and `Eval_func` without local bracket syntax.
The displayed compiler remains restricted to slots, closed displayed
application, and fibre pairs. DISPLAYED-LIFTING-0A was therefore selected as
the next proposal-only typed owner/action matrix; genuine dependency chains
remain a subsequent first-class row. The review also records accurately that
MIGRATE-2 removed the old generic HOAS LF frontend from this branch but did
not discard an earlier recursive categorical bracket implementation. No new
Lambdapi owner/rule, browser surface, parser, or bulk-transfer authority is
added. Genuine dependency chains, general :^nd coherence, Sigma arrow
action, and total-category comparison remain separate. The proposal's eight
focused tests and
821-test gate pass; the separate review's nine focused tests and 830-test
gate pass; all ten implementation/demo tests and the repeated 19-judgment
live conformance gate pass. The exact proposal checkpoint is
`e4b743f70c0454d63a93587dc045a3e2d0273ee5`; the synchronized proposal
ledger is `6ee1b55b395eec4a9a9909afff0f1b0f693312f4`; the delegated-review
checkpoint is `679a380`. The post-review synchronized root gate passes 841
tests (795 active passes, 46
intentional skips), together with the permanent ordinary fixed-evaluation
regression, bounded active-kernel check, and all 19 live conformance
judgments. The exact green local implementation checkpoint is
`d4e0e9bc5ca4dc07dcdfa44e2cb048545f3ee8ab`.

DISPLAYED-LIFTING-0A is now frozen as an executable owner/action matrix. Its
ten focused tests confirm the corrected no-second-RawExpr/checker boundary,
all six implemented ordinary recursive occurrence cases, and the exact
qualified displayed coverage. The audit identifies `Functor_catd`, ordinary
`Eval_func`/`fapp0_func`, and `Product_pair_funcd` as ingredients for open
displayed application but does not falsely claim a selected coherent
displayed evaluator or infer that a new owner is necessary. It proposes only
a separately approved DISPLAYED-EVAL-0B owner-position and
derived-construction probe; semantic DISPLAYED-LIFTING-1A, new owners/rules,
genuine chains, general `:^nd`, parsing/bulk transfer, and browser promotion
remain withheld. Its ten focused tests, the complete 851-test root gate (805
active passes, 46 intentional skips, zero failures), all 19 repeated live
conformance judgments, and the bounded active-kernel check pass. The exact
green proposal checkpoint is
`29f2c5174c96c852f88a7a6ffa84c1ad502f21bd`.

After no immediate human response followed presentation of the exact D-010
gate, H-DTTLF-USABILITY-DISPLAYED-LIFTING-01/
D-DTTLF-USABILITY-010 was approved as proposed under the user's standing
unattended delegation. The separate immutable review retains human
supersession and authorizes only DISPLAYED-EVAL-0B read-only owner-position,
derived-construction, and profile-mismatch evidence. It adds no semantic
DISPLAYED-LIFTING-1A, new owner/rule, grammar/checker case, profile join,
dependent-chain/general-`:^nd` work, parser/acquisition work, deployed
surface, or broader Git authority. Its nine focused tests, full 860-test root
gate (814 active passes, 46 intentional skips, zero failures), and all 19
repeated live conformance judgments pass. The exact review checkpoint is
`7badcd5b930bd098b178d89bf4488637695fb14d`.

DISPLAYED-EVAL-0B is now complete as a read-only executable audit and the
non-self-authorizing DISPLAYED-EVAL-OWNER-0C proposal is frozen. Preserve the
latest usability clarification: `displayedContextLambda`, `apply`, and
`fibrePair` may remain explicit typed TypeScript constructors; the important
property is recursive contextual abstraction beneath supported
subexpressions, not a new RawExpr/parser/checker layer or bracket
punctuation. No previously working categorical abstraction implementation
was discarded during this continuation.

The audit proves that arbitrary `A : Catd(Op K)` cannot also be treated as a
plain covariant argument family over `K`, but that the stable
constant-domain family
`Functor_catd(Const_catd(Op K,A),B)` supports coherent varying and fixed
evaluation. It retains universe-natural evaluation as an alternative and
selects the minimal stable closure only because active authority does not
derive that presentation or arbitrary displayed terminal weakening:
`Eval_funcd`, `Terminal_funcd`, and one `tapp0_fapp0` component rule for
each. Pairing derives both-open evaluation; terminal weakening derives the
fixed case. Global `fapp`/`tapp` remains the sole generic
functoriality/naturality owner.

The dependent-target mismatch is independently localized to a transfer that
returns a declaration checker wired to its prerequisite runtime after
installing a needed rule. The standard final recompilation against the
composed runtime accepts the unchanged term, so the pending proposal includes
one mechanical profile repair and no semantic workaround. Candidate warning
comparison adds exactly two diagnostic unjoinable critical-pair markers and
zero replaceable-pattern-variable markers.

The architecture is therefore settled and implementation-feasible for this
constant-domain displayed-application slice, without claiming arbitrary
mixed-domain evaluation, genuine dependent chains, nested displayed
abstraction, general `:^nd`, or groupoidal completion. Await or separately
review H-DTTLF-USABILITY-DISPLAYED-EVAL-OWNER-01/
D-DTTLF-USABILITY-011 before implementing exactly its two owners, two
component rules, generic transfer, profile repair, and two recursive
existing-IR application judgments. Add no semantic effect before that gate.
The completed audit/proposal evidence is green: 22 focused tests, the full
882-test root gate (836 active passes, 46 intentional skips, zero failures),
all 19 live Lambdapi conformance judgments, and the bounded active-kernel
check pass. The exact audit/proposal checkpoint is
7df9993f06fc55e2f34b09094b87987ef19cecba.

After no immediate human response followed the exact D-011 presentation, the
user's standing unattended delegation approved OWNER-0C through a separate
immutable review retaining human supersession and every frozen non-effect.
It authorizes only DISPLAYED-EVAL-1A's exact two owners, two component rules,
generic transfer, mechanical dependent-target runtime recheck, and two
recursive existing-IR application judgments. Preserve that review once
checkpointed; do not infer arbitrary mixed-domain, chain, `:^nd`, parser,
browser, or broader Git authority. Its ten focused tests, full 892-test root
gate (846 active passes, 46 intentional skips, zero failures), and all 19
live conformance judgments pass.
The exact delegated-review checkpoint is
1251e5c666d2be2ee914d0d122848a259f578da3.

DISPLAYED-EVAL-1A is implemented at the reviewed boundary. It preserves the
existing typed TypeScript construction IR, recursive contextual compiler,
backend-neutral explicit Core, and generic checker; explicit programmatic
`displayedContextLambda`, `apply`, and `fibrePair` constructors are
compatible with the usability goal because variable occurrences recurse
beneath supported typed subexpressions. The active mathematical delta is
exactly `Eval_funcd`, `Terminal_funcd`, and their two point-component rules.
The transfer distinguishes the older TypeScript profile's four
active-authority prerequisites from that delta and adds no intrinsic Core
owner. Varying `F x`, nested `H[e](G[d])`, and fixed `F a` compile, with the
fixed argument derived through terminal weakening. The dependent-target
final-runtime wiring defect is mechanically repaired. This closes neither
arbitrary mixed-domain evaluation nor a genuine dependency chain; its
proposal-only DISPLAYED-CHAIN-0A successor is now frozen and awaits D-012.
Aggregate validation passes 904 TypeScript tests (857 active, 47
intentional skips), 19/19 frozen conformance judgments, all 41 kernel health
targets, and 1,714 classified checks with zero failures.
The exact implementation checkpoint is
1a7ce3f023391aa22c34dc5626057710429bc7c3.

DISPLAYED-CHAIN-0A now gives a bounded answer to the next architectural
question. Sequential Sigma totals are the context layout, repeated
`sigma_map_func`/`sigma_pullback_total_func` is the substitution recursion,
and direct displayed functors are the term representation. A global
unwrapped section-to-displayed runtime rule fails subject reduction; a
stable explicit `sigma_functord_sec` term owner succeeds. Its full-file
candidate adds exactly six object/arrow rules, including the missing Sigma
projection and projection-pullback arrow actions, and computes immediate and
weakened outer variables at both levels. The proposal separates three
existing-signature/two existing-rule transfer prerequisites from that new
semantic delta, records a +8 critical-pair/+0 replaceable-variable warning
delta, and selects a recursive `fibred-displayed-chain-1` consumer without a
new AST, checker, parser, intrinsic Core owner, or total-category
equivalence. Do not implement it before the separate exact
H-DTTLF-USABILITY-DISPLAYED-CHAIN-01/D-DTTLF-USABILITY-012 decision. The
proposal's ten focused tests, root typecheck/lint, bounded active-kernel
check, and aggregate 914-test root gate pass (867 active, 47 intentional
skips, zero failures).

For future exact gates within that active fibred-context goal, the user
permits delegated unattended approval when no immediate human response
follows a presented bounded proposal. Preserve the proposal as
non-self-authorizing, record any delegated approval separately and explicitly,
and proceed only to a coherent green local checkpoint under the existing SOP.
Human responses supersede delegation. This grants no scope broadening,
destructive/external action, remote Git operation, integration, publication,
or history rewriting.
```
