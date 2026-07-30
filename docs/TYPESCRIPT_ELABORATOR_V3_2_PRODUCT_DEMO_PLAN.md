# TypeScript Elaborator v3.2 — Product Demo And External Review Plan

Date: 2026-07-29
Plan-ID: TS-ELAB-V3.2-PRODUCT-DEMO
Depends-On:
[`TYPESCRIPT_ELABORATOR_V3_2_HANDOFF.md`](./TYPESCRIPT_ELABORATOR_V3_2_HANDOFF.md),
[`TYPESCRIPT_ELABORATOR_V3_2_SCALE_QUALIFICATION_PLAN.md`](./TYPESCRIPT_ELABORATOR_V3_2_SCALE_QUALIFICATION_PLAN.md),
[`TYPESCRIPT_ELABORATOR_V3_2_USABILITY_PLAN.md`](./TYPESCRIPT_ELABORATOR_V3_2_USABILITY_PLAN.md),
and
[`TYPESCRIPT_ELABORATOR_V3_2_FIBRED_CONTEXT_PLAN.md`](./TYPESCRIPT_ELABORATOR_V3_2_FIBRED_CONTEXT_PLAN.md)
Supersedes: no completed profile, mathematical authority, scale row,
usability result, or browser boundary
Status: active living product-facing continuation; inventory
PRODUCT-DEMO-0A is complete; the exact PRODUCT-DEMO-1A implementation
proposal is separately approved under D-DTTLF-PRODUCT-DEMO-001 with human
supersession; PRODUCT-DEMO-1B is implemented and final-green at exact local
checkpoint `f1cb532a88ccca84786aa1cd5ee7cb006b1ad5fc`;
PRODUCT-DEMO-ORACLE-0A, PRODUCT-BROWSER-0A, and PRODUCT-SYNTAX-0A are
complete; the dedicated browser plan freezes BROWSER-DIRECTED-1A as the next
product implementation, records its exact separate
D-DTTLF-PRODUCT-BROWSER-001 review with human supersession, and now records
that slice final-green; the dedicated user-syntax plan now freezes
H-DTTLF-PRODUCT-SYNTAX-01 / D-DTTLF-PRODUCT-SYNTAX-001 as the next exact
contract, completes the disposable parser comparison, and freezes
H-DTTLF-PRODUCT-SYNTAX-02 / D-DTTLF-PRODUCT-SYNTAX-002 as the next exact
implementation proposal, now separately approved with human supersession;
direct human correction H-DTTLF-PRODUCT-SYNTAX-03 /
D-DTTLF-PRODUCT-SYNTAX-003 separates intrinsic `λ^mode` capability from an
optional checked `: annotation`, and the corrected SYNTAX-1A implementation
is final-green at exact local checkpoint
`7513cbe9e0d1439b5b1250982f40cede48e9a811`; PRODUCT-GRADUATE-1 is the
dependency-ready bounded documentation/handoff row, now approved exactly as
proposed under D-DTTLF-PRODUCT-GRADUATE-001 with human supersession

## Human Direction And Purpose

The user asked whether the remaining scale rows were the highest-yield next
work, or whether a polished external-reviewer demonstration, a narrow
user-facing parser, or a browser demonstration would better expose the
substantial functionality already implemented. The user also recalled that
the original TypeScript/emdash v1 used Parsimmon and directed that its Git
history may be used as design evidence.

This plan inserts a bounded product-facing continuation before the remaining
WalkingEnd/HIT stress, bulk-batch, and final scale-graduation rows. It does
not cancel those rows or convert demonstration evidence into a
whole-development transfer claim. Its purpose is to make the already checked
outer dependent LF and categorical/directed-DTT usability envelope easy for
an external reviewer to run, understand, and inspect before more
architecture-qualification work is accumulated.

The intended meaning of *usability* remains substantive:

- users can bind variables and use them recursively within supported typed
  subexpressions;
- contextual occurrence information selects and composes the required
  categorical structural operations and object/arrow/higher application
  forms;
- displayed dependency, reindexing, and internalized arrow action remain
  visible to the checker rather than being erased by presentation sugar; and
- explicit TypeScript constructors such as
  `displayedDependentContextLambda`, `apply`, and `fibrePair` are acceptable
  end-user inputs.

String tokenization, a prettier spelling, and a browser shell may expose this
capability, but they do not define or replace it.

## Authority And Architectural Boundary

The active Lambdapi v3.2 development remains the mathematical authority.
The TypeScript product path remains:

```text
direct typed TypeScript construction
  -> existing recursive contextual elaboration
  -> backend-neutral explicit emdash Core
  -> existing generic LF checker/evaluator/rewrite/proof engines
  -> deterministic inspection output
  -> optional bounded Lambdapi conformance oracle
```

This continuation must not introduce a second semantic checker, a
category-owner-specific expression evaluator, or a production Lambdapi
dependency. A later string parser, if selected, is only an input adapter to
the same elaboration and Core path. It is not the deferred generic
Lambdapi-source acquisition parser.

The frozen browser entry point remains
[`src/v3_2/browser.ts`](../src/v3_2/browser.ts). It currently exports only the
reviewed minimal Core product surface and deliberately excludes the
root-only directed and categorical continuation modules. Browser promotion
therefore requires a separate packaging/API review even if no mathematical
change is involved.

## PRODUCT-DEMO-0A — Completed Read-Only Inventory

### Existing executable surface

The root package now exposes eighteen direct-TypeScript or typed-text demo
commands: seventeen individual capability commands plus the composed
external-review report.

1. the outer-LF directed dependent Sigma-telescope demo;
2. ordinary categorical bracket abstraction;
3. closed indexed dependent eta and composition;
4. fibred comprehension, products, and structural pairing;
5. direct displayed functor and transfor binders;
6. grouped sequential contexts, weakening, and reindexing;
7. dependent displayed targets;
8. displayed evaluation and displayed brackets;
9. one genuine displayed dependency chain; and
10. displayed-transfor higher action; plus
11. the narrow ordinary categorical text adapter.

The demo wrappers are small. Their implementation modules already return
deeply structured results and separate `run...Demo` from
`format...Demo`. They are therefore reusable product components rather than
throwaway console scripts.

The most representative current commands are:

| Command | End-user evidence | Current boundary |
| --- | --- | --- |
| `demo:directed-dependent` | outer lambda/Pi checking, a dependent Sigma-telescope section application, explicit Core, inferred and reduced types, beta plus kernel computation, and a wrong-family diagnostic | root-only opt-in outer LF/directed profile |
| `demo:categorical-bracket` | `λ x :^f A`, recursive pointwise application, diagonal, exchange, structural basis, explicit Core, and a wrong-category diagnostic | ordinary categorical bracket envelope |
| `demo:categorical-displayed-chain` | `λ a :^fd A. λ b :^fd B(a)`, outer/inner/recursive occurrences, object and internalized-arrow observations, reindexing, and a wrong-base diagnostic | one genuine dependency edge; bounded depth |
| `demo:categorical-displayed-nd-higher` | object action, whole-Hom action, and a higher cell `H[m]` through the existing `tdapp1_int_*_transfd` package | advanced direct consumer; not a general `:^nd` binder |
| `demo:categorical-text` | `λ^f x. (H x) (K x)`, optional checked annotation, recursive silent application, exact explicit Core equivalence, whole-Hom expected routing, and a source-located diagnostic | ordinary `^f` only; experimental TypeScript spelling, not a general parser or final notation |

Observed local `ts-node` wall times for individual runs were approximately
23 seconds, 25 seconds, 41 seconds, and a variable 28–91 seconds
respectively. These are orientation measurements, not a performance
benchmark or SLA. They show that a coherent default report should avoid
making the variable higher-action lane its only entry point.

### Existing browser boundary

[`src/v3_2/browser.ts`](../src/v3_2/browser.ts) exports the Core checker,
session, kernel constructors, serializer, manifest, and associated types. It
does not export the directed/categorical programs or demos and imports no
filesystem/process-backed oracle. Consequently:

- a root CLI external-review demo is low-risk and immediately feasible;
- a browser bundle is not merely a different formatter;
- promotion must audit transitive browser safety, bundle size/startup,
  stable public API, and which exact profile is being exposed.

### Historical TypeScript v1 parser

Commit `6cb146364dfdaa299e95d3aa72a33da78e64c5e7` contains the 162-line
`src/parser.ts` Parsimmon frontend with package dependency
`parsimmon@^1.18.1`. It supports:

- `let`;
- lambda spellings `\` and `fun`;
- explicit and implicit typed binder groups;
- Pi and right-associated arrow syntax;
- left-associated explicit/implicit application;
- `Type`, variables, holes, and parentheses; and
- recursively rebuilt parsers carrying the in-scope binder-name list.

That source is useful evidence for grammar organization, combinator
feasibility, whitespace handling, binder lists, and diagnostics. Its named
HOAS `Term`, `replaceFreeVar`, mutable `globalDefs`, and global fresh-hole
state are retired and are not a v3.2 storage or checking authority.

The migration intentionally removed Parsimmon and records the root parser
replacement as not implemented. Reintroduction is therefore a reviewed
product decision, not restoration of an accidentally omitted dependency.

## Current Feasibility And Priority Assessment

| Work | Feasibility now | Direct user value | Architectural value | Recommended priority |
| --- | --- | --- | --- | --- |
| Curated external-review CLI and guide | high; mostly composition of green modules | high | medium; exposes actual boundaries | first |
| Browser-boundary audit | high and bounded | medium | high for packaging decision | after CLI |
| Browser implementation | likely medium; exact cost unknown until audit | high | medium | gated |
| User-syntax/parser audit | high and bounded | medium | high for correct frontend boundary | after CLI |
| User-facing parser implementation | medium; tokenization is easy, integration and mode-directed application are the real work | high | medium | gated |
| SCALE-STRESS-3C WalkingEnd/HIT | medium and semantically diverse | low immediate | high | resume after product checkpoint |
| SCALE-BATCH-1 | deterministic only after constituent mechanisms; labor-heavy | low immediate | high | later scale proof |
| SCALE-GRADUATE-1 | cheap only after required evidence exists | medium | high | final scale row |

The product-facing continuation is not evidence that the last three scale
rows are unnecessary. It is evidence that more declarations are not required
to demonstrate the first genuinely useful system.

## Selected Product Sequence

```text
PRODUCT-DEMO-0A inventory
  -> PRODUCT-DEMO-1A exact proposal/review
  -> PRODUCT-DEMO-1B external-review CLI + guide
  -> PRODUCT-DEMO-ORACLE-0A optional-oracle assessment
  -> PRODUCT-BROWSER-0A measured browser audit
  -> PRODUCT-SYNTAX-0A measured user-syntax audit
  -> BROWSER-DIRECTED-1A exact review/implementation (complete)
  -> SYNTAX-RESOLVE-0B exact parser-independent contract proposal
  -> disposable parser comparison (complete; tiny parser selected)
  -> H-DTTLF-PRODUCT-SYNTAX-02 / separate implementation review
  -> parser + located nodes + resolver + example as one vertical slice
  -> PRODUCT-GRADUATE-1
  -> return to SCALE-STRESS-3C / SCALE-BATCH-1 / SCALE-GRADUATE-1
```

Browser and parser audits may run in either order after PRODUCT-DEMO-1B.
The completed measurements select only the additive directed browser proposal
as the immediate product implementation. They do not silently select a
categorical browser profile, parser dependency, or syntax implementation.

## PRODUCT-DEMO-1A — Approved External-Reviewer Proposal

Gate:
`H-DTTLF-PRODUCT-DEMO-01 / D-DTTLF-PRODUCT-DEMO-001`

Separate review:
[`TYPESCRIPT_ELABORATOR_V3_2_PRODUCT_DEMO_D001_REVIEW.md`](./TYPESCRIPT_ELABORATOR_V3_2_PRODUCT_DEMO_D001_REVIEW.md),
approved as proposed under the user's standing unattended delegation with
human supersession after the proposal checkpoint `e786c61`.

### Proposed implementation

Add one root-only product-review module, one tiny executable wrapper, one
package command, a self-contained reviewer guide, and focused deterministic
tests. Export the structured report from the root v3.2 barrel, but do not
change the browser barrel.

The default report has three panels:

1. **Outer dependent LF.** Reuse the existing directed-dependent result to
   show the direct TypeScript input, explicit locally nameless Core, inferred
   and reduced dependent type, exact reduction trace, and wrong-family
   diagnostic.
2. **Ordinary functorial binding.** Reuse the categorical-bracket result to
   show `λ x :^f A. (H x) (K x)`, diagonal/exchange structural lowering,
   object/arrow-sensitive application classification, and wrong-category
   diagnostic.
3. **Displayed dependent binding.** Reuse the displayed-chain result to show
   `λ a :^fd A. λ b :^fd B(a). ...`, recursive occurrence below one genuine
   dependency edge, object and internalized-arrow computation, reindexing,
   noncollapse, and wrong-base diagnostic.

The report must state, in one place:

- the input API;
- the elaboration/checking pipeline;
- which mathematical owners/rules are reused;
- that production invokes no Lambdapi process;
- that a string parser is not required;
- the exact supported usability envelope; and
- the exact deferrals: arbitrary telescope depth, general `:^nd`, browser
  promotion, user-facing parsing, groupoidal closure, and whole-library
  transfer graduation.

The existing `demo:categorical-displayed-nd-higher` command is linked as an
optional advanced fourth witness. It is not executed by the default report
unless implementation measurement proves that doing so has acceptable and
deterministic cost.

### Exact expected file scope

- `src/v3_2/product_review_demo.ts`;
- `src/v3_2/index.ts`;
- `examples/v3_2_product_review_demo.ts`;
- `tests/v3_2_product_review_demo_tests.ts`;
- `tests/main_tests.ts`;
- `package.json`;
- `README.md`;
- `docs/TYPESCRIPT_ELABORATOR_V3_2_EXTERNAL_REVIEW_DEMO.md`; and
- synchronized entries in this plan, the handoff, and the scale ledger.

No lockfile, dependency, Lambdapi source, browser entry point, generic
checker/evaluator, transfer engine, categorical elaborator, or mathematical
owner/rule change is authorized.

### Acceptance

1. `./scripts/pnpmw run demo:external-review` succeeds from the repository
   root without Lambdapi.
2. Its output is deterministic apart from explicitly excluded timing.
3. It presents the three panels as one coherent story rather than merely
   concatenating three existing verbose console dumps.
4. Each panel derives its claims from the existing structured demo result;
   it does not maintain a second hand-written semantic result.
5. At least one explicit Core term, one inferred/reduced type, one runtime
   trace, one structural lowering, one displayed object result, one
   internalized-arrow/noncollapse result, and one source-located negative
   diagnostic are visible.
6. The reviewer guide gives exact commands for the default report, the full
   existing component reports, the optional higher-action witness, the
   TypeScript-only gate, and bounded Lambdapi conformance.
7. Focused tests cover deep immutability or stable readonly structure,
   formatter determinism, exact panel selection, boundary/deferral truth,
   browser non-export, and production-Lambdapi non-use.
8. Root typecheck, lint, focused tests, and the aggregate TypeScript gate
   pass. Existing expensive conformance is rerun only in proportion to
   affected boundaries; no Lambdapi semantic file changes are expected.
9. Local wall-time observations are recorded without claiming an SLA.

### Decision requested

Approve
`H-DTTLF-PRODUCT-DEMO-01 / D-DTTLF-PRODUCT-DEMO-001`
as proposed: compose the exact three-panel root-only external-review report
and guide from existing green structured demos, retain the higher-action
witness as optional unless measured cheap, add no semantic or browser/parser
change, and preserve every listed deferral.

## PRODUCT-DEMO-1B — Implementation Record

PRODUCT-DEMO-1B implements exactly D-DTTLF-PRODUCT-DEMO-001:

- `src/v3_2/product_review_demo.ts` composes the existing structured
  directed-dependent, ordinary bracket, and displayed-chain results;
- `examples/v3_2_product_review_demo.ts` and
  `demo:external-review` expose one root command;
- the formatter presents one coherent report rather than concatenating the
  three verbose component formatters;
- the root barrel exports the report, while `src/v3_2/browser.ts` remains
  unchanged;
- the external-review guide gives the default, full-component, optional
  higher-action, TypeScript validation, and bounded Lambdapi-oracle commands;
  and
- focused tests fail closed on component-boundary drift and verify exact
  panel selection, readonly report structure, deterministic formatting, zero
  semantic effect, browser exclusion, and no process oracle.

Observed validation:

- focused PRODUCT-DEMO-1B: 5/5 tests pass;
- actual `demo:external-review`: pass, 68.59-second local cold CLI
  observation;
- aggregate `check:ts`: 1,109 tests, 1,058 active passes, 51 intentional
  skips, zero failures, 1,155,579 ms;
- bounded `EMDASH_TYPECHECK_TIMEOUT=60s make -C emdash2 check`: pass; and
- browser entry point, lockfile, Lambdapi sources, owners/rules, checker,
  evaluator, transfer engines, contextual elaborators, and dependencies:
  zero delta.

The aggregate process reused warmed component modules and recorded the
product report's three-panel execution at 2.1 seconds. These two timings are
orientation evidence only; no performance SLA is claimed. The slower
displayed next-hom/higher-action command remains optional.

Exact local implementation checkpoint:
`f1cb532a88ccca84786aa1cd5ee7cb006b1ad5fc`.

## Later Bounded Rows

| Row | Status | Depends on | Deliverable |
| --- | --- | --- | --- |
| PRODUCT-DEMO-0A | complete | current code and history | Existing demo/API/browser/parser inventory and feasibility verdict recorded above |
| PRODUCT-DEMO-1A | approved exactly as proposed under D-DTTLF-PRODUCT-DEMO-001 with human supersession; proposal checkpoint `e786c61` | PRODUCT-DEMO-0A | Deeply frozen three-panel external-review implementation contract |
| PRODUCT-DEMO-1B | complete and final-green at `f1cb532a88ccca84786aa1cd5ee7cb006b1ad5fc` | approved PRODUCT-DEMO-1A | Root-only three-panel report module, command, reviewer guide, tests, and synchronized navigation with zero semantic/browser/parser delta |
| PRODUCT-DEMO-ORACLE-0A | complete; no new command selected | PRODUCT-DEMO-1B | Reuse the documented `check:conformance`, directed conformance, displayed-evaluation conformance, and bounded kernel commands. A new umbrella command would either duplicate them or misstate displayed-chain coverage; production remains Lambdapi-free |
| PRODUCT-BROWSER-0A | complete; routed to dedicated browser plan | PRODUCT-DEMO-1B | The directed dependent closure is Node-free and Vite/Chromium-green; the full report reaches `node:crypto` through acquisition/audit modules. Frozen additive BROWSER-DIRECTED-1A and deferred categorical runtime-spec separation are recorded in [`TYPESCRIPT_ELABORATOR_V3_2_BROWSER_DEMO_PLAN.md`](./TYPESCRIPT_ELABORATOR_V3_2_BROWSER_DEMO_PLAN.md) |
| PRODUCT-BROWSER-1 | complete and final-green at `7f696cea4b6a369e5db41c0d5e57e778b61fa10c` | D-DTTLF-PRODUCT-BROWSER-001 | Additive directed browser entry, fixed dependent-LF plus preserved minimal-Core views, Node-free/static project-subpath build, real-browser evidence, and no semantic/dependency delta |
| PRODUCT-SYNTAX-0A | complete; routed to dedicated syntax plan | PRODUCT-DEMO-1B | The existing scoped LF/categorical programs remain the semantic boundary. A small located name-bearing tree, immutable typed environment, expected-classifier seam, recursive resolution, and exact spans are specified in [`TYPESCRIPT_ELABORATOR_V3_2_USER_SYNTAX_PLAN.md`](./TYPESCRIPT_ELABORATOR_V3_2_USER_SYNTAX_PLAN.md); the measured comparison selected the tiny dependency-free parser |
| PRODUCT-SYNTAX-1 | complete and final-green at `7513cbe9e0d1439b5b1250982f40cede48e9a811`; contract approved under D-DTTLF-PRODUCT-SYNTAX-001; integrated slice approved under D-DTTLF-PRODUCT-SYNTAX-002 with human supersession; intrinsic-mode/optional-annotation correction recorded directly under D-DTTLF-PRODUCT-SYNTAX-003 | SYNTAX-RESOLVE-0B, parser review, and notation correction | Tiny dependency-free parser, private located nodes, recursive ordinary resolver, tests, command, and example landed together; other modes and final notation remain deferred |
| PRODUCT-GRADUATE-1 | approved exactly as proposed under D-DTTLF-PRODUCT-GRADUATE-001 with human supersession; implementation active; proposal checkpoint `76e7e11` | completed selected browser and syntax rows | External-review handoff, exact runnable capability envelope, remaining product risks, and route back to scale qualification |

## PRODUCT-DEMO-ORACLE-0A Completion

The external-review guide already names the truthful optional authority
commands:

- the nineteen-judgment MVP conformance command;
- directed-continuation conformance;
- categorical displayed-evaluation conformance; and
- the bounded active-kernel check.

The product report installs no new semantics. There is no dedicated live
displayed-chain oracle command whose coverage could be truthfully relabeled as
the whole three-panel report. Adding an umbrella script now would therefore
either repeat existing commands without improving evidence, or overstate the
oracle boundary. ORACLE-0A selects documentation reuse and zero package-script
delta. Lambdapi remains an optional development/conformance authority, never
a browser or production runtime dependency.

## User-Syntax Audit Questions

PRODUCT-SYNTAX-0A must answer these before selecting a parser library:

1. What is the smallest located syntax representation that preserves free
   variable occurrence, binder modes `:^o`, `:^f`, `:^n`, `:^fd`, and
   `:^nd`, explicit annotations, and application sites without becoming a
   second typed Core?
2. Can it elaborate recursively through the existing
   `CoreCategoricalProgram` and contextual compilers, or is one reusable
   surface-resolution seam missing?
3. How are silent applications classified among outer LF application,
   `fapp0`/`fapp1`, `tapp0`/`tapp1`, and displayed/higher variants from
   expected and inferred classifier information?
4. How are expressions such as
   `λ x :^f A. F x y0`, where abstraction remains functorial after
   evaluation at a constant inner argument, represented and lowered?
5. Which dependent and contravariant cases require annotations, and which
   are genuinely ambiguous rather than merely unimplemented?
6. Can parser diagnostics preserve source spans into the existing normalized
   categorical diagnostics?
7. Does Parsimmon remain the best small dependency, or would a tagged
   template or tiny hand-written parser provide a smaller browser and
   maintenance boundary?

These audit questions preserve the informal `x :^mode A` notation in which
they were originally posed. D-DTTLF-PRODUCT-SYNTAX-003 later corrected the
experimental TypeScript text surface to intrinsic `λ^mode x` plus a separate
optional `: A`. That correction is deliberately not a bulk rewrite or final
standardization of Lambdapi/kernel development notation.

Possible designs must be recorded even if one is selected:

- direct typed TypeScript only;
- a located user-syntax tree plus the existing elaborator;
- a tagged-template adapter; and
- a Parsimmon-style string parser producing that same located syntax.

The audit must reject a second independent typechecker and must not conflate
user syntax with generic Lambdapi-source acquisition.

## Browser Audit Questions

PRODUCT-BROWSER-0A must determine:

1. whether the selected root continuation graph is transitively browser-safe;
2. whether costly catalog construction/checking should run on the main
   thread, a worker, or a precompiled immutable artifact;
3. whether the browser exposes only the external-review report, an editable
   direct-TypeScript-like builder playground, or later parsed user syntax;
4. which exact profile identity and owner/rule boundary it advertises;
5. whether current startup cost is acceptable before any UI work; and
6. how browser tests preserve the no-process/no-filesystem/no-production-
   Lambdapi boundary.

This audit may produce a dedicated
`TYPESCRIPT_ELABORATOR_V3_2_BROWSER_DEMO_PLAN.md`; it does not pre-authorize
one.

Both audits are now complete. Their detailed measurements and staged
architectures are recorded in:

- [`TYPESCRIPT_ELABORATOR_V3_2_BROWSER_DEMO_PLAN.md`](./TYPESCRIPT_ELABORATOR_V3_2_BROWSER_DEMO_PLAN.md);
  and
- [`TYPESCRIPT_ELABORATOR_V3_2_USER_SYNTAX_PLAN.md`](./TYPESCRIPT_ELABORATOR_V3_2_USER_SYNTAX_PLAN.md).

The browser audit proves an immediate, Node-free directed-dependent browser
slice and diagnoses categorical bundle failure as runtime/acquisition
layering. The syntax audit confirms that text needs only a small located
syntax plus recursive resolution into the existing programs; it does not
justify a second checker or select Parsimmon merely from historical use.

## PRODUCT-GRADUATE-1 — Frozen Product Handoff Proposal

Gate:
`H-DTTLF-PRODUCT-GRADUATE-01 /
D-DTTLF-PRODUCT-GRADUATE-001`

This is a bounded documentation and routing row. It adds no runtime feature.
The proposal may only:

1. update
   [`TYPESCRIPT_ELABORATOR_V3_2_EXTERNAL_REVIEW_DEMO.md`](./TYPESCRIPT_ELABORATOR_V3_2_EXTERNAL_REVIEW_DEMO.md)
   into the current self-contained product-capability handoff;
2. retain `demo:external-review` as the curated direct-TypeScript
   outer-LF/ordinary/displayed report;
3. add `demo:categorical-text` as the editable ordinary categorical input
   lane, showing both inferred and explicit source annotations;
4. add `check:browser-directed` as the existing fully client-side directed
   dependent-LF plus minimal-Core browser lane;
5. distinguish executable TypeScript text syntax from informal historical
   Lambdapi/kernel binder notation;
6. publish one exact command/capability/limitation matrix;
7. record the green checkpoints and current validation counts; and
8. route the persistent product continuation back to SCALE-STRESS-3C,
   SCALE-BATCH-1, and SCALE-GRADUATE-1.

The handoff must say plainly:

- direct typed TypeScript remains the most complete input surface;
- the text adapter currently lowers only ordinary `^f`, with `^n`, `^fd`, and
  `^nd` fail-closed;
- displayed/dependent text telescopes are not implemented even though their
  direct typed TypeScript consumers are executable;
- the intrinsic `λ^mode` plus optional `: annotation` spelling is an
  experimental TypeScript decision, not final cross-environment notation;
- the browser currently exposes the directed-dependent witness and preserved
  minimal Core playground, not the categorical text adapter;
- categorical browser promotion still requires
  BROWSER-CATEGORICAL-0A runtime-boundary separation and a later review;
- no GitHub Pages workflow or publication is present;
- production invokes no Lambdapi process; and
- product demonstration does not graduate whole-library mechanical transfer,
  arbitrary displayed depth, groupoidal closure, confluence, unrestricted
  normalization, or standalone subject reduction.

Acceptance is documentation-specific and bounded:

- every named command and linked source file exists;
- the new text examples match the final-green SYNTAX-1A tests/demo;
- the selected browser claim matches the final-green additive browser plan;
- current aggregate counts and checkpoints are exact;
- README, handoff, product, syntax, browser, and scale navigation agree;
- `git diff --check` and `git diff --cached --check` pass; and
- the exact staged diff changes documentation only.

### Exact non-authorization

The proposal authorizes no parser or semantic expansion, browser entry or UI,
runtime-boundary refactor, dependency/lock change, checker/evaluator/Core/
action-table change, Lambdapi source or process change, deployment/workflow/
publication, scale result, or remote/broad Git operation.

## Scale Relationship

This plan changes priority, not truth:

- SCALE-INDUCTIVE-HYBRID-0A already shows that checked generated owners can
  enter as ordinary explicit symbols and rules;
- the frozen SCALE-INDUCTIVE-1B2 decision remains independently pending;
- SCALE-STRESS-3C remains necessary to qualify the selected
  WalkingEnd/dependent-eliminator/higher-action/HIT mechanism class;
- SCALE-BATCH-1 remains necessary to support a throughput/repetition claim;
  and
- SCALE-GRADUATE-1 remains necessary for the final mechanical-transfer
  envelope.

The product demo may expose existing higher-action or induction evidence, but
it cannot close those rows by presentation.

## Git And Persistent-Goal Boundary

This plan inherits
[`PERSISTENT_GOAL_GIT_EXPERIMENTATION.md`](./PERSISTENT_GOAL_GIT_EXPERIMENTATION.md)
and the scale plan's exact checkpoint authority. On the dedicated
`goal/typescript-elaborator-v3.2` branch/worktree, local checkpoints are
authorized only after a bounded tranche is green, affected ledgers and
navigation are synchronized, the exact staged diff contains no unrelated
work, and `git diff --cached --check` passes.

No push, merge, PR, publication, release, new branch/worktree, rebase, amend,
reset, history rewrite, branch/worktree deletion, or unrelated cleanup is
authorized.

## Persistent `/goal` Launch Prompt

```text
Kick off or continue the current dependency-ready work routed by
docs/TYPESCRIPT_ELABORATOR_V3_2_PRODUCT_DEMO_PLAN.md, with
docs/TYPESCRIPT_ELABORATOR_V3_2_SCALE_QUALIFICATION_PLAN.md retained as the
top-level architecture-qualification ledger and
docs/TYPESCRIPT_ELABORATOR_V3_2_HANDOFF.md as the recovery entry point.

Treat the living plans and their Persistent /goal Launch Prompts as part of
the objective. Recover actual state from active code and tests, all
worktrees, staged and unstaged changes, branch ancestry, current authorities,
and the decision/side-task ledgers. Follow root AGENTS.md and the nested
emdash2 SOP for every Lambdapi action.

Follow the next dependency-ready reviewed row rather than a stale prompt
snapshot. Prioritize a truthful external-reviewer experience for the already
implemented outer dependent LF and ordinary/displayed categorical usability
envelope. Preserve the single existing checker/evaluator and backend-neutral
explicit Core. Direct typed TypeScript remains a valid primary input.
String parsing is an optional user-input adapter, not a second checker and
not Lambdapi-source acquisition. Browser promotion requires its own measured
boundary. Do not promote parser or browser implementation before the living
plan's bounded audit and exact review select one.

Preserve completed usability, displayed-chain, higher-action, LF-sort, and
inductive audit checkpoints. Preserve every pending decision as pending
unless its exact separate review is obtained or validly recorded. A product
demo does not close WalkingEnd/HIT, batch-transfer, or scale-graduation rows.
Return to the scale ledger when the product plan routes back to it.

For a narrowly frozen dependency-ready proposal, the user's standing
delegation permits a separate immutable unattended approval only after no
immediate human response, with human supersession and the Git checkpoint SOP.
It does not authorize an unfrozen or broadened implementation.

Existing authority permits only bounded green local checkpoint commits in
the dedicated goal worktree after synchronized ledgers and exact staged-diff
review. Do not push, merge, publish, release, amend, rebase, reset, rewrite
history, delete branches/worktrees, or perform unrelated cleanup.
```

## Change Log

- **2026-07-29 — D-DTTLF-PRODUCT-GRADUATE-001 recorded.** After no immediate
  objection to checkpoint `76e7e11`, applied the user's standing unattended
  delegation with human supersession to the exact documentation-only product
  handoff. It authorizes no runtime, parser, browser, dependency, Lambdapi,
  deployment, scale-result, or broader Git change.
- **2026-07-29 — H-DTTLF-PRODUCT-GRADUATE-01 frozen.** With the selected
  external-review, directed-browser, and ordinary categorical-text rows
  final-green, proposed one documentation-only graduation that consolidates
  their runnable command matrix and exact limitations, then routes back to
  the remaining scale qualification. It changes no runtime or product
  behavior and is not self-authorizing.
- **2026-07-29 — PRODUCT-DEMO-0A completed and PRODUCT-DEMO-1A proposed.**
  Inventoried sixteen current root demos, the minimal browser barrel, and the
  historical Parsimmon frontend. Selected a three-panel external-review CLI
  and guide as the highest-yield next implementation, retained the variable-
  cost higher-action demo as an optional advanced witness, and separated
  browser and user-syntax work into measured gates. No semantic, dependency,
  browser, parser, or Git mutation was made by the inventory.
- **2026-07-29 — D-DTTLF-PRODUCT-DEMO-001 recorded with human
  supersession.** After no immediate objection to checkpoint `e786c61`, a
  separate immutable decision record approves only the exact three-panel
  root-only PRODUCT-DEMO-1B report/guide/test scope under the user's standing
  unattended delegation. It authorizes no semantic, parser, browser,
  dependency, Lambdapi, or broader Git change.
- **2026-07-29 — PRODUCT-DEMO-1B implemented and final-green.** Added one
  root-only three-panel structured report, CLI command, reviewer guide, and
  five focused tests. The actual command and 1,109-test aggregate gate pass,
  as does the bounded active-kernel check. The browser, parser/dependencies,
  Lambdapi sources, generic engines, elaborators, and mathematical
  owners/rules are unchanged. Exact green local checkpoint:
  `f1cb532a88ccca84786aa1cd5ee7cb006b1ad5fc`.
- **2026-07-29 — Product audits completed and split into dedicated plans.**
  ORACLE-0A selects the already documented optional conformance commands
  rather than a misleading umbrella. BROWSER-0A proves the directed demo
  Vite/Chromium-green and finds the categorical report's `node:crypto`
  reachability in acquisition/audit layering. SYNTAX-0A specifies a
  parser-independent located syntax and recursive resolver into the existing
  LF/categorical programs, retaining the historical Parsimmon source only as
  grammar evidence. The additive directed browser proposal is next; no
  categorical browser, parser dependency, or syntax implementation is
  silently authorized.
- **2026-07-29 — Additive directed browser slice completed.** The dedicated
  browser plan now records the unchanged frozen minimal entry, additive
  directed-dependent entry, two-view Vite fixture, relative static assets for
  a likely `/emdash/` GitHub Pages path, 75-module production build, clean
  Chromium execution, and the 1,114-test aggregate. Sandpack is not a
  requirement; no workflow/publication, backend, categorical browser,
  parser, dependency, or semantic change was made. The parser-independent
  SYNTAX-RESOLVE-0B contract is the next proposal boundary. Exact green local
  checkpoint: `7f696cea4b6a369e5db41c0d5e57e778b61fa10c`.
- **2026-07-29 — SYNTAX-RESOLVE-0B exact contract frozen.** The dedicated
  syntax plan now proposes H-DTTLF-PRODUCT-SYNTAX-01 /
  D-DTTLF-PRODUCT-SYNTAX-001 for a narrow ordinary categorical grammar,
  request-local typed environment, explicit expected routing, recursive
  application resolution, and exact spans. It also corrects the sequencing:
  disposable parser comparison comes first, then a separately reviewed
  parser, located nodes, resolver, tests, and example land together. No
  parser/dependency, code, browser, semantics, or Lambdapi change is part of
  this proposal.
- **2026-07-29 — Parser comparison completed.** Disposable Parsimmon and
  tiny recursive-descent parsers accepted/rejected the same frozen corpus and
  both Vite-built. The tiny parser trades more local source for zero
  dependency/typing/lock impact, an 856-byte gzip bundle rather than 7,094
  bytes, and direct stable-diagnostic ownership. The dedicated syntax plan
  freezes H-DTTLF-PRODUCT-SYNTAX-02 / D-DTTLF-PRODUCT-SYNTAX-002 for one
  integrated parser/resolver/example slice. No production code is yet
  authorized.
- **2026-07-29 — D-DTTLF-PRODUCT-SYNTAX-003 direct correction recorded.**
  Before the syntax implementation checkpoint, the user separated intrinsic
  abstraction capability (`λ^f`, `λ^n`, `λ^fd`, `λ^nd`) from the optional
  `: domain/family` annotation. The ordinary text resolver now recovers an
  omitted source from its required expected classifier and checks an explicit
  source. Deferred modes remain fail-closed, and final TypeScript/Lambdapi
  notation consolidation remains a later design gate.
- **2026-07-29 — Corrected PRODUCT-SYNTAX-1 final-green.** Added the narrow
  ordinary categorical text command and adapter through the existing typed
  program. Thirteen focused tests, the actual demo, typecheck/lint, the
  1,127-test aggregate, and bounded active Lambdapi check pass. No
  dependency/lock, checker/evaluator/Core/action-table, browser, or Lambdapi
  delta occurred. Exact local implementation checkpoint:
  `7513cbe9e0d1439b5b1250982f40cede48e9a811`.
