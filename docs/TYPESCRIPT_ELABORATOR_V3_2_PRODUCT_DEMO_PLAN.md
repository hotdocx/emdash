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
supersession; PRODUCT-DEMO-1B is dependency-ready

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

The root package already exposes sixteen direct-TypeScript demo commands:

1. the outer-LF directed dependent Sigma-telescope demo;
2. ordinary categorical bracket abstraction;
3. closed indexed dependent eta and composition;
4. fibred comprehension, products, and structural pairing;
5. direct displayed functor and transfor binders;
6. grouped sequential contexts, weakening, and reindexing;
7. dependent displayed targets;
8. displayed evaluation and displayed brackets;
9. one genuine displayed dependency chain; and
10. displayed-transfor higher action.

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
  -> promote at most one reviewed browser/parser implementation subplan
  -> PRODUCT-GRADUATE-1
  -> return to SCALE-STRESS-3C / SCALE-BATCH-1 / SCALE-GRADUATE-1
```

Browser and parser audits may run in either order after PRODUCT-DEMO-1B.
Neither implementation is silently selected by this plan.

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

## Later Bounded Rows

| Row | Status | Depends on | Deliverable |
| --- | --- | --- | --- |
| PRODUCT-DEMO-0A | complete | current code and history | Existing demo/API/browser/parser inventory and feasibility verdict recorded above |
| PRODUCT-DEMO-1A | approved exactly as proposed under D-DTTLF-PRODUCT-DEMO-001 with human supersession; proposal checkpoint `e786c61` | PRODUCT-DEMO-0A | Deeply frozen three-panel external-review implementation contract |
| PRODUCT-DEMO-1B | dependency-ready | approved PRODUCT-DEMO-1A | Root-only report module, command, reviewer guide, tests, and synchronized navigation |
| PRODUCT-DEMO-ORACLE-0A | pending | PRODUCT-DEMO-1B | Decide whether one bounded optional conformance command materially improves peer review without making Lambdapi a runtime dependency |
| PRODUCT-BROWSER-0A | pending | PRODUCT-DEMO-1B | Measure transitive browser safety, bundle/worker/startup boundary, exact public facade, and minimal UI options; produce a separate implementation proposal only if justified |
| PRODUCT-BROWSER-1 | gated/deferred | approved browser proposal | Implement only the selected browser profile and UI; likely deserves a dedicated subplan |
| PRODUCT-SYNTAX-0A | pending | PRODUCT-DEMO-1B | Compare direct TypeScript, historical Parsimmon grammar, tagged-template, and small located-syntax adapters against the existing contextual compiler; freeze mode/application and diagnostic boundaries |
| PRODUCT-SYNTAX-1 | gated/deferred | approved syntax proposal | Implement only the selected user-facing syntax adapter; likely deserves a dedicated subplan |
| PRODUCT-GRADUATE-1 | pending | required product rows | External-review handoff, exact runnable capability envelope, remaining product risks, and route back to scale qualification |

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
