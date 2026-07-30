# TypeScript Elaborator v3.2 — User-Syntax Parity Plan

Date: 2026-07-30
Plan-ID: TS-ELAB-V3.2-SYNTAX-PARITY
Depends-On:
[`TYPESCRIPT_ELABORATOR_V3_2_USER_SYNTAX_PLAN.md`](./TYPESCRIPT_ELABORATOR_V3_2_USER_SYNTAX_PLAN.md),
[`TYPESCRIPT_ELABORATOR_V3_2_INTEGRATED_REVIEWER_PLAN.md`](./TYPESCRIPT_ELABORATOR_V3_2_INTEGRATED_REVIEWER_PLAN.md),
[`TYPESCRIPT_ELABORATOR_V3_2_CATEGORICAL_BINDER_RFC.md`](./TYPESCRIPT_ELABORATOR_V3_2_CATEGORICAL_BINDER_RFC.md),
[`TYPESCRIPT_ELABORATOR_V3_2_DISPLAYED_BRACKET_PLAN.md`](./TYPESCRIPT_ELABORATOR_V3_2_DISPLAYED_BRACKET_PLAN.md),
and
[`TYPESCRIPT_ELABORATOR_V3_2_SCALE_QUALIFICATION_PLAN.md`](./TYPESCRIPT_ELABORATOR_V3_2_SCALE_QUALIFICATION_PLAN.md)
Status: `SYNTAX-PARITY-0A` inventory implemented and focused-green;
`H-DTTLF-PRODUCT-SYNTAX-PARITY-01 /
D-DTTLF-PRODUCT-SYNTAX-PARITY-001` approved as proposed by a separate
immutable unattended review with human supersession; `SYNTAX-PARITY-1A`
is dependency-ready
Selected-Successor:
[`TYPESCRIPT_ELABORATOR_V3_2_BOOK_AND_REPOSITORY_GRADUATION_PLAN.md`](./TYPESCRIPT_ELABORATOR_V3_2_BOOK_AND_REPOSITORY_GRADUATION_PLAN.md)

## Objective And Human Priority

After the integrated reviewer is green, bring the end-user text surface into
measured parity with the mathematical constructions already exposed by the
direct typed TypeScript API. The first audit must prioritize the already
implemented natural, displayed functorial, and displayed natural modes
represented experimentally as `lambda^n`, `lambda^fd`, and `lambda^nd`.
After syntax graduation, the current product goal proceeds to the
reader-facing book/repository graduation plan. Bulk scale qualification stays
pending for a future persistent goal rather than automatically resuming here.

Here and below `lambda^mode` denotes the Unicode or ASCII intrinsic binder
head, such as `λ^nd` or `\^nd`. It does not revive the earlier temporary
notation in which the mode looked like part of a mandatory type annotation.
The domain or family annotation remains separately optional whenever
bidirectional expected information can recover it.

The target of parity is not arbitrary JavaScript syntax and is not every
possible callback program. It is the mathematical construction surface
accepted by the scoped TypeScript categorical programs:

- binders and bound-variable occurrences;
- typed categorical applications and their existing action selection;
- supported ordinary and displayed contextual constructors;
- supported dependent-context presentations; and
- the corresponding explicit-Core/checker/evaluator results and diagnostics.

The audit must make that target finite and testable before proposing a
runtime change.

## Settled Architecture

The text frontend remains an adapter into the existing implementation:

```text
source text
  -> private located name-bearing syntax
  -> immutable name/scope resolution
  -> existing classifier-directed categorical program
  -> existing recursive contextual lowering/factorization
  -> backend-neutral explicit emdash Core
  -> existing checker, conversion, evaluator, and runtime
```

There is no second `RawExpr` dependent type theory, categorical action table,
checker, evaluator, Core, or browser-only semantic implementation.

The current direct TypeScript callback APIs remain useful implementation
boundaries. A text binder resolves a source name to the same scoped token that
the callback receives and then recursively constructs the body through the
same typed program. The parser need not and cannot reproduce arbitrary
JavaScript control flow; parity means that the same supported mathematical
term can be constructed from text.

## Parsing, Elaboration, And Factorization Are Distinct

The implementation may expose one public `elaborate...Text` operation, but
its diagnostics and tests must preserve three conceptual phases.

### 1. Deterministic parsing

The grammar recognizes identifiers, grouping, application, binder heads,
optional annotations, and later selected telescope forms. Parsing is
deterministic and source-located. Parsimmon could express the same grammar,
but the already selected dependency-free recursive-descent implementation
is sufficient; a parser library would not solve the semantic steps below.

Malformed text is a parsing failure. A syntactically valid binder mode can
parse even when the current semantic profile does not yet implement it.

### 2. Typed resolution and application selection

Names resolve through an immutable typed environment. The subject
classifier, argument classifier, binder mode, and bidirectional expected
classifier select the existing `fapp*`, `tapp*`, component, whole-Hom, or
other reviewed action through the current program.

This selection must not be heuristic. If the available typed information does
not determine one supported action, the resolver must either require a
source annotation or reject the expression with an exact ambiguity/
unsupported-shape diagnostic. A conversion budget exhaustion is likewise a
diagnostic, never permission to guess.

### 3. Internal categorical factorization

Some categorical binder bodies must be recursively factored back into genuine
outer functors or transformations. This is a finite structural compilation
over the constructions already supported by the direct TypeScript surface.
It is not general theorem search.

For example, the current displayed-transformation factorer recognizes:

- a component of an already coherent closed `Transfd`; and
- recursively typed vertical composition of such components.

It then returns the corresponding genuine outer transformation. Arbitrary
pointwise data is rejected because component types alone do not construct
naturality. Adding a textual `lambda^nd` route must preserve that exact
invariant.

## Internalization Invariant

The frontend must never request or accept an external naturality square,
functoriality equation, or coherence witness from the user merely to turn
pointwise data into a categorical term. Object action, arrow action, and
higher action must be owned by sufficiently internalized emdash
constructions.

The existing TypeScript name `CoreCategoricalAbstractionEvidence` denotes
immutable lowering/inspection trace data: body IR, result IR, usage,
selected rule, and prerequisites. It is not an external proof premise.
New documentation and APIs should prefer terms such as *abstraction lowering
trace*, *occurrence metadata*, or *factorization trace* when the distinction
matters. A later mechanical rename may be proposed separately; it is not a
semantic prerequisite.

Consequently:

- text resolution may call an existing internally coherent constructor;
- a recursive factorer may recover an outer construction from a reviewed
  finite component grammar;
- unsupported bodies fail closed; and
- general automatic naturality synthesis remains outside the parser and this
  plan.

## Current Measured Starting Point

`src/v3_2/categorical_text.ts` currently owns a private three-node located
tree:

- identifier;
- left-associated whitespace application; and
- one intrinsic-mode lambda with an optional identifier annotation.

Its parser accepts an alphabetic mode suffix. Its resolver currently lowers
only `^f`; `^n`, `^fd`, and `^nd` reach the semantic
`UNSUPPORTED_BINDER_MODE` boundary. Ordinary application delegates
recursively to `CoreCategoricalProgram.apply`, and the root expected action
shape is forwarded only to the root application.

The direct typed surface is substantially wider. Existing reviewed evidence
includes, among other bounded profiles:

- ordinary functorial abstraction with recursive variable occurrence;
- indexed natural section abstraction and section composition;
- independent displayed siblings;
- displayed functor abstraction over identity, eta, finite composition, and
  qualified weakening/reindexing;
- stable displayed evaluation;
- one genuine displayed dependency edge and one mixed
  `a; b,c; d` telescope;
- displayed transformation eta and recursive component composition; and
- a separate displayed-transformation next-Hom/higher-action consumer.

This list is orientation, not the parity inventory. The audit must locate the
actual exported constructors, capability gates, expected classifier data,
profiles, positive tests, and fail-closed boundaries from current code.

## Completed `SYNTAX-PARITY-0A` Result

The executable, deeply frozen audit now lives in
`src/v3_2/categorical_text_parity_audit.ts`, with its focused witnesses in
`tests/v3_2_categorical_text_parity_audit_tests.ts`. It classifies all **68**
public `CoreCategoricalProgram` methods exactly once across **14**
mathematical-capability rows:

| Classification | Rows | Interpretation |
| --- | ---: | --- |
| already text-complete | 1 | Ordinary `lambda`/`^f` already has a checked text route. |
| mechanical syntax route | 1 | The six ordinary structural constructors need only a deterministic structural spelling and direct routing. |
| typed resolver seam | 9 | The direct mathematical operation exists; text needs a finite binding, expected-classifier, or structural-form contract. |
| semantic capability absent | 1 | Arbitrary contexts and general coherence synthesis are not direct-TypeScript capabilities and therefore are not parser work. |
| deliberately non-textual host behavior | 2 | Closed declaration construction and inspection/compilation remain host APIs rather than expression syntax. |

The audit also proves the following boundary without changing runtime
behavior:

- the lexer/parser already accepts the alphabetic intrinsic modes `^n`,
  `^fd`, and `^nd`;
- each currently reaches the exact resolver-side
  `UNSUPPORTED_BINDER_MODE` boundary;
- the corresponding direct `dependentLambda`,
  `displayedFunctorLambda`, and `displayedTransforLambda` operations execute
  under their reviewed profiles;
- recursive displayed-cell composition executes through the existing
  `composeCells` owner; and
- `CoreCategoricalProgram.apply` remains the one classifier-directed
  application ladder. The text frontend does not acquire a second action
  table.

The 68-method inventory is intentionally broader than the first
implementation tranche. It separates the already available single-binder
semantics from later dependent-context and explicit-constructor presentation
work rather than making “parity” an open-ended claim.

## Proposed Gate `H-DTTLF-PRODUCT-SYNTAX-PARITY-01`

Decision `D-DTTLF-PRODUCT-SYNTAX-PARITY-001` proposes
`SYNTAX-PARITY-1A`, the smallest dependency-closed product slice:

- enable intrinsic modes `n`, `fd`, and `nd`;
- route only to `dependentLambda`, `displayedFunctorLambda`,
  `displayedTransforLambda`, `composeCells`, and the existing `apply`;
- add a `displayed-family` environment binding kind and expected result kinds
  for dependent sections, displayed functors, and displayed
  transformations;
- recognize the fixed binary application spine
  `composeCells left right` and route it to the existing direct method; and
- preserve the direct finite factorization grammars and exact fail-closed
  behavior.

The exact positive witnesses are:

```text
λ^n  k : K. (FF k) (s k)
λ^fd a : E. GG (FF a)
λ^nd k : K. composeCells (theta k) (eta k)
```

The proposal must reject wrong annotations/profiles/endpoints,
non-adjacent cell composition, pointwise data that is not internally
factorable, and nested or multi-binder forms deferred to
`SYNTAX-PARITY-1B`. Text and direct TypeScript must produce equal explicit
Core and equal abstraction/factorization observations. Node and browser must
use the same adapter.

This proposal adds no mathematical owner, Core node, checker/evaluator
branch, external coherence evidence, Lambdapi declaration/rule, or second
semantic frontend. Its executable object reports zero semantic delta and is
non-self-authorizing. The separate immutable
[`D-DTTLF-PRODUCT-SYNTAX-PARITY-001` review](./TYPESCRIPT_ELABORATOR_V3_2_SYNTAX_PARITY_D001_REVIEW.md)
now approves the exact frozen scope under the user's standing unattended
delegation, with any later explicit human decision superseding it.

After `1A`, the measured continuation is:

1. `SYNTAX-PARITY-1B` — nested/dependent contexts and displayed/fibred
   structural forms;
2. `SYNTAX-PARITY-1C` — the remaining selected mathematical constructor
   spellings; and
3. `SYNTAX-PARITY-GRADUATE-1` — freeze the exact text/direct-TypeScript
   parity envelope and route to the book/repository graduation plan.

## SYNTAX-PARITY-0A — Dependency-Ready Inventory And Design Audit

After the integrated-reviewer checkpoint, inspect every public or
product-relevant direct TypeScript categorical construction and record one
row per mathematical capability:

1. owning module and method;
2. required profile/capability;
3. input classifier and expected classifier;
4. scoped bindings introduced;
5. ordinary/displayed dependency and variance;
6. object-, arrow-, and higher-action ownership;
7. recursive body grammar already accepted by the direct implementation;
8. proposed text spelling;
9. whether the existing located tree is sufficient;
10. whether resolution is a mechanical route into an existing method;
11. exact positive equivalence witness against direct TypeScript; and
12. exact negative, ambiguity, or unsupported-shape witness.

Classify each row as exactly one of:

- **already text-complete** — current syntax and resolver cover it;
- **mechanical syntax route** — existing semantics need only grammar,
  environment, expected-classifier, or method routing;
- **typed resolver seam** — the semantic construction exists, but the current
  callback-only API needs a small parser-independent expected/scoping
  contract before text can call it cleanly;
- **semantic capability absent** — direct TypeScript itself does not yet
  support the construction, so this is not parser work; or
- **deliberately non-textual host behavior** — arbitrary JavaScript behavior
  with no mathematical syntax-parity obligation.

The audit must pay special attention to:

- `^n`, `^fd`, and `^nd` binders;
- nested binders and dependent telescope family resolution;
- optional annotations versus intrinsic binder modes;
- ordinary and displayed application at object and arrow levels;
- whole-Hom and higher-action expected routing;
- reindexing, weakening, pairing, and dependent-context constructors;
- contravariant positions; and
- exact factorization failure for pointwise-but-not-internalizable bodies.

The output is an executable/deeply frozen inventory plus a bounded
implementation proposal. The audit may add tests and proposal data but must
not add grammar or runtime behavior before a separate review.

## Expected Feasibility

The syntax portion is high-confidence and largely mechanical:

- the parser already reads arbitrary alphabetic intrinsic modes;
- binder tokens already provide hygienic scoped occurrences;
- direct constructors already prove the semantic lowering;
- application already enters one classifier-directed program; and
- every located node can retain exact source spans.

The remaining work is not expected to require a new kernel or frontend
architecture. The main engineering work is to expose enough typed expected
information to the resolver, recursively resolve dependent annotations under
earlier binders, and map each bounded callback construction to a deterministic
text form.

The audit may nevertheless find a real semantic absence. If so, it must
classify that row as absent and route it to the relevant usability/kernel
plan rather than hiding it in parser logic. One specifically required scale
owner may move earlier only through the existing measured, separately
reviewed selective-scale policy.

## Proposed Graduation Evidence

A later syntax-parity implementation is not complete merely because new
strings parse. For every promoted row it must demonstrate:

- source text and direct TypeScript compile to equal explicit Core;
- inferred and expected classifiers agree;
- object/arrow/higher observations match the direct capability where
  applicable;
- recursive occurrence and nested subexpression behavior are covered;
- unsupported modes, profiles, families, variances, and pointwise coherence
  fail at exact spans;
- browser and root entry points use the same text adapter;
- no external naturality evidence is accepted;
- no Node, parser-dependency, Lambdapi-source, or checker/Core semantic delta
  occurs unless separately proposed; and
- focused, aggregate, browser, and proportional Lambdapi conformance gates
  pass.

## Work Ledger

| Row | Status | Depends on | Deliverable |
| --- | --- | --- | --- |
| SYNTAX-PARITY-0A | **complete; focused-green** | REVIEWER-INTEGRATE-1A and current direct TypeScript surface | Executable/deeply frozen 68-method/14-capability inventory, classification, direct semantic witnesses, exact negative boundary, and bounded proposal |
| H-DTTLF-PRODUCT-SYNTAX-PARITY-01 / D-DTTLF-PRODUCT-SYNTAX-PARITY-001 | **approved as proposed; immutable unattended review with human supersession** | SYNTAX-PARITY-0A and checkpoint `d73195b` | Review permits only the frozen `SYNTAX-PARITY-1A` three-mode/application/cell-composition scope |
| SYNTAX-PARITY-1A | **dependency-ready** | approved D001 review | Implement only `^n`, `^fd`, `^nd`, the frozen binding/expected contracts, existing direct-builder routes, tests, browser exposure, and documentation |
| SYNTAX-PARITY-1B | gated | `SYNTAX-PARITY-1A` plus separate exact review | Nested/dependent contexts and displayed/fibred structural forms |
| SYNTAX-PARITY-1C | gated | `SYNTAX-PARITY-1B` plus separate exact review | Remaining selected mathematical constructor spellings and routes |
| SYNTAX-PARITY-GRADUATE-1 | gated | completed reviewed parity rows | Freeze exact text/direct-TypeScript parity and residual semantic rather than parser gaps |
| SELECTIVE-SYNTAX-SCALE-* | conditional, none selected | a measured parity row requiring one missing active owner plus separate review | Promote only a named dependency required by a compelling text/reviewer witness |
| BOOK-DELTA-0A | selected successor after syntax graduation | SYNTAX-PARITY-GRADUATE-1 | Route to the book/repository plan’s capability-oriented delta audit; do not turn syntax implementation history into book prose |

## Explicit Non-Authorization

This plan currently authorizes no:

- new mathematical owner, runtime rule, proof rule, unification rule, Core
  node, checker/evaluator branch, or semantic profile;
- arbitrary pointwise-to-functor or pointwise-to-transformation promotion;
- external naturality/coherence witness API;
- heuristic action selection or theorem search;
- second parser, exported raw syntax type theory, checker, evaluator, or
  categorical action table;
- parser dependency or lockfile change;
- claim that every JavaScript callback has a textual equivalent;
- final repository-wide Lambdapi/TypeScript notation migration;
- Lambdapi-source acquisition parser;
- bulk transfer, groupoidal closure, book prose/artifact mutation, deployment,
  or publication; or
- push, merge, PR, release, rebase, amend, reset, history rewrite, cleanup,
  branch deletion, or worktree removal.

## Git And Persistent-Goal Boundary

This plan inherits
[`PERSISTENT_GOAL_GIT_EXPERIMENTATION.md`](./PERSISTENT_GOAL_GIT_EXPERIMENTATION.md).
Existing authority permits bounded green local checkpoints only in the
dedicated goal branch/worktree after synchronized ledgers, exact staged-diff
review, and `git diff --cached --check`.

## Persistent `/goal` Launch Prompt

```text
Continue the next dependency-ready reviewed row routed by
docs/TYPESCRIPT_ELABORATOR_V3_2_SYNTAX_PARITY_PLAN.md, with
docs/TYPESCRIPT_ELABORATOR_V3_2_BOOK_AND_REPOSITORY_GRADUATION_PLAN.md as the
selected post-syntax product route,
docs/TYPESCRIPT_ELABORATOR_V3_2_SCALE_QUALIFICATION_PLAN.md retained as the
future architecture-qualification ledger, and
docs/TYPESCRIPT_ELABORATOR_V3_2_HANDOFF.md as the recovery entry.

Recover current code/tests, all worktrees and ancestry, staged and unstaged
state, active authorities, and living decision ledgers before acting.
Preserve the integrated reviewer and all completed semantic checkpoints.

Treat parity as parity with mathematical constructions exposed by the direct
typed TypeScript API, not arbitrary JavaScript callback behavior. Keep
parsing deterministic, use immutable scoped resolution and existing
classifier-directed programs, and distinguish parsing, typed elaboration,
and internal categorical factorization. Never guess an application action or
promote arbitrary pointwise data to coherent categorical data.

Recover the completed executable SYNTAX-PARITY-0A inventory and continue only
the next separately reviewed row in its ledger. The exact
H-DTTLF-PRODUCT-SYNTAX-PARITY-01 /
D-DTTLF-PRODUCT-SYNTAX-PARITY-001 review is recorded with human
supersession; implement only its frozen `SYNTAX-PARITY-1A` scope. A missing
direct semantic capability belongs in the relevant usability/kernel plan,
not in parser heuristics.

After exact syntax graduation, route to the capability-delta and
reader-narrative rows in the book/repository graduation plan. Keep bulk
WalkingEnd/HIT, batch, and whole-transfer graduation pending for a future
goal unless one exact dependency is required by the selected reader-facing
example and separately reviewed.

Existing Git authority permits only bounded green local checkpoints in the
dedicated goal worktree after synchronized ledgers and exact staged-diff
review. Do not push, merge, publish, deploy, release, amend, rebase, reset,
rewrite history, delete branches/worktrees, or perform unrelated cleanup.
```

## Change Log

- **2026-07-30 — D001 separately approved under unattended delegation.**
  After no immediate human objection to the checkpointed proposal, recorded
  an immutable, human-supersedable review approving only the three existing
  single-binder modes, the existing application ladder, and direct
  `composeCells` routing. Nested/dependent contexts and remaining structural
  syntax stay outside `SYNTAX-PARITY-1A`.
- **2026-07-30 — `SYNTAX-PARITY-0A` completed and first gate frozen.**
  Classified all 68 public categorical-program methods exactly once in 14
  executable capability rows. Confirmed that `^n`, `^fd`, and `^nd` already
  parse and fail only at the semantic mode boundary, while their direct
  internalized builders and recursive cell composition are green. Proposed
  the bounded, non-self-authorizing `SYNTAX-PARITY-1A` modes-first slice and
  separated later context/constructor parity into `1B` and `1C`.
- **2026-07-30 — Book/repository graduation selected after syntax parity.**
  The current product goal now proceeds from exact text/direct-TypeScript
  parity to a capability-oriented, theorem-led book update and consolidated
  repository introduction. Bulk scale rows remain pending in their ledger
  for a future goal rather than automatically resuming after this plan.
- **2026-07-30 — Syntax parity selected as the next product-facing task.**
  Recorded the user's clarification that the desired post-reviewer task is to
  synchronize text with the mathematical constructions already exposed by
  the direct TypeScript API, especially existing `^n`, `^fd`, and `^nd`
  capabilities, before deferred bulk scale work.
- **2026-07-30 — Parsing and internalization boundary clarified.** Parsing is
  deterministic; syntactically valid input may later fail typed resolution
  or internal factorization. Application selection uses classifiers and
  expected information rather than heuristics. Existing abstraction
  “evidence” is lowering trace metadata, not an external naturality premise,
  and general coherence theorem synthesis remains outside the parser.
