# TypeScript Elaborator v3.2 — Compact Contextual `:^nd` Text Parity

Date: 2026-08-02

Plan-ID: TS-ELAB-V3.2-CONTEXTUAL-ND-TEXT-PARITY

Depends-On:
[`TYPESCRIPT_ELABORATOR_V3_2_MIXED_INTRODUCTION_PUBLIC_CONTINUATION_PLAN.md`](./TYPESCRIPT_ELABORATOR_V3_2_MIXED_INTRODUCTION_PUBLIC_CONTINUATION_PLAN.md),
[`TYPESCRIPT_ELABORATOR_V3_2_SYNTAX_PARITY_PLAN.md`](./TYPESCRIPT_ELABORATOR_V3_2_SYNTAX_PARITY_PLAN.md),
and
[`TYPESCRIPT_ELABORATOR_V3_2_CATEGORICAL_BINDER_RFC.md`](./TYPESCRIPT_ELABORATOR_V3_2_CATEGORICAL_BINDER_RFC.md)

Status: active living syntax successor;
`HOM-CATD-ACTION-TRANSFER-GRADUATE-0AG` is read-only complete with zero
semantic delta; `CONTEXTUAL-ND-TEXT-PARITY-0AH` is executable and read-only
complete; the exact `CONTEXTUAL-ND-TEXT-PARITY-1AI` proposal frozen below
under H-DTTLF-USABILITY-CONTEXTUAL-ND-TEXT-PARITY-01 /
D-DTTLF-USABILITY-065 is separately reviewed-approved from immutable proposal
checkpoint `a4ee654d8e025df6962ea92f219819430852f51a` under the standing
unattended delegation, with immediate human supersession. The bounded
implementation audit then found one proposal-bookkeeping omission before any
behavior edit: nine existing tests pin the categorical-text revision literal,
while D-065 item 7 requires synchronizing them and its exact file list omitted
them. The zero-behavior
`CONTEXTUAL-ND-TEXT-REVISION-CORRECTION-1AI1` proposal below is separately
reviewed-approved under D-DTTLF-USABILITY-066 from immutable proposal
checkpoint `bb485375f6c843adc6c3b80755b1eb11e9cdbf0a`; D-065 implementation is
implemented and focused-green. Its synchronized semantic checkpoint is
pending in the current bounded commit; the read-only 0AJ graduation audit is
the next dependency-ready row.

## Objective

Bring the existing categorical text adapter into exact parity with the
already-implemented compact contextual displayed-natural binder, without
adding another parser, checker, action table, or coherence mechanism.

The direct mathematical API now distinguishes two useful presentations of a
whole displayed transformation:

```text
base-component presentation
  displayedTransforLambda(k => eta[k])

compact contextual presentation
  displayedTransforContextLambda(a => eta[a])
```

The first callback exposes the base object `k`. The second internally tracks
the expanded telescope

```text
k :^n K; a :^n E[k]
```

and exposes only the fibre object `a`. The compact route recursively factors
point eta, generic identity, vertical composition, and fixed-head pre- and
postwhiskering into genuine closed `Transfd` owners. Text parity must expose
that already-checked route while preserving the historical base-component
route.

## Settled Architecture

The parser remains a deterministic adapter:

```text
text
  -> private located syntax
  -> expected-contract-directed name/scope resolution
  -> existing CoreCategoricalProgram method
  -> existing recursive contextual factorer
  -> explicit Core/checker/evaluator/runtime
```

The text layer must not synthesize naturality, inspect Core terms to invent a
classifier, or duplicate the direct factorer. Syntactic parsing may succeed
before expected-contract resolution or internal factorization fails; that is
the existing fail-closed phase separation, not a parser defect.

Binder mode remains intrinsic to the binder head:

```text
lambda^nd a : E. body
```

The family annotation is optional when the selected expected contract already
supplies `E`. The annotation is not the binder mode. Because the historical
base-component presentation also uses `^nd`, the checked expected contract—not
a lexical heuristic—must select which direct program method receives the
callback.

## Inherited Semantic Evidence

The semantic predecessor has already checked a fixed alternating target:

```text
T0 = Transf_catd(A0,B0,alpha0,beta0)
H0 = Hom_catd(T0,x0,y0)
T1 = Transf_catd(A1,H0,alpha1,beta1)
D  = Hom_catd(T1,x1,y1).
```

For `P,Q,R : Functord E D`, direct TypeScript accepts:

```text
lambda^nd a. eta[a]
lambda^nd a. id(P[a])
lambda^nd a. theta[a] o eta[a]
lambda^nd a. M(eta[a])
lambda^nd a. eta[L[a]].
```

Every result is a whole internally coherent `Transfd`. The transferred
`Hom_catd` action also computes through all four alternating classifier heads.
No parser change may broaden that exact semantic envelope.

## Measured Starting Boundary

The graduated text adapter currently has one
`displayed-transfor` expected contract. Its resolver:

- interprets the optional `^nd` annotation as a base category;
- calls `CoreCategoricalProgram.displayedTransforLambda`;
- exposes a base-object token to the body;
- routes neutral application and `composeCells`; and
- already preserves direct/text equality for eta and recursive whole-fibre
  component composition.

The newer direct compact API is not selected by that contract. In particular:

- its optional annotation should denote the source displayed family;
- its callback token is an indexed fibre object rather than a base object;
- `identityCell(endpoint)` has no dedicated text resolver head; and
- neutral application must be measured for contextual eta and both
  whiskering orientations rather than assumed from the direct tests.

This is an expected-contract/resolver parity gap, not a new grammar, kernel,
Core, checker, evaluator, or mathematical-construction gap.

## Work Ledger

| Slice | Status | Dependency | Exact boundary |
|---|---|---|---|
| `HOM-CATD-ACTION-TRANSFER-GRADUATE-0AG` | complete read-only; zero semantic delta | final-green D-062 through D-064 | Fixed alternating Hom/Transf targets and their generic action work; no `Transf_catd_func` consumer was found. |
| `CONTEXTUAL-ND-TEXT-PARITY-0AH` | executable read-only audit complete; zero behavior delta | completed 0AG; graduated historical syntax parity; direct D-055 through D-058; one disposable focused probe | Neutral application already handles compact eta and both whiskers, `composeCells` already recurses, and the direct factorer remains the coherence gate. Current text fails at exactly the expected-contract/family-annotation distinction (`EXPECTED_CATEGORY`) and absent `identityCell` resolver head (`UNKNOWN_IDENTIFIER`). The historical base-component route remains green. |
| `CONTEXTUAL-ND-TEXT-PARITY-1AI` | implemented and focused-green under D-DTTLF-USABILITY-065; semantic checkpoint pending in the synchronized commit | completed 0AH; immutable proposal checkpoint `a4ee654d8e025df6962ea92f219819430852f51a`; separate D-065 review; approved D-066 correction; 14/14 affected parity and 24/24 nearest direct regressions | One expected-contract kind selects the existing compact program method and one fixed `identityCell` resolver head delegates to the existing program operation. Eta and both whiskers remain neutral applications, composition remains `composeCells`, and the direct factorer remains the sole coherence gate. Historical `^nd` is unchanged. |
| `CONTEXTUAL-ND-TEXT-REVISION-CORRECTION-1AI1` | implemented with zero behavior delta under D-DTTLF-USABILITY-066; checkpoint shared with 1AI | approved D-065 item 7; immutable proposal checkpoint `bb485375f6c843adc6c3b80755b1eb11e9cdbf0a`; separate D-066 review; exact revision search | Only the old revision literal changed in the nine already-existing pin assertions omitted from D-065's file list. No import, test logic, behavior, runner, or validation boundary changed. |
| `CONTEXTUAL-ND-TEXT-PARITY-GRADUATE-0AJ` | dependency-ready read-only graduation | final-green conditional 1AI/1AI1 | Re-audit the exact direct/text envelope and select the next semantic or reader-facing continuation without claiming unrestricted `:^nd`. |

## `CONTEXTUAL-ND-TEXT-PARITY-0AH` Audit Contract

The audit must answer these questions from executable evidence:

1. Can one additive expected-contract kind select
   `displayedTransforContextLambda` without changing the historical
   `displayed-transfor` contract?
2. Can the resolver validate an optional displayed-family annotation through
   the existing `compareDisplayedFamilies` route?
3. Does existing neutral application already lower exact contextual eta,
   prewhiskering, and postwhiskering when the callback token is an indexed
   fibre object?
4. Is one fixed-arity `identityCell` resolver route sufficient for contextual
   identity, with the existing direct factorer remaining the sole coherence
   gate?
5. Does existing `composeCells` recursively route contextual point
   composition without a second resolver tree?
6. Do mismatched families, endpoints, orientation, arbitrary point arrows,
   missing expectations, and foreign terms still fail closed through existing
   diagnostics?
7. Does one fixed alternating `Transf`/`Hom` target use the same route with no
   classifier-specific parser case?

The audit may use disposable ignored probes and focused existing tests. It may
edit documentation and freeze a proposal, but it may not change production or
test behavior until a separate immutable review approves that proposal.

## `CONTEXTUAL-ND-TEXT-PARITY-0AH` Audit Result

The disposable executable audit is green for every direct compact body using
ordinary neutral `program.apply` calls—no resolver-specific expected-shape
hint was needed:

```text
eta[a]
id(P[a])
theta[a] o eta[a]
M(eta[a])
eta[L[a]].
```

The recovered abstraction rules are respectively eta, identity, composition,
postwhiskering, and prewhiskering. Eta and identity compare with their closed
owners, and composition compares with generic whole-`Transfd` composition.
This proves that text resolution can reuse the ordinary application resolver,
existing `composeCells`, and the direct contextual factorer; it needs no
application-action table or coherence branch.

The same probe measured the current text boundary exactly:

```text
lambda^nd k : K. eta k
  -> categorical.displayed-transfor-eta

lambda^nd a : E. eta a
  -> EXPECTED_CATEGORY

lambda^nd a. identityCell (P a)
  -> UNKNOWN_IDENTIFIER
```

Here `lambda^nd` is the plan's ASCII rendering of the parser's accepted
Unicode `λ^nd` or ASCII `\^nd` spelling. The first result confirms that the
historical base-component route is healthy. The second fails because that
route interprets the annotation as a category rather than a displayed family.
The third isolates the only missing constructor spelling; neutral eta,
composition, and whiskering require no new head.

The probe was deleted after recording the result. No tracked behavior changed,
and the unrelated temporary experiment directories were untouched.

## Frozen `CONTEXTUAL-ND-TEXT-PARITY-1AI` Proposal

### H-DTTLF-USABILITY-CONTEXTUAL-ND-TEXT-PARITY-01 /
### D-DTTLF-USABILITY-065

Approve exactly this TypeScript-only adapter slice:

1. Extend `CoreCategoricalTextTermExpected` with one additive
   `displayed-context-transfor` contract carrying the checked source displayed
   family and the two existing displayed-functor endpoint terms.
2. Keep the historical `displayed-transfor` contract and
   `resolveDisplayedTransforLambda` unchanged. The expected-contract kind—not
   the `^nd` token or an annotation heuristic—selects the compact route.
3. Add one `resolveDisplayedContextTransforLambda` method. It validates an
   optional annotation with the existing displayed-family comparison and
   calls the existing
   `CoreCategoricalProgram.displayedTransforContextLambda` exactly once.
4. Resolve the callback body through the existing lexical environment and
   ordinary recursive `resolveLambdaBody`; do not add another located syntax
   node, parser production, scope engine, or callback evaluator.
5. Add exactly one fixed-arity `identityCell` application route beside the
   existing `composeCells` route. It resolves one ordinary term argument and
   delegates to the existing `CoreCategoricalProgram.identityCell` method.
6. Leave eta, prewhiskering, and postwhiskering on generic neutral
   application. Leave recursive vertical composition on the existing
   `composeCells` route. Add no contextual special case for any of them.
7. Bump only the categorical-text revision to
   `CONTEXTUAL-ND-TEXT-PARITY-1AI-CATEGORICAL-TEXT-1` and synchronize exact
   revision assertions.
8. Extend the existing categorical-text parity corpus rather than adding a
   new root-runner entry. Check direct/text equality for eta, identity,
   recursive composition, prewhiskering, and postwhiskering, with both omitted
   and correct optional family annotation where meaningful.
9. Include one fixed alternating `Transf_catd`/`Hom_catd` target to prove that
   the resolver does not branch on classifier head. Reuse the 0AG semantic
   envelope; do not add a `Transf_catd` text constructor or action case.
10. Retain exact negative evidence for a wrong annotation kind, mismatched
    family annotation, incompatible endpoints/orientation, unsupported
    arbitrary point arrows, missing/wrong expected contract, and the existing
    historical base-component `^nd` route.
11. Change no Lambdapi source, transfer declaration/rule, Core node, generic
    checker/conversion/evaluator/runtime, categorical-program method, browser
    preset, public report, book, README, package, workspace, or root test
    runner.
12. Validate proportionally: the affected text-parity file, nearest direct
    contextual eta/identity/composition/whiskering tests, root typecheck and
    lint, whitespace, and exact diff. Carry forward the recent qualified
    aggregate because none of its owning boundaries changes.

The implementation file boundary is exactly:

```text
src/v3_2/categorical_text.ts
tests/v3_2_categorical_text_parity_tests.ts
```

plus synchronized plan/handoff documentation. If implementation discovers a
need for a program method, Core/checker/runtime case, classifier decomposition,
or constructor-specific coherence logic, stop and return to a corrected
proposal rather than broadening D-DTTLF-USABILITY-065.

The decision question is:

> Approve H-DTTLF-USABILITY-CONTEXTUAL-ND-TEXT-PARITY-01 /
> D-DTTLF-USABILITY-065 as proposed: preserve the historical base-component
> `^nd` route, add one expected-contract-selected compact contextual route and
> one `identityCell` resolver head, reuse neutral application,
> `composeCells`, and the existing direct factorer for all semantics, and add
> only the exact focused parity/negative evidence above?

## Frozen Revision-Pin File-List Correction

### H-DTTLF-USABILITY-CONTEXTUAL-ND-TEXT-REVISION-CORRECTION-01 /
### D-DTTLF-USABILITY-066

The pre-implementation search required by D-065 found nine existing tests
whose sole relevant assertion is:

```text
CORE_CATEGORICAL_TEXT_REVISION
  === TEXT-PARITY-RECURSIVE-MIXED-1-CATEGORICAL-TEXT-1.
```

D-065 item 7 already requires changing the production constant and
synchronizing exact revision assertions, but the proposal's later “exact
implementation file boundary” omitted these nine files. That contradiction
must be corrected before implementation.

Approve exactly this zero-behavior correction:

1. Add these nine existing files to D-065's mechanical synchronization
   boundary:

   ```text
   tests/v3_2_categorical_displayed_telescope_generic_tests.ts
   tests/v3_2_categorical_text_constructor_tests.ts
   tests/v3_2_categorical_text_displayed_constructor_tests.ts
   tests/v3_2_categorical_text_graduation_audit_tests.ts
   tests/v3_2_categorical_text_internal_action_audit_tests.ts
   tests/v3_2_categorical_text_internal_action_tests.ts
   tests/v3_2_categorical_text_nested_ordinary_tests.ts
   tests/v3_2_categorical_text_recursive_mixed_tests.ts
   tests/v3_2_categorical_text_result_constructor_audit_tests.ts
   ```
2. In each file, replace only the old expected revision string with
   `CONTEXTUAL-ND-TEXT-PARITY-1AI-CATEGORICAL-TEXT-1`.
3. Change no import, assertion structure, test logic, fixture, snapshot,
   runtime expectation, or root-runner wiring.
4. Validate the synchronization by an exact repository search proving that no
   assertion retains the superseded revision, plus the D-065 focused suite,
   root typecheck/lint, and whitespace. Do not run nine expensive suites merely
   to re-evaluate an exact string replacement, and do not run the long
   aggregate.
5. Resume D-065 unchanged after a separate immutable review. This correction
   authorizes no additional resolver, syntax, semantic, parser/browser,
   package, documentation-product, or Git scope.

The decision question is:

> Approve H-DTTLF-USABILITY-CONTEXTUAL-ND-TEXT-REVISION-CORRECTION-01 /
> D-DTTLF-USABILITY-066 as proposed: correct D-065's exact file list by
> authorizing only the nine mechanical revision-literal replacements above,
> then resume the otherwise unchanged compact contextual text implementation?

## `CONTEXTUAL-ND-TEXT-PARITY-1AI` Implementation Result

The approved adapter slice is implemented without a new syntax tree, program
method, Core/checker/runtime case, classifier decomposition, or coherence
branch. The additive `displayed-context-transfor` expected contract carries
the optional-annotation family plus the two endpoint terms. Only that contract
selects `displayedTransforContextLambda`; the historical
`displayed-transfor` contract and base-component callback remain unchanged.

The resolver adds exactly one named term operation, `identityCell(endpoint)`,
and delegates it to the existing program method. Compact eta and fixed-head
pre/postwhiskering remain ordinary neutral applications, while recursive
vertical composition remains on the existing `composeCells` route. The
existing direct contextual factorer therefore continues to decide whether a
parsed point body determines a coherent whole `Transfd`.

Focused evidence is final-green:

- the affected text-parity file is 14/14, covering annotated and omitted
  family annotations, eta, identity, recursive composition, both whiskering
  orientations, the fixed four-level `Transf -> Hom -> Transf -> Hom` target,
  exact fail-closed negatives, and the historical base-component route;
- the nearest direct eta/identity/composition/whiskering corpus is 24/24,
  including fibre point, base-arrow, and higher-cell observations;
- root TypeScript typecheck and lint pass;
- exact search finds no superseded revision assertion, the nine D-066 files
  contain only the approved literal replacement, and whitespace is clean; and
- no kernel, browser, package, root runner, or public barrel changed, so no
  kernel or long aggregate rerun was required.

The implementation does not graduate unrestricted `:^nd`, arbitrary
point-arrow synthesis, or a varying four-parameter `Transf_catd` classifier.
Those remain semantic coverage questions rather than text-parser work.

## Explicit Non-Goals

This plan does not authorize:

- `Transf_catd_func` or another Lambdapi owner/rule;
- a new Core node, LF declaration, checker/evaluator branch, or runtime rule;
- a second public AST or parser dependency;
- decomposition of target classifiers to guess an expected contract;
- external naturality, functoriality, equality, or coherence evidence;
- curry, total-context sections, casts, or classifier mirrors;
- arbitrary pointwise arrow synthesis or unrestricted `:^nd`;
- browser presets, landing-page claims, book edits, deployment, publication,
  merge, push, scale resumption, or unrelated cleanup.

## Validation And Checkpoint Policy

For the read-only audit and proposal checkpoint:

- inspect staged and unstaged diffs separately;
- run only disposable/focused probes plus `git diff --check` and document-link
  hygiene;
- do not run the long TypeScript aggregate; and
- checkpoint the audit before freezing any behavioral implementation gate.

For a later approved TypeScript-only implementation:

- run its focused direct/text and negative corpus;
- run root typecheck and lint;
- run neighboring historical syntax-parity regressions;
- run `check:ts` only if the public barrel, shared generic checker/runtime,
  root test runner, or another boundary named by root SOP actually changes;
  otherwise carry forward the recent qualified aggregate; and
- synchronize this ledger, the predecessor plan, and the handoff before a
  bounded local checkpoint.

## Persistent `/goal` Launch Prompt

Continue the living TypeScript/emdash v3.2 objective from
`docs/TYPESCRIPT_ELABORATOR_V3_2_HANDOFF.md` and this plan. Recover the actual
goal worktree, active kernel/SOP, completed checkpoints, decision ledger, and
current dependency-ready row on every continuation.

Treat `HOM-CATD-ACTION-TRANSFER-GRADUATE-0AG` as read-only complete: fixed
alternating `Transf_catd`/`Hom_catd` targets, all five reviewed contextual
constructors, and their transferred action work without `Transf_catd_func`.
Keep a genuinely four-parameter-varying classifier deferred until a concrete
consumer exists.

Treat `CONTEXTUAL-ND-TEXT-PARITY-0AH` as executable and read-only complete.
Treat D-DTTLF-USABILITY-065 and its zero-behavior D-DTTLF-USABILITY-066
file-list correction as implemented and focused-green at their exact reviewed
boundaries. Preserve their 14/14 affected parity, 24/24 nearest direct,
typecheck/lint, exact revision-search, and whitespace evidence; do not repeat
the unchanged long aggregate. Execute
`CONTEXTUAL-ND-TEXT-PARITY-GRADUATE-0AJ` read-only first and select at most one
next semantic or reader-facing continuation from current evidence.
Preserve internal object-, arrow-, base-arrow-, and higher-action ownership and
fail closed outside the direct semantic envelope.

Use proportional validation and rollback-safe local checkpoints according to
`docs/PERSISTENT_GOAL_GIT_EXPERIMENTATION.md`. Preserve unrelated work. Do not
push, merge, rebase, amend, reset, publish, remove worktrees, deploy, or perform
unrelated cleanup without exact authorization.

## Decision Ledger

- **2026-08-02 — D-065/D-066 implementation final-green.** The text adapter
  adds one compact expected-contract route and one fixed `identityCell` head,
  while reusing neutral application, `composeCells`, and the existing direct
  factorer. The affected parity corpus is 14/14 and the nearest direct corpus
  is 24/24; typecheck, lint, exact revision search, and whitespace pass. The
  fixed alternating target follows the same route, all nine correction files
  contain only their approved literal replacement, and the historical route
  remains green. No aggregate, kernel, browser, or public-product boundary
  changed. The synchronized semantic checkpoint is pending in this bounded
  commit; read-only 0AJ is next.
- **2026-08-02 — D-DTTLF-USABILITY-066 approved exactly as proposed.** A
  separate immutable review of proposal checkpoint
  `bb485375f6c843adc6c3b80755b1eb11e9cdbf0a` confirms that the correction
  authorizes only nine exact revision-literal replacements already required
  by D-065 item 7. Under the standing unattended delegation, with immediate
  human supersession, D-065 implementation is dependency-ready.
- **2026-08-02 — D-065 implementation paused; D-066 file-list correction
  frozen.** Before editing behavior, exact search found nine existing tests
  pinning the revision whose update D-065 item 7 requires. D-065's exact file
  boundary omitted them. The correction authorizes only replacing those nine
  string literals and explicitly forbids test-logic or behavior changes. It is
  decision-pending until separate immutable review.
- **2026-08-02 — D-DTTLF-USABILITY-065 approved exactly as proposed.** A
  separate immutable review of proposal checkpoint
  `a4ee654d8e025df6962ea92f219819430852f51a` confirms that the delta is one
  additive expected-contract route and one `identityCell` resolver head. The
  endpoint terms remain semantic authority; the family field checks only the
  optional binder annotation and cannot cast or override endpoints. Approval
  is under the standing unattended delegation with immediate human
  supersession. `CONTEXTUAL-ND-TEXT-PARITY-1AI` is implementation-ready.
- **2026-08-02 — 0AH executable audit complete; D-065 frozen.** Direct compact
  eta, identity, recursive composition, prewhiskering, and postwhiskering all
  work through neutral application plus the existing factorer. Historical
  text `λ^nd k : K. eta k` remains green. Compact family annotation currently
  fails with `EXPECTED_CATEGORY`, and `identityCell` is the sole missing
  constructor head. The frozen proposal adds one expected-contract route and
  one resolver head, with no semantic or parser-grammar delta. It remains
  decision-pending until a separate immutable review.
- **2026-08-02 — plan opened after 0AG semantic graduation.** The alternating
  fixed-classifier probe demonstrates that current Hom/Transf nesting and
  action need no new owner. Inspection of `categorical_text.ts` isolates the
  first real user-facing gap: its historical `^nd` contract selects the
  base-component callback, not the compact fibre-object contextual callback.
  The read-only 0AH audit is dependency-ready; no behavior or implementation
  proposal is authorized yet.
