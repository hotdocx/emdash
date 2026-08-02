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
semantic delta; `CONTEXTUAL-ND-TEXT-PARITY-0AH` is dependency-ready and
read-only first. No implementation proposal is authorized yet.

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
| `CONTEXTUAL-ND-TEXT-PARITY-0AH` | dependency-ready read-only audit; zero behavior delta authorized | completed 0AG; graduated historical syntax parity; direct D-055 through D-058 | Inventory one additive expected-contract route, optional family annotation, `identityCell`, neutral eta/pre/post application, recursive composition, exact negatives, and regression compatibility with historical base-component `^nd`. Freeze at most one bounded proposal. |
| `CONTEXTUAL-ND-TEXT-PARITY-1AI` | conditional; not authorized | completed 0AH and separate immutable review | Implement only the exact frozen adapter delta with focused direct/text equivalence and fail-closed tests. No semantic or public-preset expansion. |
| `CONTEXTUAL-ND-TEXT-PARITY-GRADUATE-0AJ` | deferred read-only graduation | green conditional 1AI | Re-audit the exact direct/text envelope and select the next semantic or reader-facing continuation without claiming unrestricted `:^nd`. |

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

Make `CONTEXTUAL-ND-TEXT-PARITY-0AH` the sole dependency-ready slice. Audit the
existing text adapter against the direct compact contextual `:^nd` API,
preserve the historical base-component route, and freeze at most one bounded
expected-contract/resolver proposal. Do not change behavior before a separate
review. Preserve internal object-, arrow-, base-arrow-, and higher-action
ownership and fail closed outside the direct semantic envelope.

Use proportional validation and rollback-safe local checkpoints according to
`docs/PERSISTENT_GOAL_GIT_EXPERIMENTATION.md`. Preserve unrelated work. Do not
push, merge, rebase, amend, reset, publish, remove worktrees, deploy, or perform
unrelated cleanup without exact authorization.

## Decision Ledger

- **2026-08-02 — plan opened after 0AG semantic graduation.** The alternating
  fixed-classifier probe demonstrates that current Hom/Transf nesting and
  action need no new owner. Inspection of `categorical_text.ts` isolates the
  first real user-facing gap: its historical `^nd` contract selects the
  base-component callback, not the compact fibre-object contextual callback.
  The read-only 0AH audit is dependency-ready; no behavior or implementation
  proposal is authorized yet.
