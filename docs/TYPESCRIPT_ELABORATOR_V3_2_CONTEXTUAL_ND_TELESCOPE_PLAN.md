# TypeScript Elaborator v3.2 — Contextual `:^nd` Canonical Telescopes

Date: 2026-08-02

Plan-ID: TS-ELAB-V3.2-CONTEXTUAL-ND-TELESCOPE

Depends-On:
[`TYPESCRIPT_ELABORATOR_V3_2_CONTEXTUAL_ND_TEXT_PARITY_PLAN.md`](./TYPESCRIPT_ELABORATOR_V3_2_CONTEXTUAL_ND_TEXT_PARITY_PLAN.md),
[`TYPESCRIPT_ELABORATOR_V3_2_FIBRED_CONTEXT_PLAN.md`](./TYPESCRIPT_ELABORATOR_V3_2_FIBRED_CONTEXT_PLAN.md),
[`TYPESCRIPT_ELABORATOR_V3_2_MIXED_INTRODUCTION_PUBLIC_CONTINUATION_PLAN.md`](./TYPESCRIPT_ELABORATOR_V3_2_MIXED_INTRODUCTION_PUBLIC_CONTINUATION_PLAN.md),
and
[`TYPESCRIPT_ELABORATOR_V3_2_CATEGORICAL_BINDER_RFC.md`](./TYPESCRIPT_ELABORATOR_V3_2_CATEGORICAL_BINDER_RFC.md)

Status: active semantic successor; compact single-fibre `:^nd` text parity is
final-green at checkpoint `dabe9d9827462b76a493c1dd34cc658e137f22d5`;
`CONTEXTUAL-ND-TEXT-PARITY-GRADUATE-0AJ` is read-only complete with zero
behavior delta; `CONTEXTUAL-ND-TELESCOPE-0AK` is dependency-ready and
read-only. No implementation proposal or semantic change is authorized yet.

## Objective

Determine the smallest scalable direct architecture for displayed-natural
abstraction over the canonical finite displayed telescopes already supported
by the displayed-functor context compiler. The intended end-user envelope is
conceptually:

```text
independent siblings
  lambda^nd (a : E, b : C). body(a,b)

genuine dependency
  lambda^nd (a : A; b : B[a]). body(a,b)

canonical finite mixed layers
  lambda^nd (a : A; b : B[a], c : C[a]; d : D[b,c]). body(a,b,c,d)
```

Literal text spelling remains downstream. The semantic task is to expose the
variables individually to a direct TypeScript callback while producing one
whole internally coherent `Transfd`, with no pointwise naturality payload.

## Inherited Settled Architecture

The following decisions are not reopened:

1. Direct recursive binders are fundamental. Mixed curry, a total-context
   section, and callback-retaining encodings are not prerequisites.
2. Binder mode is intrinsic: `lambda^nd` denotes natural displayed
   abstraction. A family annotation is an optional classifier check, not the
   source of the mode.
3. Endpoint displayed functors remain semantic authority. No family field,
   contextual view, or text expectation may cast or override them.
4. Object, fibre-arrow, base-arrow, and higher-cell action must be owned by
   existing internal emdash constructions. External equality or naturality
   evidence is forbidden.
5. The existing single-fibre factorer is the coherence gate for the reviewed
   body algebra:

   ```text
   eta | identity(endpoint) | compose(outer,inner)
       | postmap(H,cell) | premap(cell,L).
   ```

6. Fixed and recursively nested `Hom_catd`/`Transf_catd` targets are already
   target-generic. A varying four-parameter `Transf_catd` constructor is not a
   dependency of contextual telescope abstraction.

## `CONTEXTUAL-ND-TEXT-PARITY-GRADUATE-0AJ` Result

The read-only graduation audit is complete with zero behavior delta.

### Compact text parity is exact at the reviewed semantic boundary

The direct program and text adapter now accept the same five single-fibre
contextual bodies. The text layer adds no action table or coherence branch:

- eta and fixed-head pre/postwhiskering use neutral application;
- identity uses the existing `identityCell` program operation;
- vertical composition uses the existing `composeCells` operation; and
- `displayedTransforContextLambda` and its recursive point factorer remain the
  sole authorities for recovering a whole `Transfd`.

The fixed four-level `Transf -> Hom -> Transf -> Hom` target uses the same
expected-contract route. Therefore neither classifier-head parsing nor
`Transf_catd_func` is the next blocker.

### Context arity is now the first semantic usability boundary

The direct compact method owns exactly the expanded telescope

```text
k :^n K; a :^n E[k]
```

and the point factorer is parameterized by exactly one base ordinal and one
fibre ordinal. By contrast, the displayed-functor context machinery already
owns:

- pointwise product families for independent siblings;
- Sigma base extension for genuine dependency;
- pullback/reindexing of earlier families into later bases;
- product projections, weakening, pairing, exchange, and contraction;
- a generic dependency-plan fold for arbitrary finite canonical layers; and
- internally owned object and base-arrow action for those accessors.

That machinery currently compiles a contextual object body directly into a
whole displayed functor. It does not expose a reusable immutable “context
normal form plus accessor functors” to the displayed-transfor factorer.

### Reader-facing promotion is downstream

The public reviewer still demonstrates the historical base-component
`lambda^nd k` composition form. The compact form is now suitable for a later
preset, and the frozen syntax-capability audit underclaims compact composition
and whiskering. Those are presentation synchronizations, not semantic
blockers. Promoting them before the multi-variable architecture is measured
would create avoidable repeated reader-facing churn.

## Candidate Contextual Normal Form

The preferred audit candidate is not a new mathematical owner. It factors the
existing canonical context compiler into an immutable internal bundle:

```text
CanonicalDisplayedContext = {
  rootBase,
  accumulatedBase,
  terminalSourceFamily,
  variables: [internally coherent accessors],
  structuralPrerequisites,
  dependentPrerequisites
}
```

The normalization follows the existing semantic constructions:

- an independent terminal sibling group is represented by the transparent
  fibrewise product and its existing projections;
- a completed dependency prefix is represented in the accumulated Sigma base;
- earlier variables are recovered through Sigma projections and existing
  section/pullback weakening under later families; and
- the final variable or sibling group is the terminal displayed source
  family.

The callback may expose friendly variables individually, but each value must
be obtained by applying one of these internally coherent accessors. It must
not expose independent point data and later assert that it is natural.

If every accessor can be presented as a finite endpoint chain from one
terminal contextual slot, the existing single-fibre point factorer can remain
unchanged. This is already strongly suggested for independent siblings:
product projections are closed displayed functors and therefore fit existing
prewhiskering. Genuine dependency is the decisive case: an earlier prefix
variable is recovered from the hidden accumulated base and weakened under the
terminal family, so its construction may require a bounded extension of the
endpoint compiler even though all semantic owners already exist.

This “packed semantic context, individually exposed variables” representation
is not a total-context section and does not invoke curry. It is internal
compiler evidence for the same direct telescope the user wrote.

## Alternatives Retained For Audit

The audit must compare, rather than assume, these implementation shapes:

1. **Reusable contextual-normal-form bundle — preferred candidate.** Factor
   dependency planning, accumulated bases, terminal family, and accessors out
   of the current displayed-functor compiler. Feed its single terminal slot
   through the existing displayed-transfor factorer.
2. **Multi-ordinal point factorer — fallback candidate.** Retain one actual
   slot per written variable and generalize point factorization over the
   existing contextual wiring map. This may be necessary if dependent prefix
   accessors cannot be expressed as a finite chain from the terminal slot.
3. **Dedicated recursion over canonical layers — comparison candidate.** Add
   one frontend-only recursive wrapper whose cases mirror the already-owned
   product/Sigma/pullback layer fold and end in the existing unary factorer.
4. **Nested unary `lambda^nd` — unlikely candidate.** A completed inner binder
   is a whole transformation, not a point body for the next outer binder, so
   naive nesting does not by itself provide the required introduction rule.

The following are rejected unless a later separately reviewed audit produces
contrary executable evidence:

- external component/naturality equations;
- a cast from a pointwise arrow to `Transfd`;
- mixed curry or a total-context-section API;
- a second Core/checker/evaluator hierarchy;
- a new kernel owner merely to name frontend context wiring; and
- classifier-head-specific parser or factorer branches.

## Work Ledger

| Slice | Status | Dependency | Exact boundary |
|---|---|---|---|
| `CONTEXTUAL-ND-TEXT-PARITY-1AI` | final-green at `dabe9d9827462b76a493c1dd34cc658e137f22d5` | D-065/D-066 | Single-fibre compact text exactly matches eta, identity, recursive composition, and both whiskering orientations; historical base-component text remains unchanged. |
| `CONTEXTUAL-ND-TEXT-PARITY-GRADUATE-0AJ` | read-only complete; zero behavior delta | final-green 1AI | Graduates only the exact single-fibre direct/text envelope and identifies canonical multi-variable context abstraction—not parser or classifier-head behavior—as the first remaining usability gap. |
| `CONTEXTUAL-ND-TELESCOPE-0AK` | dependency-ready read-only architecture audit | completed 0AJ; generic displayed context fold; single-fibre point factorer | Compare reusable context-normal-form, multi-ordinal factorer, and bounded layer-recursion candidates using one independent-sibling witness, one genuine dependency witness, and one finite mixed-layer witness. Freeze at most one smallest implementation proposal. |
| `CONTEXTUAL-ND-TELESCOPE-1AL` | deferred conditional implementation | completed 0AK and separate reviewed proposal | Implement only the selected internally owned contextual abstraction seam, focused object/base-arrow/higher-cell evidence, and direct negatives. Text/browser promotion remains later. |

## `CONTEXTUAL-ND-TELESCOPE-0AK` Audit Contract

The read-only audit must answer these questions from current code and bounded
disposable probes:

1. Can the existing generic dependency planner produce one stable contextual
   normal form containing accumulated base, terminal source family, and one
   coherent accessor for every written variable?
2. For independent siblings, do existing fibrewise-product projections let
   the unchanged unary contextual factorer recover eta, identity,
   composition, and both whiskering orientations?
3. For a genuine chain `a : A; b : B[a]`, can the prefix accessor be expressed
   through existing Sigma projection and section/pullback weakening so that a
   body may use both `a` and `b` without external evidence?
4. Does the same mechanism fold over an arbitrary finite canonical mixture of
   sibling groups and dependency layers rather than adding a finite arity
   table?
5. Can endpoint and body checking remain expected-type-directed and fail
   closed for incompatible bases, family order, dependency edges, polarity,
   orientation, or arbitrary point arrows?
6. Do object, fibre-arrow, base-arrow, and higher-cell observations reduce
   through already-active owners? Audit existing kernel constructions before
   proposing any declaration or rule.
7. Is the smallest reusable seam a context-normal-form helper, a generalized
   endpoint compiler, or a multi-ordinal factorer? Freeze at most one exact
   proposal and record the alternatives.

The audit may add disposable ignored probes and edit documentation. It may not
change TypeScript behavior, Lambdapi source, tests, browser presets, public
claims, packages, or runners. Any implementation proposal requires its own
immutable checkpoint and separate review.

## Explicit Non-Claims

This plan does not yet claim or authorize:

- arbitrary dependency DAGs or exchange across a genuine dependency;
- every variance/polarity alternation;
- a varying `Transf_catd(A[k],B[k],F[k],G[k])` constructor;
- arbitrary point-arrow or transformation-valued body synthesis;
- general displayed curry, a `Product_catd` facade, or new product
  definitional equalities;
- unrestricted `:^nd` or ordinary-DTT-like occurrence completeness;
- text syntax, browser presets, README/book changes, deployment, publication,
  bulk scale resumption, or whole-library transfer graduation; or
- push, merge, rebase, amend, reset, worktree removal, or unrelated cleanup.

## Validation And Checkpoint Policy

For 0AK, use exact source inspection, disposable focused probes, document-link
hygiene, and `git diff --check`. Do not run the long TypeScript aggregate. If a
probe depends on current kernel names, use the bounded active-kernel check
required by repository SOP; do not edit Lambdapi during the audit.

For any later separately approved implementation, run only its focused direct
object/base-arrow/higher-cell corpus, nearest contextual regressions,
typecheck/lint, and exact diff. A shared generic checker/runtime or public
barrel change would independently trigger the root aggregate rule; otherwise
carry forward the current qualified aggregate.

Use rollback-safe local checkpoints under
[`PERSISTENT_GOAL_GIT_EXPERIMENTATION.md`](./PERSISTENT_GOAL_GIT_EXPERIMENTATION.md).
Preserve unrelated work.

## Persistent `/goal` Launch Prompt

Continue the living TypeScript/emdash v3.2 objective from
`docs/TYPESCRIPT_ELABORATOR_V3_2_HANDOFF.md` and this plan. Recover the actual
goal worktree, active kernel/SOP, completed checkpoints, decision ledger, and
current dependency-ready row on every continuation.

Treat compact single-fibre direct/text `:^nd` parity as final-green at
`dabe9d9827462b76a493c1dd34cc658e137f22d5` and 0AJ as read-only complete.
Execute `CONTEXTUAL-ND-TELESCOPE-0AK` read-only first. Compare the reusable
context-normal-form, multi-ordinal factorer, and bounded layer-recursion
candidates from executable evidence. Preserve direct recursive binders and
internal object/arrow/higher action; add no curry, total-context section, cast,
external coherence, parser/browser behavior, or kernel owner during the
audit. Freeze at most one smallest implementation proposal and obtain a
separate review before behavior changes.

Use proportional validation and rollback-safe local checkpoints. Preserve
unrelated work. Do not push, merge, rebase, amend, reset, publish, deploy,
remove worktrees, or perform unrelated cleanup without exact authorization.

## Decision Ledger

- **2026-08-02 — 0AJ read-only graduation complete; 0AK selected.** Compact
  single-fibre direct/text parity is exact for eta, identity, recursive
  composition, and fixed-head pre/postwhiskering, including a fixed
  alternating Hom/Transf target. The next semantic usability boundary is
  multiple individually usable variables over the already-graduated canonical
  sibling/dependency context fold. The first audit compares an internal
  contextual-normal-form bundle with multi-ordinal and recursive-layer
  alternatives; it authorizes no behavior.
