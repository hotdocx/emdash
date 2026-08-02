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
`CONTEXTUAL-ND-TEXT-PARITY-GRADUATE-0AJ` and
`CONTEXTUAL-ND-TELESCOPE-0AK` are read-only complete with zero behavior delta.
The audit checkpoint is `7eacf68ded54424fdac36339833b0df50d978451`.
The exact `CONTEXTUAL-ND-TELESCOPE-1AL` / D-DTTLF-USABILITY-067 proposal below
is frozen pending separate review; no semantic change is authorized yet.

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

## Selected Contextual Normal Form

The selected audit result is not a new mathematical owner. It factors the
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

The callback exposes friendly variables individually, but every value is the
application of one of these internally coherent accessors to one terminal
contextual fibre slot. It does not expose independent point data and later
assert that it is natural.

Each accessor is a closed displayed functor from the terminal context family.
Simple occurrences therefore remain finite endpoint chains from one terminal
slot. Composite occurrences such as `fibrePair(a,b)` are compiled by the
already-recursive displayed-context compiler against identity wiring for that
one terminal slot. The direct endpoint seam records the resulting whole
functor and passes it to the existing single-fibre point factorer. The
factorer, rather than a new contextual coherence algorithm, remains the sole
authority that may recover a whole `Transfd`.

This “packed semantic context, individually exposed variables” representation
is not a total-context section and does not invoke curry. It is internal
compiler evidence for the same direct telescope the user wrote.

## `CONTEXTUAL-ND-TELESCOPE-0AK` Audit Result

The read-only audit is complete with zero TypeScript, test, kernel, runtime,
parser, or browser delta.

### Independent siblings reuse the transparent product

A disposable witness packed two sibling families with the existing
fibrewise product and applied its two projection functors to one contextual
slot. The unchanged unary factorer recovered left and right eta, generic
identity, recursive composition, and both pre- and postwhiskering. The point
and higher observations remained ordinary internally typed `hom` terms. This
confirms that sibling variables require no multi-ordinal coherence rule.

### Genuine dependency is an accessor problem, not a new introduction rule

For

```text
k : K; a : A[k]; b : B[(k,a)]
```

the terminal source is `B` over `Sigma(A)`. The existing generic context
compiler already constructs:

- the prefix accessor from `B` to the pullback of `A` along the Sigma
  projection, using `sigma_functord_sec` and section/pullback weakening; and
- the pairing accessor from `B` to the fibrewise product of that lifted `A`
  with `B`.

A focused disposable consumer fed the pairing accessor to the unchanged
single-fibre contextual transformation binder. Eta was recovered as
prewhiskering, recursive composition produced a whole displayed
transformation, and both its point component and higher naturality
observation were internally typed. The emitted accessor Core contains the
existing `section-pullback` and `displayed-product-pair` owners. No cast,
external equation, curry, or new owner was used.

### The existing fold is genuinely finite-generic

Source inspection shows that the generic displayed telescope compiler loops
over every canonical sibling layer, constructs product projection wiring for
every binding, and lifts every accessor through every later Sigma layer. It
contains no two-, four-, or six-variable arity table. The existing durable
four-layer/six-binding corpus separately checks an early accessor, a middle
accessor, the final sibling pair, an internal base-arrow cell, and the
`homd_int` consumer. Its fail-closed corpus rejects wrong layer bases,
wrong target bases, duplicates, a false one-layer telescope, and predecessor
profile overreach.

One deliberately stronger disposable stress attempted to materialize a
single left-associated pair containing all six variables. It was stopped
after approximately eleven and a half minutes without a phase-local result.
Because that script did not emit phase markers, it does not establish whether
profile construction or expression duplication dominated. It is diagnostic
performance evidence only, not a semantic rejection. The selected
implementation must compute the context normal form once and share its
accessors; it must not rebuild one complete contextual functor independently
for each variable. Performance graduation remains separate from semantic
finite-genericity.

### Architecture selection

The audit selects the reusable contextual-normal-form candidate with these
exact refinements:

1. Extract the existing layer/product/Sigma/accessor fold into one immutable
   internal helper used by both displayed-functor and displayed-transfor
   contextual abstraction.
2. Create one hidden final-base slot and one terminal-family fibre slot.
3. Reify each normal-form accessor as a closed displayed functor and expose
   its application to the terminal slot as the corresponding friendly
   callback variable.
4. Extend the direct endpoint compiler only while this context is active: a
   simple accessor application keeps the existing chain fast path; a
   supported composite object expression reuses `compileDisplayedContextual`
   with identity wiring for the terminal slot.
5. Feed that compiled endpoint into the existing eta/identity/composition/
   whiskering point factorer. Do not add a second coherence synthesizer.
6. Preserve expected classifier checks and the existing failure boundary for
   incompatible bases, layer order, polarity, orientation, escaped values,
   and arbitrary point arrows.

The multi-ordinal factorer is not selected because coherent accessors already
reduce every written variable to one terminal slot. Dedicated recursion over
layer counts is not selected because it would duplicate the existing generic
fold. Naive nested unary `lambda^nd` remains semantically mismatched: a
completed inner binder is a whole transformation rather than the next outer
point body.

## Frozen `CONTEXTUAL-ND-TELESCOPE-1AL` Proposal

### H-DTTLF-USABILITY-CONTEXTUAL-ND-TELESCOPE-01 /
### D-DTTLF-USABILITY-067

Approval authorizes exactly the following TypeScript-only semantic slice:

1. In `src/v3_2/categorical_surface.ts`, extract the existing canonical
   sibling-layer/Sigma/accessor loop from
   `displayedGenericDependentContextLambda` into one private immutable normal
   form. It must contain the root base, layers, final base, terminal source
   family, and one lifted contextual compilation for every binding. The
   existing displayed-functor method must consume this helper without changing
   its emitted Core, evidence, errors, or availability boundary.
2. Generalize that private normal form to represent one independent sibling
   layer as well as two or more dependent layers. Preserve the existing
   displayed-functor API rule that routes a single sibling layer through
   `displayedContextLambda`; only the new transformation API may consume the
   general one-layer form.
3. Add one public direct program method with this semantic shape:

   ```ts
   displayedTransforDependentContextLambda(
     bindings,
     body: (variables: readonly CoreCategoricalTerm[]) =>
       CoreCategoricalTerm,
     options?
   ): CoreCategoricalTerm
   ```

   It requires at least two source-ordered canonical bindings and the existing
   mixed displayed profile. It evaluates the callback exactly once. Its result
   endpoints are synthesized from the typed point body and then checked again
   against the recovered whole transformation; callers need not separately
   duplicate contextual endpoint functors.
4. The builder creates exactly one hidden final-base slot and one terminal-
   family fibre slot. For every written binding, it reifies the corresponding
   normal-form accessor as a closed displayed functor and passes its
   application to that terminal slot as the friendly callback value. The
   callback receives no raw component function, equality, naturality square,
   retained closure, or total-context section.
5. Keep the existing direct endpoint-chain path unchanged as the fast path.
   While the new callback is active, add one scoped contextual fallback that
   compiles a supported composite endpoint through the existing
   `compileDisplayedContextual` recursion with identity wiring for the one
   terminal slot. Record whether the recovered endpoint is identity and carry
   its structural/dependent prerequisites; do not encode a synthetic chain or
   add a finite expression-shape table.
6. Route the compiled endpoint through the existing
   `factorDisplayedTransforPoint`. Eta, generic identity, typed recursive
   vertical composition, and fixed-head pre/postwhiskering must remain the
   complete accepted body algebra. The contextual fallback may broaden their
   endpoint expressions only to constructions already accepted by the
   displayed-context compiler, including variables, closed displayed-functor
   application, fibre pairing, and already-qualified displayed evaluation or
   nested forms.
7. Do not add a second transformation factorer. Local base/fibre usage is
   discharged only by the normal-form accessors and the existing factorer;
   the recovered result must be a closed whole `displayed-transfor` over the
   terminal source family. Arbitrary indexed point arrows remain rejected.
8. Add one frozen abstraction-evidence variant for the new telescope binder.
   It records source-ordered binding names, lifted binding families, canonical
   layers, terminal source family, recovered source/target family and
   functors, the underlying eta/identity/composition/whiskering rule, and
   merged structural/dependent prerequisites. It is metadata about explicit
   Core, not new Core or kernel evidence.
9. Preserve exact fail-closed diagnostics for duplicate names, noncanonical
   layer bases, incompatible callback families, wrong variation/dependency,
   noncovariant polarity, non-object cell level, escaped/foreign values,
   predecessor-profile use, and nonfactorable arbitrary point arrows. A
   failed callback must unwind every active base, slot, and contextual
   endpoint registration in `finally` blocks.
10. Add focused durable tests to the already registered
    `tests/v3_2_categorical_displayed_telescope_generic_tests.ts`; do not add
    or edit the root test runner. Cover:

    - independent siblings with a paired eta endpoint;
    - a genuine `a : A; b : B[a]` endpoint using both friendly variables;
    - generic identity, recursive composition, and both whiskering
      orientations over contextual endpoints;
    - one four-layer/six-binding witness using an early accessor and the final
      sibling pair, without requiring the diagnostic all-six synthetic pair;
    - a point component, an internal base-arrow/higher-naturality observation,
      callback-once behavior, frozen layer evidence, and explicit Core
      containing the existing product/Sigma/pullback owners; and
    - the exact negative matrix from item 9 plus unchanged compact unary and
      displayed-functor telescope behavior.

11. Edit only:

    - `src/v3_2/categorical_surface.ts`;
    - `src/v3_2/categorical_program.ts`;
    - `tests/v3_2_categorical_displayed_telescope_generic_tests.ts`;
    - this plan, the handoff, and the mixed-continuation ledger; and
    - one immutable D-067 review artifact before implementation.

    Any additional production or test file requires a frozen correction.
12. Run the affected telescope test file once, the nearest compact contextual
    `:^nd` regression in the same process where practical, root TypeScript
    typecheck and lint, exact revision/search checks, and whitespace hygiene.
    Do not run the approximately forty-four-minute aggregate: this slice
    changes no generic LF/checker/runtime, package, public barrel, root test
    runner, kernel, parser, or browser boundary. Carry forward the qualified
    aggregate and kernel evidence recorded by the predecessor plans.
13. Synchronize this plan, the handoff, and the mixed-continuation ledger, then
    create one rollback-safe local semantic checkpoint and one ledger
    checkpoint. Do not push, merge, rebase, amend, reset, publish, deploy,
    remove worktrees, or clean unrelated paths.

Explicit non-effects of D-067:

- no Lambdapi declaration, rewrite, unification rule, proof-time comparison,
  catalog, health, or warning change;
- no Core node, generic LF/checker/evaluator/runtime rule, second AST, parser,
  browser preset, README/book claim, or deployment;
- no curry, total-context section, cast, external coherence payload,
  `Product_catd` facade, `Transf_catd_func`, or new mixed classifier;
- no arbitrary dependency DAG, exchange across a dependency, unrestricted
  variance, arbitrary point-arrow synthesis, or unrestricted `:^nd` claim;
  and
- no claim that the diagnostic all-six-pair stress is performance-graduated.

## Alternatives Assessed By The Audit

The audit compared, rather than assumed, these implementation shapes:

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
| `CONTEXTUAL-ND-TELESCOPE-0AK` | read-only complete; zero behavior delta | completed 0AJ; generic displayed context fold; single-fibre point factorer | Select one shared normal form, coherent accessors applied to one terminal slot, and contextual endpoint reuse of the existing recursive object compiler. Independent siblings, genuine dependency, and finite mixed layers require no new owner or coherence algorithm. |
| `CONTEXTUAL-ND-TELESCOPE-1AL` | D-DTTLF-USABILITY-067 frozen pending separate review; implementation withheld | completed 0AK at `7eacf68ded54424fdac36339833b0df50d978451` | Factor one reusable normal form, add one synthesis-capable direct dependent-context transformation method, extend only the contextual endpoint seam, and cover recursive body/object/base-arrow/higher evidence plus fail-closed negatives. Text/browser promotion remains later. |

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
`dabe9d9827462b76a493c1dd34cc658e137f22d5`, 0AJ as read-only complete, and
`CONTEXTUAL-ND-TELESCOPE-0AK` as read-only complete at
`7eacf68ded54424fdac36339833b0df50d978451` with zero behavior delta. Its
selected architecture is one shared canonical-context normal form,
coherent accessors applied to one terminal contextual slot, recursive endpoint
compilation through the existing displayed-context compiler, and the existing
single-fibre factorer as sole coherence gate. Treat D-DTTLF-USABILITY-067 as
frozen pending a separate immutable review. After review, implement only its
thirteen numbered items. Preserve direct recursive binders and internal
object/arrow/higher action; add no curry, total-context section, cast, external
coherence, parser/browser behavior, or kernel owner.

Use proportional validation and rollback-safe local checkpoints. Preserve
unrelated work. Do not push, merge, rebase, amend, reset, publish, deploy,
remove worktrees, or perform unrelated cleanup without exact authorization.

## Decision Ledger

- **2026-08-02 — D-DTTLF-USABILITY-067 frozen pending separate review.** The
  exact TypeScript-only gate extracts one shared canonical normal form, exposes
  its coherent accessors through one terminal slot, adds one synthesis-capable
  direct telescope binder, and reuses the existing contextual object compiler
  only as the endpoint seam for the existing point factorer. Its exact file,
  test, validation, failure, performance, and non-effect boundaries are the
  thirteen numbered items above. No behavior is authorized before a separate
  immutable review.
- **2026-08-02 — 0AK read-only architecture audit complete; shared normal
  form selected.** Independent product projections, a genuine Sigma/pullback
  prefix accessor, and the existing finite-generic layer fold all feed one
  terminal contextual slot without external evidence. Composite variable
  occurrences can reuse the existing recursive displayed-context compiler;
  the current point factorer remains the sole `Transfd` gate. Multi-ordinal,
  layer-count recursion, curry, and new-owner alternatives are not selected.
  A non-phase-local all-six pairing stress was bounded after approximately
  eleven and a half minutes and is recorded only as a reason to share the
  normal form rather than recompute accessors. Freezing the exact 1AL proposal
  is next; no behavior is authorized by this audit.
- **2026-08-02 — 0AJ read-only graduation complete; 0AK selected.** Compact
  single-fibre direct/text parity is exact for eta, identity, recursive
  composition, and fixed-head pre/postwhiskering, including a fixed
  alternating Hom/Transf target. The next semantic usability boundary is
  multiple individually usable variables over the already-graduated canonical
  sibling/dependency context fold. The first audit compares an internal
  contextual-normal-form bundle with multi-ordinal and recursive-layer
  alternatives; it authorizes no behavior.
