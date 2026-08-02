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
is separately reviewed-approved from immutable proposal checkpoint
`57c811fd9ab992abffa6b2388aed06dec3dae19d` under the user's standing
unattended delegation, with immediate human supersession. Implementation is
dependency-ready at exactly its thirteen numbered items, subject to the exact
D-DTTLF-USABILITY-068 audit-inventory file-list correction below. D-068 is
separately reviewed-approved from immutable checkpoint
`dc104610c3cb8bbaf665382afe23802c12db41a2` under the standing unattended
delegation, with immediate human supersession. The combined D-067/D-068
implementation is final-green at rollback-safe semantic checkpoint
`01848adf70acbb49e2f6dbbe35b8fef90b517915`.
`CONTEXTUAL-ND-TELESCOPE-GRADUATE-0AM` is read-only complete with zero
behavior delta. It selects the exact
`CONTEXTUAL-ND-TELESCOPE-TEXT-PARITY-1AN` / D-DTTLF-USABILITY-069 proposal
below, frozen pending separate review.

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

## Frozen Text-Parity Inventory Correction

### H-DTTLF-USABILITY-CONTEXTUAL-ND-TELESCOPE-AUDIT-CORRECTION-01 /
### D-DTTLF-USABILITY-068

The first implementation typecheck found one exact mechanical consumer omitted
from D-067 item 11. Adding a public `CoreCategoricalProgram` method is
deliberately exhaustive: `categorical_text_parity_audit.ts` fails typechecking
until every method is classified. This is not a request for text syntax.

Approval authorizes exactly:

1. Add `src/v3_2/categorical_text_parity_audit.ts` to the D-067 writable file
   boundary.
2. Add `displayedTransforDependentContextLambda` to the existing
   `displayed-natural-abstraction-and-composition` capability row. Update only
   that row's profile, scoped-binding, body-grammar, proposed-text, positive,
   and negative prose as needed to distinguish implemented direct semantic
   capability from deferred text parity. Keep its classification
   `typed-resolver-seam` and its first implementation row
   `SYNTAX-PARITY-1A`; add no parser/resolver behavior.
3. Add `tests/v3_2_categorical_text_parity_audit_tests.ts` to the writable test
   boundary and update only its exact public-method count from 83 to 84 plus
   any assertion needed to prove the new method occurs exactly once in that
   existing capability row. Do not change the capability-row count or
   classification counts.
4. Run the focused parity-audit test with the D-067 focused validation; do not
   add a test-runner import or repeat the aggregate.
5. Make no other production, test, parser, text revision, expected-contract,
   browser, kernel, Core, checker, runtime, package, or public-claim change.

D-067 implementation may resume after the separate immutable review recorded
below. All D-067 semantic and non-effect boundaries remain unchanged.

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
| `CONTEXTUAL-ND-TELESCOPE-1AL` | final-green at `01848adf70acbb49e2f6dbbe35b8fef90b517915` | completed 0AK at `7eacf68ded54424fdac36339833b0df50d978451`; D-067 proposal `57c811fd9ab992abffa6b2388aed06dec3dae19d`; D-068 correction `dc104610c3cb8bbaf665382afe23802c12db41a2`; immutable reviews | One shared normal form now feeds a synthesis-capable direct dependent-context transformation method and the existing contextual endpoint/factorer seam. Independent siblings, genuine dependency, four-layer/six-binding access, identity, composition, both whiskerings, point/higher action, frozen evidence, and the fail-closed matrix are executable. Text/browser promotion remains later. |
| `CONTEXTUAL-ND-TELESCOPE-AUDIT-CORRECTION-1AL1` | final-green; implementation folded into 1AL | first D-067 typecheck; exhaustive public-method inventory | The new method occurs exactly once in the existing displayed-natural capability row; the inventory is 84 methods in 14 unchanged rows and adds no text behavior. |
| `CONTEXTUAL-ND-TELESCOPE-GRADUATE-0AM` | read-only complete; zero behavior delta | final-green 1AL; prior alternating Hom/Transf and mixed-target evidence | The finite canonical semantic envelope is coherent and classifier-head-agnostic. Grouped text grammar already exists; the missing seam is one expected-contract/resolver route, not a mixed-variance construction. |
| `CONTEXTUAL-ND-TELESCOPE-TEXT-PARITY-1AN` | D-DTTLF-USABILITY-069 frozen pending separate review; zero behavior authorized before approval | completed 0AM; final-green typed method | Add one grouped displayed-transformation expected contract and resolver route to the existing typed API, preserve the body algebra and fail-closed boundary, bump the text revision, and prove direct/text parity without a second parser or semantic factorer. |

## `CONTEXTUAL-ND-TELESCOPE-GRADUATE-0AM` Audit Result

The exact finite canonical semantic envelope graduates:

1. A source telescope is an arbitrary finite nonempty sequence of canonical
   sibling layers, where every later layer is literally over the Sigma total
   of the preceding layer's left-associated fibrewise product. The public
   transformation method requires at least two written bindings; compact one-
   fibre `:^nd` remains the earlier final-green method.
2. Every written variable is a coherent accessor application to one terminal
   contextual slot. There is no multi-ordinal coherence payload, retained
   callback, total-context section, or external naturality equation.
3. The body algebra is the existing factorer algebra: eta, generic identity,
   typed recursive vertical composition, and fixed-head pre- and
   postwhiskering over endpoint expressions already accepted by the recursive
   displayed-context compiler.
4. The result is one closed whole `Transfd`. Point components and base-arrow/
   higher observations use existing internal owners. The implementation does
   not inspect `Hom_catd` or `Transf_catd` classifier heads and adds no
   arrow-only binder.
5. Independent siblings, a genuine dependency edge, and a four-layer/six-
   binding early-plus-final occurrence are executable. The deep semantic
   witness takes about 6.8 seconds after removing redundant explicit-Core
   serialization; worst-case serialization size remains a performance non-
   claim rather than a semantic failure.

The text audit finds a narrow mechanical seam:

- `LocatedLambda` already parses arbitrary alphabetic modes and comma/
  semicolon binding groups. No grammar or second AST is missing.
- The existing `displayed-dependent-context-functor` resolver already owns
  exact group-shape checking, optional displayed-family annotations, ordered
  flattening, callback-local bindings, and canonical layer-presentation
  validation.
- `resolveContextLambdaBody` already resolves `fibrePair`, named eta,
  `identityCell`, `composeCells`, and ordinary applications recursively.
- Only `resolveRootLambda` rejects a grouped mode other than `^fd`, and the
  public expected-contract union has no grouped displayed-transformation
  variant. The final-green typed method already synthesizes its endpoints, so
  the new text contract needs source groups but must not duplicate source and
  target functors.

No concrete mixed-variance prerequisite was found. Existing alternating
`Hom_catd`/`Transf_catd` contextual evidence, the fixed mixed-target corpus,
and the `homd_int` consumer remain internal-action evidence. Unrestricted
variance is still a non-claim, but it is not a blocker for routing the exact
typed mathematical constructions now implemented. Therefore 0AM selects text
parity rather than another semantic owner or factorer.

## Frozen `CONTEXTUAL-ND-TELESCOPE-TEXT-PARITY-1AN` Proposal

### H-DTTLF-USABILITY-CONTEXTUAL-ND-TELESCOPE-TEXT-PARITY-01 /
### D-DTTLF-USABILITY-069

Approval authorizes exactly:

1. Add one `CoreCategoricalTextTermExpected` variant named
   `displayed-dependent-context-transfor`. It contains ordered
   `sourceGroups` and no separately supplied endpoint functors; the typed body
   and final-green program method synthesize and recheck those endpoints.
2. In `resolveRootLambda`, route both a multi-level grouped `^nd` lambda and a
   one-level multi-sibling `^nd` lambda to one new resolver. Preserve the
   existing `^fd` routes and all ungrouped `^n`, `^fd`, and compact `^nd`
   routes. The parser and located syntax nodes do not change.
3. Factor the existing exact source-group cardinality, annotation, flattening,
   and callback-environment setup only as needed for reuse by the `^fd` and
   `^nd` grouped resolvers. Do not introduce a second elaborator or duplicate
   the canonical layer algorithm.
4. The new resolver must call only
   `displayedTransforDependentContextLambda`. Pass source-ordered bindings and
   resolve the body recursively in the existing callback-local environment.
   Do not request or construct pointwise naturality evidence.
5. Generalize the existing post-elaboration layer-presentation check to accept
   either the displayed-functor telescope evidence or the new displayed-
   transformation telescope evidence. Presented comma/semicolon groups must
   exactly equal the internally derived layers.
6. Text may express exactly the final-green body algebra through existing term
   syntax: paired eta, generic identity, recursive `composeCells`, and fixed-
   head pre/post application. An unsupported body must preserve the typed
   API's fail-closed diagnostic; no arbitrary point arrow is promoted.
7. Advance `CORE_CATEGORICAL_TEXT_REVISION` exactly to
   `CONTEXTUAL-ND-TELESCOPE-TEXT-PARITY-1AN-CATEGORICAL-TEXT-1`. Mechanically
   synchronize the nine existing exact revision assertions and no unrelated
   expected output.
8. Update the existing displayed-natural capability-row prose in
   `categorical_text_parity_audit.ts` to record grouped direct/text coverage.
   Keep its `typed-resolver-seam` classification, `SYNTAX-PARITY-1A` owner,
   the 84-method count, fourteen-row count, and classification totals.
9. Add focused tests to the already registered generic telescope corpus. Cover
   direct/text equality for an independent paired eta and a genuine dependent
   pair; identity, composition, and both whiskering orientations; one deep
   group-presentation witness without serializing its enormous Core; callback-
   once and frozen evidence; optional annotations; and wrong expected kind,
   group shape, annotation family, mode, predecessor profile, and unsupported
   body failures.
10. Edit only:

    - `src/v3_2/categorical_text.ts`;
    - `src/v3_2/categorical_text_parity_audit.ts`;
    - `tests/v3_2_categorical_displayed_telescope_generic_tests.ts`;
    - the eight other test files that pin the exact text revision:
      `v3_2_categorical_text_internal_action_audit_tests.ts`,
      `v3_2_categorical_text_recursive_mixed_tests.ts`,
      `v3_2_categorical_text_result_constructor_audit_tests.ts`,
      `v3_2_categorical_text_nested_ordinary_tests.ts`,
      `v3_2_categorical_text_internal_action_tests.ts`,
      `v3_2_categorical_text_displayed_constructor_tests.ts`,
      `v3_2_categorical_text_constructor_tests.ts`, and
      `v3_2_categorical_text_graduation_audit_tests.ts`;
    - this plan, the handoff, and the mixed-continuation ledger; and
    - one immutable D-069 review artifact before implementation.

    Any additional production or test file requires a frozen correction.
11. Run typecheck, lint, whitespace hygiene, the focused parity-audit test,
    and one name-filtered telescope text run that covers the new cases. Verify
    the exact revision inventory by search. Do not rerun the long aggregate,
    full telescope corpus, browser, kernel, print, or book checks; none of
    those boundaries changes.
12. Synchronize the three living ledgers, then create one rollback-safe local
    semantic checkpoint and one ledger checkpoint. Do not push, merge, rebase,
    amend, reset, publish, deploy, remove worktrees, or clean unrelated paths.

Explicit non-effects:

- no new parser grammar, second AST, Core/checker/runtime case, kernel owner,
  rewrite/unification rule, external coherence payload, curry, product facade,
  or classifier decomposition heuristic;
- no arbitrary dependency DAG, exchange, unrestricted variance, unrestricted
  `:^nd`, arbitrary point-arrow synthesis, or serialization-performance claim;
- no browser/README/book/public preset, deployment, publication, scale
  resumption, package, barrel, or root-runner change; and
- no claim that host-language callback control flow is reproducible as text.

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

## `CONTEXTUAL-ND-TELESCOPE-GRADUATE-0AM` Audit Contract

This is the next dependency-ready row. It is read-only and must:

1. Reconcile the final-green implementation and focused evidence against all
   thirteen D-067 items and the exact D-068 inventory correction.
2. State the precise graduated semantic envelope: finite canonical sibling/
   Sigma layers, coherent named accessors, terminal-slot synthesis, and the
   existing eta/identity/composition/pre/post factorer algebra.
3. Confirm that point components and base-arrow/higher observations continue
   through internal kernel-owned constructions; do not introduce external
   naturality data or a new owner.
4. Distinguish semantic finite genericity from the explicitly non-graduated
   cases: arbitrary dependency DAGs, exchange across dependency, unrestricted
   polarity/variance, arbitrary point arrows, and worst-case explicit-Core
   serialization size.
5. Audit the existing categorical text expected-contract and resolver seams
   for independent siblings and genuine dependency without editing them.
   Determine whether telescope text parity is now mechanical over the typed
   API or identify one exact semantic obstruction.
6. Reconcile the inherited alternating `Hom_catd`/`Transf_catd`, fixed mixed
   target, and `homd_int` evidence. Do not require a new variance feature
   merely because unrestricted variance remains a non-claim; require one
   executable missing end-user term before selecting semantic work.
7. Select and freeze at most one exact next proposal. Prefer text parity if no
   concrete semantic counterexample is found. Any behavior change requires a
   separate immutable proposal checkpoint and review.

The audit may edit the three living ledgers and use bounded disposable ignored
probes. It may not edit TypeScript behavior, tests, parser/browser artifacts,
Lambdapi, public claims, packages, or runners, and it must not rerun the long
aggregate or the already-measured telescope corpus.

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
separately reviewed-approved from immutable proposal checkpoint
`57c811fd9ab992abffa6b2388aed06dec3dae19d` under the standing unattended
delegation, with immediate human supersession. Implement only its thirteen
numbered items plus the separately reviewed exact D-068 inventory correction.
Treat the combined implementation as final-green at
`01848adf70acbb49e2f6dbbe35b8fef90b517915`. Run
`CONTEXTUAL-ND-TELESCOPE-GRADUATE-0AM` as read-only complete with zero behavior
delta. It finds no concrete mixed-variance blocker and freezes exactly
`CONTEXTUAL-ND-TELESCOPE-TEXT-PARITY-1AN` / D-DTTLF-USABILITY-069 pending a
separate immutable review. Do not implement it before that review. Preserve
direct recursive binders and internal
object/arrow/higher action; add no curry, total-context section, cast,
external coherence, parser/browser behavior, or kernel owner.

Use proportional validation and rollback-safe local checkpoints. Preserve
unrelated work. Do not push, merge, rebase, amend, reset, publish, deploy,
remove worktrees, or perform unrelated cleanup without exact authorization.

## Decision Ledger

- **2026-08-02 — 0AM read-only graduation complete; D-069 text-parity
  proposal frozen.** The final-green typed method graduates finite canonical
  sibling/Sigma telescopes, coherent named accessors, the existing recursive
  eta/identity/composition/whiskering factorer, and internal point/higher
  action. Arbitrary DAGs, exchange, unrestricted variance, arbitrary point
  arrows, and worst-case serialization remain explicit non-claims. Source
  inspection finds that grouped grammar, annotations, callback-local body
  resolution, and canonical presentation checks already exist; only one
  grouped transformation expected contract and resolver route are missing.
  No executable mixed-variance counterexample requires semantic work first.
  The exact twelve-item D-069 proposal is frozen pending separate review and
  authorizes no behavior yet.
- **2026-08-02 — D-067/D-068 implementation final-green at
  `01848adf70acbb49e2f6dbbe35b8fef90b517915`; 0AM selected.** One shared
  canonical normal form now serves the existing displayed-functor telescope
  and the new synthesis-capable displayed-natural telescope. The new callback
  receives coherent accessor applications to one terminal slot; the existing
  point factorer alone recovers eta, identity, recursive composition, and both
  whiskering orientations. Independent siblings, a genuine Sigma/pullback
  dependency, a four-layer/six-binding early-plus-final witness, point
  components, internal higher action, frozen evidence, exact mode/profile/
  family/escape failures, and unchanged compact unary behavior execute.
  Typecheck and lint are green. The focused parity inventory passes 6/6. The
  first telescope run completed all semantics and reported only two stale
  `Sigma_cat` spelling assertions plus one duplicate fixture declaration;
  after exact harness correction, the affected 3/3 rerun passes. Redundant
  serialization of the deep explicit Core was removed because the genuine
  dependency test already proves product/Sigma/pullback owners; this reduces
  the deep test body from approximately sixteen minutes to 6.8 seconds
  without weakening the four-layer evidence. The long aggregate and kernel
  checks remain intentionally carried forward because no corresponding
  boundary changed. The next row is the read-only 0AM graduation audit. It
  must distinguish the proven finite canonical semantic envelope from
  unrestricted variance and serialization-performance non-claims, then
  select text parity unless one executable semantic counterexample requires a
  separately reviewed prerequisite.
- **2026-08-02 — D-DTTLF-USABILITY-068 separately reviewed-approved.** The
  immutable review of correction checkpoint
  `dc104610c3cb8bbaf665382afe23802c12db41a2` confirms that exactly one existing
  semantic capability row and its exact count test are mechanically affected.
  Classification totals, row count, text revision, parser/resolver behavior,
  and every D-067 non-effect remain unchanged. Implementation may resume under
  the standing unattended delegation with immediate human supersession.
- **2026-08-02 — D-DTTLF-USABILITY-068 inventory correction frozen.** The
  first implementation typecheck proves that the exhaustive public-method
  inventory and its focused count test are mechanically affected by D-067's
  new public method. The five-item correction adds only those two files,
  classifies the method in the existing displayed-natural semantic row, and
  keeps parser/resolver behavior unchanged. D-067 implementation pauses until
  a separate immutable review.
- **2026-08-02 — D-DTTLF-USABILITY-067 separately reviewed-approved.** The
  immutable review of proposal checkpoint
  `57c811fd9ab992abffa6b2388aed06dec3dae19d` confirms that the new method
  connects the existing finite-generic accessor fold to the existing recursive
  endpoint compiler and point factorer. It highlights scoped cleanup,
  identity-versus-chain discrimination, prerequisite retention, exact recovered
  endpoint checks, and the non-graduated performance stress as mandatory
  implementation conditions. Under the standing unattended delegation, with
  immediate human supersession, the thirteen-item implementation is
  dependency-ready.
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
