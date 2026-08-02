# TypeScript Elaborator v3.2 — Compositional Natural Binders

Date: 2026-08-02

Plan-ID: TS-ELAB-V3.2-COMPOSITIONAL-NATURAL-BINDER

Depends-On:
[`TYPESCRIPT_ELABORATOR_V3_2_CONTEXTUAL_ND_TELESCOPE_PLAN.md`](./TYPESCRIPT_ELABORATOR_V3_2_CONTEXTUAL_ND_TELESCOPE_PLAN.md),
[`TYPESCRIPT_ELABORATOR_V3_2_RECURSIVE_MIXED_NESTING_PLAN.md`](./TYPESCRIPT_ELABORATOR_V3_2_RECURSIVE_MIXED_NESTING_PLAN.md),
[`TYPESCRIPT_ELABORATOR_V3_2_MIXED_INTRODUCTION_PUBLIC_CONTINUATION_PLAN.md`](./TYPESCRIPT_ELABORATOR_V3_2_MIXED_INTRODUCTION_PUBLIC_CONTINUATION_PLAN.md),
and
[`TYPESCRIPT_ELABORATOR_V3_2_CATEGORICAL_BINDER_RFC.md`](./TYPESCRIPT_ELABORATOR_V3_2_CATEGORICAL_BINDER_RFC.md)

Status: active semantic successor. The predecessor's canonical finite
displayed-natural telescope, grouped text, and reviewer route are final-green
at rollback-safe semantic/product checkpoint
`607a026f88bc6d3b9f305ecb21f6630ce7c94950`.
`COMPOSITIONAL-NATURAL-BINDER-0A` is complete as a read-only architecture
audit. The exact `COMPOSITIONAL-NATURAL-BINDER-1B` proposal below was frozen at
`7104ca8cc8c9c46187093ba2051dd80917cc31a3` and independently approved by
[`D-DTTLF-USABILITY-074`](./TYPESCRIPT_ELABORATOR_V3_2_COMPOSITIONAL_NATURAL_BINDER_D074_REVIEW.md).
The classifier-exact action correction was frozen at
`de900588d9961f3bb73d56ef7b1f535459c89015` and separately approved under
[`D-DTTLF-USABILITY-075`](./TYPESCRIPT_ELABORATOR_V3_2_COMPOSITIONAL_NATURAL_BINDER_D075_REVIEW.md)
at `36668e00b722ece632353f9636fb8bb083b1db5c`. The combined implementation is
focused-green: the reusable root ordinary-natural bracket reconstructs eta,
identity, recursive vertical composition, and both fixed whiskers through
existing active owners, rejects arbitrary point arrows, and leaves compact
`:^nd` unchanged. Its rollback-safe semantic checkpoint is pending the local
checkpoint operation recorded by this continuation.

## Objective

Determine and qualify a reusable ordinary-natural abstraction architecture:

```text
lambda^n a : A. body(a)
  : an object of Transf_cat(F,G)
```

The body must acquire naturality only by recursive construction from active
internal owners. It must never be accepted as a pointwise arrow plus external
naturality equations.

Once that ordinary abstraction is explicit, determine whether the existing
compact displayed-natural binder can lower compositionally through the
expanded natural telescope:

```text
lambda^nd a. body(a)

conceptual expansion
  k :^n K;
  a :^n E[k];
  body(k,a)
```

The target is a natural, scalable binder architecture, not merely a notation
rewrite. The audit must identify the exact classifier at each layer and prove
object, arrow, base-arrow, and higher-action behavior through the active
kernel.

## Clarified Current Status

The current implementation is sound but integrated rather than maximally
compositional:

1. `dependentLambda` exposes one `:^n` base token and constructs a dependent
   section for a reviewed eta/composition body algebra.
2. `displayedTransforLambda` exposes one base token whose body is already an
   indexed transformation and factors reviewed eta/composition forms back to
   one whole `Transfd`.
3. `displayedTransforContextLambda` implements compact `lambda^nd a` as one
   dedicated two-token algorithm. It literally creates:

   ```text
   aBase :^n K;
   a     :^n E[aBase]
   ```

   It checks an indexed-Hom body and recursively factors eta, identity,
   vertical composition, and fixed-head pre/postwhiskering into a closed
   `Transfd`. Its recorded abstraction evidence names both natural binders.
4. `displayedTransforDependentContextLambda` extends that integrated approach
   over arbitrary finite canonical sibling/Sigma layers.
5. `categoricalLambda` is the reusable ordinary **functorial** bracket. There
   is no corresponding public general ordinary-natural transformation bracket
   that can be invoked independently and then nested.

Thus all of the following are true at once:

- the inner natural variable and its action are genuinely understood;
- compact `:^nd` semantically represents the two-level natural telescope;
- no external naturality-square evidence is present; and
- compact `:^nd` is not currently implemented by composing two reusable
  public `:^n` abstractions.

The predecessor therefore graduates arbitrary finite canonical telescope
depth **within its reviewed factorer algebra**. It does not graduate arbitrary
compositional natural-transformation introduction.

## Expanded And Compact Classifier Presentations

The implementation review after D-075 sharpens the phrase “compositional
nesting.” Compact displayed binders and explicit nested binders should remain
distinct typed surface forms even when the kernel compares their result
classifiers.

For covariant directed families `E,D : K -> Cat`, the intended first-hom
presentations are:

```text
expanded:
  lambda^n k. lambda^f a. body(k,a)
    : Transf_cat K Cat_cat E D

compact:
  lambda^fd a. body(a)
    : Functord_cat E D
```

The active kernel owns a proof-time comparison between these category heads
and a runtime object projection from `Functord_cat` to `Transf_cat`. The inner
functorial abstraction is mathematically exact: the outer component has type
`Hom_cat Cat_cat E[k] D[k]`, which computes to
`Functor_cat E[k] D[k]`. The expanded form exposes the base variable and
retains the ordinary-transfor presentation; the compact form hides that base
variable, declares displayed dependency intrinsically, and retains the stable
displayed-functor head used by later displayed projections.

At the second hom, the corresponding canonical presentations are:

```text
expanded:
  lambda^n k. lambda^n a. body(k,a)
    : Hom_cat (Transf_cat K Cat_cat E D) FF GG

compact:
  lambda^nd a. body(a)
    : Transfd_cat E D FF GG
```

The active kernel again owns the direct proof-time second-hom comparison and
runtime object projection. This makes a compositional canonical implementation
semantically plausible without a new owner. It does **not** mean that the
current TypeScript methods already compose literally: `categoricalLambda`
accepts a fixed ordinary source category, `transforLambda` currently rejects
outer-slot capture, and the rich frontend does not yet join an open
`categorical-abstraction` with an `ordinary-natural-component` at target
`Cat_cat`.

`Functor_catd` and `Transf_catd` must not be conflated with those covariant
first- and second-hom facades. They are mixed-variance Cat-valued families:
their source family is over `Op K`, their target family is over `K`, and a
section of `Transf_catd` is not silently equal to a general `Transfd_cat`.
They remain separate classifier-specific consumers and stress tests.

The next compositional audit must therefore compare both `:^fd` and `:^nd`.
It may select literal public-method composition, a shared scoped contextual
abstraction engine with thin presentation-specific wrappers, or a hybrid. The
requirement is that explicit and compact syntax both recurse through
internally owned object/arrow/higher action and fail closed without it; literal
reuse of one public callback method by another is not itself a requirement.
Some reusable representation of scoped fibre categories and open component
classifiers is nevertheless necessary internally. Presentation-aware
packaging is necessary but not sufficient: the joint body compiler must prove
the inner functor or transfor's dependence on `k` by recursive construction.
The existing integrated compact factorers are the positive implementation
evidence for that joint compilation.

## Classifier Distinctions The Audit Must Preserve

The audit must not collapse four related but distinct active constructions:

| Construction | Active reading | Role in this plan |
|---|---|---|
| `Transf_cat F G` | ordinary category of transformations between ordinary functors | target classifier of the reusable inner `lambda^n a` bracket |
| `Functord_cat E D` | category of displayed functors between covariant families | its Hom computes to `Transfd_cat` |
| `Transfd_cat FF GG` | category whose objects are coherent displayed transformations | current compact `:^nd` result classifier and higher-action root |
| `Transf_catd A B FF GG` | mixed-variance Cat-valued family with fibre `Transf_cat(FF[k^-],GG[k])` | classifier for a distinct outer section experiment and a stress test of compositional nesting |

In particular, this plan does **not** presuppose a definitional equality:

```text
Transfd_cat FF GG
  =? Pi_cat (Transf_catd A B FF GG).
```

The source/target variance hypotheses differ. The exact relationship must be
derived from active owners, existing runtime computation, or an explicitly
qualified proof-time comparison. If no such general relationship exists, the
ordinary bracket can still be reusable while compact `:^nd` retains a thin
classifier-specific outer package.

## Settled Design Rules

1. Binder mode is intrinsic. `lambda^n` means natural abstraction; a type
   annotation may guide/check classifiers but does not create naturality.
2. Variables are object-level tokens that vary naturally. There is no
   separate user binder for an arrow token. Arrow and higher action are
   selected internally from classifiers and existing owners.
3. A natural bracket must fail closed on an arbitrary point arrow. Accepted
   bodies must be recursively factorable through coherence-owning operations.
4. Direct recursive binders remain fundamental. Curry, total-context sections,
   casts, and external equations are not prerequisites.
5. Runtime reduction and proof-time unification remain distinct. Do not use
   unrestricted proof-rule search to guess a classifier or naturality proof.
6. Existing integrated `:^nd` factorers remain rollback evidence until exact
   Core, type, and action parity demonstrates that a compositional route can
   replace or delegate to them.
7. Formation/elimination recursion already graduated in the recursive-mixed
   plan. This plan addresses **introduction**; it must not reimplement the
   generic Hom-category reifier or action ladder.
8. No new Lambdapi owner is justified until the audit proves that the active
   generic `Transf_cat`, `tapp*`, `Hom_catd`, `Transf_catd`, `Functord_cat`,
   `Transfd_cat`, and internal action owners cannot express one exact positive
   consumer.

## Candidate Architecture

The preferred candidate, subject to the audit, is a reusable typed method
schematically shaped as:

```text
transforLambda(
  name,
  sourceCategory A,
  sourceFunctor F,
  targetFunctor G,
  a => body(a)
) : transformation F G
```

Its recursive body compiler should begin with the constructions already
qualified by the displayed factorer:

- eta/application of an already coherent transformation;
- identity;
- typed vertical composition;
- fixed-head prewhiskering;
- fixed-head postwhiskering; and
- generic applications whose classifier selects an existing natural action.

The implementation should reuse one typed natural-transformation IR/factorer
where possible. Uniform code is not itself a requirement: a small
classifier-specific outer package is acceptable if the mathematical
constructions differ. The requirement is a natural, generalizable
architecture without duplicated end-to-end shape hacks.

For compact displayed abstraction, the candidate comparison is:

```text
current integrated:
  lambda^nd a. eta[a]

candidate compositional reading:
  lambda^n k. (lambda^n a. eta[k][a])
```

The audit must determine the exact Core/API representation of the outer layer
rather than assuming it is literally the current `dependentLambda` call.

## `COMPOSITIONAL-NATURAL-BINDER-0A` Audit Result

The read-only audit selects **shared natural-component construction IR with
distinct ordinary and displayed outer compilers**. It does not select a new
kernel construction and does not yet refactor compact `:^nd`.

### Existing semantic authority

The active kernel already supplies the complete semantic ladder needed by the
first ordinary binder slice:

- `Transf_cat F G` and its object classifier;
- `tapp0_fapp0` for a point component;
- `tapp1_func`/`tapp1_fapp0` and the next Hom action;
- generic category identity and vertical composition;
- fixed precomposition through `comp_cat_con_func`; and
- fixed postcomposition through the existing `hom_postcomp_func`
  specialization used by `comp_cat_cov_func`.

The required owners are already present in the maximal reviewed TypeScript
runtime lineage. No Lambdapi declaration, rewrite rule, unification rule, or
transfer declaration is missing for the selected slice.

### Exact TypeScript seam

The backend-neutral TypeScript Core already has a rich `transfor` type, maps it
to `transfor-category`, checks closed ordinary components, and carries generic
ordinary transformation action owners. The scoped categorical API lacks:

1. a public rich ordinary-transformation assumption facade;
2. a reusable ordinary-natural abstraction method; and
3. a construction-only classifier for a component whose index is a locally
   nameless open categorical slot.

The existing code marks this seam precisely. A closed component succeeds, but
the same component at an open ordinary slot raises
`MISSING_STRUCTURAL_OWNER` with:

```text
Open ordinary transfor components require later contextual naturality lowering
```

This is a frontend introduction gap, not a kernel inconsistency and not a need
for external naturality evidence.

### Classifier result

The active kernel explicitly documents sections of the mixed family as:

```text
Pi_cat (Transf_catd A B FF GG).
```

The existing TypeScript API can construct the corresponding family and a
section assumption. This remains a legitimate mixed-section presentation,
distinct from `Transfd_cat`. Existing tests already exercise fixed
`Transf_catd` contextual object/arrow action. The audit therefore rejects both
of these shortcuts:

- equating `Pi_cat(Transf_catd ...)` with `Transfd_cat`; and
- making the new ordinary bracket depend on that equation.

### Disposable probe evidence

A disposable builder probe established:

- closed `eta[x]` synthesizes the expected rich `hom` classifier and explicit
  `tapp0_fapp0` Core;
- replacing closed `x` by the current ordinary contextual token reaches the
  exact intentional `MISSING_STRUCTURAL_OWNER` seam above; and
- an actual `Transf_catd` section is constructible through the existing mixed
  API. Its full maximal-profile checker probe was stopped after two minutes to
  respect the bounded-validation SOP; the already-checkpointed focused
  `Transf_catd` action test remains the validation authority rather than
  starting another long aggregate-like run.

## Frozen `COMPOSITIONAL-NATURAL-BINDER-1B` Proposal

Gate: `H-DTTLF-USABILITY-COMPOSITIONAL-NATURAL-01`

Decision: `D-DTTLF-USABILITY-074`

### Public typed API

Add, under one explicit continuation profile:

```text
transfor(name, F, G)
  : Transf_cat F G

transforLambda(name, F, G, a => body(a))
  : Transf_cat F G
```

The source and target categories are inferred from closed rich functor
endpoints. Binder mode is intrinsically natural; options may check plicity,
polarity, cell level, and dependency but cannot turn another binder mode into
natural abstraction.

### Construction-only natural component

Add one locally nameless frontend classifier recording:

```text
ordinary-natural-component
  source category X
  target category B
  whole source functor P : X -> B
  whole target functor Q : X -> B
  active natural index ordinal
```

It represents the open point Hom `P[a] -> Q[a]`. It is immutable inspection
data only. It cannot reach explicit Core, cannot be supplied with a naturality
equation, and must be eliminated by the enclosing `transforLambda`.

### Recursive body algebra

The first slice accepts exactly:

1. `eta[a]`, recovering `eta` exactly;
2. `eta[L[a]]`, recovering fixed prewhiskering through the existing
   precomposition functor and generic Hom action;
3. `H(component)`, recovering fixed postwhiskering through the existing
   postcomposition functor and generic Hom action;
4. `id(P[a])`, where the existing ordinary contextual compiler first recovers
   `P : X -> B`; and
5. typed recursive vertical composition of two accepted components.

The ordinary contextual compiler remains the authority for functorially
factoring object expressions. The natural factorer adds only the inverse
component-to-transformation step. Arbitrary point arrows, unsupported open
classifiers, captured outer slots, and mismatched endpoints fail closed.

### Exact Core output

The factorer emits only existing explicit Core:

- the original coherent transformation for eta;
- generic `id` at `Functor_cat X B`;
- generic `comp_fapp0` at `Functor_cat X B`;
- generic `fapp1_fapp0` of existing `comp_cat_con_func`; and
- generic `fapp1_fapp0` of the existing `hom_postcomp_func` specialization.

No new Core node, checker branch, runtime rule, declaration-refinement
facility, kernel owner, cast, coercion, curry, or external coherence payload is
authorized.

## Frozen `COMPOSITIONAL-NATURAL-ACTION-CORRECTION-1B2` Proposal

Gate: `H-DTTLF-USABILITY-COMPOSITIONAL-NATURAL-ACTION-CORRECTION-01`

Decision: `D-DTTLF-USABILITY-075`

The first focused generic-checker run accepts eta, identity, recursive
composition, arbitrary-arrow rejection, scope hygiene, and the predecessor
compact `:^nd` eta route. It rejects the generic prewhiskering expression with
a `Hom`-classifier versus `Transf`-classifier endpoint mismatch. Exact source
inspection identifies a transfer-presentation gap rather than missing
mathematics:

- Lambdapi defines `comp_cat_con_func` and the corresponding generic Hom
  action transparently, so its action can normalize to canonical
  `comp_cat_fapp0` endpoints there;
- the TypeScript transfer intentionally imports `comp_cat_con_func` as an
  opaque signature, so generic `fapp1_fapp0` retains opaque
  `fapp0(comp_cat_con_func(...), ...)` endpoints; and
- the active kernel already owns classifier-exact action functors
  `comp_cat_con_fapp1_func` and `comp_cat_cov_fapp1_func`, whose target
  `Transf_cat` endpoints are stated directly with `comp_cat_fapp0`.

Correct only the two whiskering branches by importing those two existing
owners as opaque checked signatures and applying them through generic object
application. Eta, identity, composition, and compact `:^nd` remain unchanged.
The correction adds:

1. one signatures-only transfer fragment with exactly the two active owners;
2. no runtime or proof rule, transparent-definition mirror, checker branch,
   Core node, new Lambdapi owner, or kernel edit; and
3. focused declaration-boundary assertions plus generic checker acceptance of
   both canonical whiskering endpoints.

This correction supersedes only the D-074 implementation detail saying that
the first TypeScript slice emits generic Hom action of the opaque facades. It
does not weaken the architectural result: both branches still reconstruct
internally coherent active-kernel transformations without an external
naturality payload.

### Files and tests

Behavior edits are limited to:

- `src/v3_2/categorical_surface.ts`;
- `src/v3_2/categorical_program.ts`;
- one focused `tests/v3_2_categorical_compositional_natural_binder_tests.ts`;
- `tests/main_tests.ts` only if required by runner discovery; and
- the owning plan/handoff ledgers.

Focused evidence must cover eta exactness, identity, recursive composition,
both whiskering orientations, arbitrary-arrow rejection, escaped/foreign
scope rejection, callback single evaluation, deep freezing, generic checker
acceptance, closed component elimination, and preservation of the existing
compact `:^nd` eta route. Existing `Transf_catd` section/action and
`Transfd_cat` higher-action tests are carried forward; this slice must not
rewrite those classifiers or factorers.

Validation is limited to the new focused test, the nearest existing
ordinary/displayed surface tests, root typecheck, lint, exact diff hygiene,
and—because this changes the shared scoped frontend and public program—a
single root `check:ts` only after the bounded tranche is otherwise green.
Recent kernel/browser/print/book evidence is carried forward. No kernel CI,
browser, print, book, or repository aggregate is authorized.

## Read-Only `COMPOSITIONAL-NATURAL-BINDER-0A` Audit

This row changes no behavior. It must:

1. Inventory active Lambdapi owners and rules for ordinary transformations:
   `Transf_cat`, its object classifier, generic identities/composition,
   `tapp0*`, `tapp1*`, and ordinary pre/postwhiskering.
2. Inventory the exact TypeScript rich types, applications, assumptions,
   reifiers, and factorers for ordinary transformations. Determine whether a
   new public method can return an existing type without a new Core node or
   checker branch.
3. Trace `dependentLambda`, `displayedTransforLambda`,
   `displayedTransforContextLambda`, and
   `displayedTransforDependentContextLambda` into their current lowerers.
   Identify genuinely shared recursion and duplicated classifier-specific
   recovery.
4. Audit the exact active relationships among `Hom_catd`, `Transf_catd`,
   `Functord_cat`, and `Transfd_cat`, including the already-transferred base
   and higher actions. Do not infer equality from similar fibre formulas.
5. Build disposable TypeScript probes, using existing profiles only, for:

   - `lambda^n a. eta[a]` at one ordinary `Transf_cat`;
   - identity, vertical composition, and both whiskering orientations;
   - the current compact `lambda^nd a. eta[a]` and its expanded contextual
     evidence;
   - one well-typed section over an actual `Transf_catd` family; and
   - one `Transfd_cat` Hom/higher-action consumer.

6. For each probe, inspect object component, ordinary arrow/naturality action,
   outer base-arrow action when indexed, and the next higher action. A point
   equality alone is insufficient.
7. Compare three implementation alternatives:

   - extract a generic ordinary-natural factorer and let compact `:^nd`
     delegate compositionally;
   - share a typed natural-body IR while retaining distinct ordinary and
     displayed outer compilers; or
   - retain the integrated factorer and add only a standalone ordinary
     abstraction if exact classifier composition is not available.

8. Select at most one bounded semantic implementation slice. Freeze its exact
   public API, files, tests, positive/negative behavior, validation, and
   non-effects under a separate review gate before editing behavior.

Disposable probes must be bounded and removed or kept only in ignored
temporary space. Do not run the root aggregate, kernel CI, browser, print, or
book gates during this audit.

## Required First Implementation Evidence

Any later implementation proposal must include at least:

1. ordinary eta:

   ```text
   lambda^n a. eta[a] == eta
   ```

2. ordinary identity, recursive vertical composition, prewhiskering, and
   postwhiskering;
3. rejection of an arbitrary point arrow with no internal naturality owner;
4. exact callback scoping, use counts, and no retained JavaScript callback;
5. generic checker validation of unchanged backend-neutral Core;
6. a compact-versus-compositional displayed comparison where the active
   classifiers make it well-typed;
7. one genuine `Transf_catd` outer-section consumer, kept distinct from
   `Transfd_cat` unless the kernel establishes a comparison;
8. object, arrow, base-arrow, and higher-action observations; and
9. preservation of the existing final-green compact/telescope behavior and
   its fail-closed boundary.

## Work Ledger

| Slice | Status | Dependency | Exact boundary |
|---|---|---|---|
| `CONTEXTUAL-ND-TELESCOPE-REVIEWER-1AP` | final-green at `607a026f88bc6d3b9f305ecb21f6630ce7c94950` | D-070 through D-073 | Typed canonical finite `:^nd`, grouped text, lean chain-2A reviewer preset, production/browser evidence, and effective aggregate qualification. |
| `COMPOSITIONAL-NATURAL-BINDER-0A` | complete; read-only | final-green 1AP; user-approved architectural direction | Existing semantic ladder and rich Core are sufficient; exact gap is open ordinary-component lowering. `Pi_cat(Transf_catd)` remains distinct from `Transfd_cat`. |
| `COMPOSITIONAL-NATURAL-BINDER-1B` | implementation final-focused-green; semantic checkpoint pending | completed 0A; D-074 and D-075 | Rich `transfor` assumptions and reusable root `transforLambda` pass eta, identity, recursive composition, both whiskers, arbitrary-arrow rejection, scope/callback/immutability, closed elimination, generic checking, and compact-`:^nd` preservation. The first slice deliberately rejects an outer contextual capture. |
| `COMPOSITIONAL-NATURAL-ACTION-CORRECTION-1B2` | implemented final-focused-green; semantic checkpoint pending | focused 1B failure; D-075; existing `comp_cat_con_fapp1_func` and `comp_cat_cov_fapp1_func` | Imports exactly two existing classifier-exact action signatures and uses them for pre/postwhiskering. Adds zero rules, kernel owners, Core nodes, checker branches, or external coherence fields. |
| `COMPOSITIONAL-NATURAL-BINDER-GRADUATE-0C` | dependency-ready read-only successor after checkpoint | completed 1B/1B2 | Compare canonical expanded `Transf_cat`/iterated-Hom presentations with compact `Functord_cat`/`Transfd_cat` for both `:^fd` and `:^nd`; select one shared contextual architecture and freeze exact body/classifier/variance non-claims before text or browser promotion. Keep mixed `Functor_catd`/`Transf_catd` distinct. |
| `COMPOSITIONAL-NATURAL-TEXT-PARITY-1D` | deferred | graduated direct typed API | Add text syntax only after the target mathematical AST/API is settled. |

## Explicit Non-Claims

This plan does not yet claim or authorize:

- an arbitrary pointwise function becoming a natural transformation;
- unrestricted body synthesis or ordinary-DTT-like occurrence completeness;
- a global equality between `Transfd_cat` and a section of `Transf_catd`;
- arbitrary dependency/variance DAGs, exchange across dependency, or every
  polarity alternation;
- a new curry, total-context section argument, product facade, cast, coercion,
  or external naturality/coherence payload;
- a new Lambdapi owner, rewrite rule, or unification rule;
- a second parser, text behavior, browser preset, book change, scale resumption,
  or whole-library transfer graduation; or
- push, merge, rebase, amend, reset, publication, deployment, worktree
  removal, or unrelated cleanup.

## Validation And Checkpoint Policy

`COMPOSITIONAL-NATURAL-BINDER-0A` is read-only. Use exact source inspection,
bounded disposable probes, document/link hygiene, and `git diff --check`.
Run a bounded active-kernel check only when a probe depends on current kernel
names or computation, and keep it within the nested SOP timeout. Do not rerun
the 52-minute TypeScript aggregate.

Any later behavior slice must have a separately frozen/reviewed validation
matrix. Use focused tests and typecheck/lint first. Run a root aggregate only
if the eventual shared-behavior delta independently requires it at a new
checkpoint boundary; carry forward unchanged evidence whenever possible.

The combined D-074/D-075 implementation has the following final proportional
evidence:

- root workspace check, typecheck, and the complete changed-file lint pass;
- exact diff hygiene and the bounded active-kernel check pass;
- the focused compositional-natural suite passes 6/6, covering the exact
  two-signature/no-rule boundary, eta, identity, recursive composition, both
  whiskers, arbitrary-arrow rejection, scope/callback/immutability, closed
  component elimination, generic checker acceptance, and compact-`:^nd`
  preservation; and
- the single root `check:ts` was run once. Its shared behavior reached the
  new suite without a semantic failure; the command remained non-green only
  on pre-existing active-kernel source-digest pins and the public README's
  line-wrapped `Hom-category recursion` assertion. Those unrelated historical
  contracts are not repaired in this semantic tranche, and the aggregate must
  not be repeated for this unchanged boundary.

Use rollback-safe local checkpoints under
[`PERSISTENT_GOAL_GIT_EXPERIMENTATION.md`](./PERSISTENT_GOAL_GIT_EXPERIMENTATION.md).
Preserve unrelated work.

## Persistent `/goal` Launch Prompt

Continue the living TypeScript/emdash v3.2 objective from
`docs/TYPESCRIPT_ELABORATOR_V3_2_HANDOFF.md` and this plan. Recover the actual
goal worktree, active kernel/SOP, completed checkpoints, decision ledger, and
current dependency-ready row on every continuation.

Treat the predecessor canonical finite `:^nd` typed/text/reviewer envelope as
final-green at `607a026f88bc6d3b9f305ecb21f6630ce7c94950`. Preserve its
integrated factorers as sound rollback evidence. Treat
`COMPOSITIONAL-NATURAL-BINDER-0A` as complete: the kernel/rich Core action
ladder exists and the exact missing seam is open ordinary-component
introduction. Distinguish semantic expansion of compact `:^nd` from actual
composition of reusable public `:^n` constructors. Do not assume
`Transfd_cat` equals a section of `Transf_catd`.

Treat `COMPOSITIONAL-NATURAL-BINDER-1B` and its classifier-exact D-075
correction as final-focused-green after their rollback-safe semantic
checkpoint. Continue with read-only
`COMPOSITIONAL-NATURAL-BINDER-GRADUATE-0C`. Compare the canonical expanded
`Transf_cat`/iterated-Hom route with compact `Functord_cat`/`Transfd_cat` for
both `:^fd` and `:^nd`; do not conflate that route with mixed
`Functor_catd`/`Transf_catd`. Natural transformation bodies must be recursively
constructed from internal owners and fail closed without them. Keep the
existing compact factorers unchanged until exact parity supports a later
delegation decision. Preserve object, arrow, base-arrow, and higher action;
add no curry, cast, total-context section, external coherence, new kernel
owner, text/browser behavior, or scale work without a separate reviewed gate.

Use proportional validation and rollback-safe local checkpoints. Preserve
unrelated work. Do not push, merge, rebase, amend, reset, publish, deploy,
remove worktrees, or perform unrelated cleanup without exact authorization.

## Decision Ledger

- **2026-08-02 — D-DTTLF-USABILITY-075 approved and implemented.** A separate
  immutable review at `36668e00b722ece632353f9636fb8bb083b1db5c` approves
  exactly the two existing classifier-exact action signatures. The final
  focused suite passes 6/6; both whiskers are accepted by the generic checker,
  and the transfer adds no rule or mathematical owner. The one shared root
  aggregate was not repeated after reporting only existing source-digest and
  README-wrap contracts outside this tranche.
- **2026-08-02 — canonical expanded/compact distinction clarified.** Explicit
  `lambda^n k. lambda^f a` and compact `lambda^fd a` retain respectively the
  `Transf_cat` and `Functord_cat` facades; explicit
  `lambda^n k. lambda^n a` and compact `lambda^nd a` retain the iterated-Hom
  and `Transfd_cat` facades. The active kernel owns their canonical proof-time
  comparisons. Mixed `Functor_catd`/`Transf_catd` remain distinct. The next
  read-only graduation audit must compare both modes and may select a shared
  internal contextual compiler without requiring literal public-method
  nesting.
- **2026-08-02 — H-DTTLF-USABILITY-COMPOSITIONAL-NATURAL-ACTION-CORRECTION-01
  proposal frozen.** The first focused checker run passes four of five test
  groups and isolates the remaining failure to generic Hom action through an
  opaquely imported composition facade. The active kernel already provides
  the classifier-exact `comp_cat_con_fapp1_func` and
  `comp_cat_cov_fapp1_func`; D-075 proposes importing only those two opaque
  signatures, with no rules or semantic delta.
- **2026-08-02 — D-DTTLF-USABILITY-074 approved.** A separate review of
  proposal checkpoint `7104ca8cc8c9c46187093ba2051dd80917cc31a3` confirms
  that the construction-only classifier adds no LF semantics and that all five
  positive branches reconstruct existing internal owners. The standing
  unattended-review delegation approves exact 1B implementation while
  preserving compact `:^nd` and all classifier distinctions.
- **2026-08-02 — H-DTTLF-USABILITY-COMPOSITIONAL-NATURAL-01 proposal frozen.**
  The read-only audit finds no missing kernel semantics. D-074 proposes one
  construction-only ordinary natural-component classifier and a reusable
  `transforLambda` whose eta, identity, composition, prewhiskering, and
  postwhiskering cases emit existing Core owners. Compact `:^nd`,
  `Transf_catd`, and `Transfd_cat` remain unchanged pending an independent
  review.
- **2026-08-02 — compositional natural-binder direction selected.** The user
  confirms that the highest-yield usability gap is a reusable ordinary
  `lambda^n a` abstraction from which compact displayed-natural binding can be
  compositionally understood when classifiers permit. The current `:^nd`
  factorer remains sound but integrated. This plan records a read-only audit,
  not an implementation authorization.
- **2026-08-02 — predecessor reviewer route final-green.** D-070 through D-073
  are checkpointed at `607a026f88bc6d3b9f305ecb21f6630ce7c94950`.
  Focused Core/reviewer tests, typecheck/lint, the production fixture, and real
  browser are green. The sole aggregate ran 52.2 minutes and reported only the
  stale literal-eleven source assertion corrected by focused 1/1 D-073
  evidence; it must not be repeated for this unchanged boundary.
