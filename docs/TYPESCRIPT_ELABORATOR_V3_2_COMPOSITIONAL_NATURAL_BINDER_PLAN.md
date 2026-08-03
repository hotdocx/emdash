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
`:^nd` unchanged. Its exact rollback-safe semantic checkpoint is
`a0c8c7a77a310ded8c972d2308e47f27c3a8c25d`.
The expanded first-hom proposal was frozen at
`5929b2962ea6fe3465047556f9992bab4a827971` and independently approved under
[`D-DTTLF-USABILITY-076`](./TYPESCRIPT_ELABORATOR_V3_2_COMPOSITIONAL_NATURAL_BINDER_D076_REVIEW.md).
Its implementation is final-focused-green at rollback-safe semantic checkpoint
`9a997edb6a34ddc3310f1a9db7e5db8bdd52c8e1`. Literal typed
`lambda^n k. lambda^f a` now shares the
compact `:^fd` recursive factorer and emits byte-identical Core while retaining
the ordinary `Transf_cat` facade.
The read-only `COMPOSITIONAL-ND-EXPANDED-1D` audit is complete. It finds no
missing kernel owner and selects the existing open `indexed-functor` view plus
the compact point factorer as the second-hom seam. The exact bounded proposal
below is frozen at `f176d08b9aa831b05241ef301475379d78e32939` under
`H-DTTLF-USABILITY-COMPOSITIONAL-ND-EXPANDED-01` and independently approved by
[`D-DTTLF-USABILITY-077`](./TYPESCRIPT_ELABORATOR_V3_2_COMPOSITIONAL_NATURAL_BINDER_D077_REVIEW.md).
Its bounded implementation is final-focused-green at rollback-safe semantic
checkpoint `b89420d442536544185e8ab5dbe6876bd9980b96`. Literal typed
`lambda^n k. lambda^n a` now shares the
compact `:^nd` point factorer and byte-identical Core while retaining the
ordinary iterated-Hom facade and delegating component, point, base-arrow, and
higher action to the recovered coherent `Transfd` owner.
The read-only `COMPOSITIONAL-NATURAL-TEXT-PARITY-1D` audit is complete. The
located grammar already represents both expanded nested forms and the neutral
body resolver already covers their reviewed operations. The only missing seam
is expected-classifier-directed routing into the checkpointed typed methods.
The exact adapter-only proposal below is frozen under
`H-DTTLF-USABILITY-COMPOSITIONAL-TEXT-PARITY-01` at
`19ec1adb1bd2ee3288338e7069759549c1f282a8` and independently approved by
[`D-DTTLF-USABILITY-078`](./TYPESCRIPT_ELABORATOR_V3_2_COMPOSITIONAL_NATURAL_BINDER_D078_REVIEW.md).
Its exact adapter implementation is final-focused-green at rollback-safe
semantic checkpoint `7f7d201948e5f035e516f6fb15554a1aea26029d`.

The read-only `CLASSIFIER-DIRECTED-FUNCTOR-BRACKET-0E` audit is complete. It
finds that the desired consolidation is feasible, but at a more precise
boundary than a universal fixed/open compiler. The fixed-category
`compileContextual` and displayed `compileDisplayedContextual` backends are
both recursive and internally action-owning, but accept materially different
body algebras. Meanwhile, the existing one-binding `displayedContextLambda`
already uses the richer displayed backend and produces byte-identical Core and
types to compact `displayedFunctorLambda` for identity, eta, composition, and
qualified weakening. The selected next candidate is therefore a bounded
read-only scope audit for reusing that existing displayed backend from the
compact and open-displayed wrappers. No behavior refactor is yet authorized.

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

## `COMPOSITIONAL-NATURAL-BINDER-GRADUATE-0C` Audit Result

The audit selects a **shared scoped contextual engine with literal typed
nesting and thin facade-specific result wrappers**. This is a hybrid only at
the presentation boundary: the body is compiled once by construction from
internal owners, while expanded and compact syntax retain their distinct
active category heads.

### Kernel result

No mathematical owner is missing. The active kernel supplies both canonical
comparisons and their runtime object projections:

```text
Transf_cat K Cat_cat E D
  =proof-time Functord_cat E D

Obj(Functord_cat E D)
  -> Obj(Transf_cat K Cat_cat E D)

Hom_cat (Transf_cat K Cat_cat E D) FF GG
  =proof-time Transfd_cat E D FF GG

Obj(Transfd_cat E D FF GG)
  -> Obj(Hom_cat (Transf_cat K Cat_cat E D) FF GG).
```

Consequently the two introduction pairs are semantically feasible without a
cast, curry, total-context section, or external coherence field:

```text
lambda^n k. lambda^f a. body(k,a)
  : Transf_cat K Cat_cat E D

lambda^fd a. body(a)
  : Functord_cat E D

lambda^n k. lambda^n a. body(k,a)
  : Hom_cat (Transf_cat K Cat_cat E D) FF GG

lambda^nd a. body(a)
  : Transfd_cat E D FF GG.
```

The inner `lambda^f a` is exactly the arrow in `Cat_cat` required by the
outer first-hom component: `Hom_cat Cat_cat E[k] D[k]` computes to
`Functor_cat E[k] D[k]`. At the second hom, the inner `lambda^n a` is the
fibre natural transformation between `FF[k]` and `GG[k]`; the joint outer
compiler must retain its base action rather than accepting an arbitrary
pointwise family.

### TypeScript result

Literal composition of the current public methods is not yet possible:

- `CoreCategoricalCategory` carries a closed `KernelExpression`; it has no
  scoped representation for the open fibre `E[k]`;
- public `fibre(E,k)` deliberately rejects an open contextual token;
- `categoricalLambda` therefore accepts only fixed ordinary categories; and
- the first `transforLambda` deliberately rejects capture of an already-active
  outer slot.

Those are representation boundaries, not semantic counterexamples. The
compact `displayedFunctorLambda` and `displayedTransforContextLambda` already
create the required hidden two-token contexts and recursively recover whole
coherent owners. The correct refactor seam is therefore their scoped
body-factorization logic, not their final rich classifier.

The selected internal architecture has three layers:

1. a construction-only scoped fibre-category descriptor containing the active
   base ordinal, base category, and displayed family;
2. one shared recursive two-token factorer per mathematical binder level,
   eliminating every locally nameless token before explicit Core; and
3. thin wrappers retaining either the expanded ordinary facade or the compact
   displayed facade.

The intended convergence after both expanded levels graduate is therefore:

```text
shared scoped functorial compiler(k,a,body)
  -> expanded wrapper : Transf_cat K Cat_cat E D
  -> compact wrapper  : Functord_cat E D

shared scoped natural-component compiler(k,a,body)
  -> expanded wrapper : Hom_cat (Transf_cat K Cat_cat E D) FF GG
  -> compact wrapper  : Transfd_cat E D FF GG.
```

“Reuse” means that both wrappers invoke the same internal recursive
factorization and emit the same Core term. It does not require the compact API
to invoke the public expanded callback method literally: the compact API must
still hide `k`, record displayed-binder inspection evidence, and retain the
stable displayed facade required by downstream projections. Existing compact
factorers remain rollback evidence until same-Core, same-action parity is
proved before delegation or replacement.

The descriptor is not a `KernelExpression`, cannot be assumed as a closed
category, cannot escape its callback, and cannot reach the generic checker.
This avoids a placeholder free variable or frontend cast while allowing the
typed TypeScript AST to mirror literal nested binders.

### Disposable facade probe

One bounded no-file TypeScript probe used the existing
`compositional-natural-binder-1` profile. It compiled compact eta witnesses,
then rechecked their **unchanged terms** under the expanded rich types:

- compact `:^fd` as rich `transfor` at
  `Transf_cat K Cat_cat E D`; and
- compact `:^nd` as rich `hom` at
  `Hom_cat (Transf_cat K Cat_cat E D) FF GG`.

Both generic checks succeeded and both expanded terms were byte-for-byte the
same explicit Core as their compact terms. The serialized inferred and
expected types remained different presentations, as required. The existing
second-hom compatibility additionally reported runtime category
`not-equal`, proof-time `solved`, and runtime object classifiers `equal`.
The probe took about seven minutes in the maximal profile and must not be
repeated; it replaces, rather than motivates, another aggregate run.

### Alternative disposition

- **Literal current-method composition without scoped classifiers:** rejected;
  it cannot represent `E[k]` and would force a fake closed expression.
- **Only a combined convenience callback:** rejected as the final
  architecture; it would preserve the integrated implementation rather than
  make direct recursive binders fundamental.
- **A fully general open-category calculus immediately:** deferred; the first
  consumer needs only fibre categories owned by a displayed family at the
  active natural token.
- **Selected hybrid:** expose literal typed nesting for the qualified fibre
  case, share the compact recursive factorer, and retain expanded/compact
  classifier facades separately.

## Frozen `COMPOSITIONAL-FD-EXPANDED-1C` Proposal

Gate: `H-DTTLF-USABILITY-COMPOSITIONAL-FD-EXPANDED-01`

Decision:
[`D-DTTLF-USABILITY-076`](./TYPESCRIPT_ELABORATOR_V3_2_COMPOSITIONAL_NATURAL_BINDER_D076_REVIEW.md)
approved from immutable proposal checkpoint
`5929b2962ea6fe3465047556f9992bab4a827971`

### Exact typed surface

Under the existing explicit continuation profile, add the qualified literal
typed composition:

```typescript
emdash.transforLambda('k', E, D, k =>
    emdash.lambda(
        'a',
        emdash.fibre(E, k),
        emdash.fibre(D, k),
        a => body(k, a)
    )
)
```

Its surface result is an ordinary `transfor` with category
`Transf_cat K Cat_cat E D`. The existing compact call remains:

```typescript
emdash.displayedFunctorLambda('a', E, D, a => body(a))
```

with surface result `displayed-functor` at `Functord_cat E D`.

Implement this by:

1. overloading `fibre` for an active `CoreCategoricalSlotToken` to return one
   construction-only scoped fibre category;
2. routing `lambda` over two compatible scoped fibre categories to one
   contextual functorial abstraction;
3. allowing `transforLambda` parallel displayed-family endpoints as the exact
   `K -> Cat_cat` outer classifier; and
4. extracting the existing compact `:^fd` identity/eta/finite-chain/qualified-
   weakening factorization into one shared internal helper, with separate
   expanded `transfor` and compact `displayed-functor` wrappers.

The expanded wrapper may recover the ordinary facade only after the shared
factorer has produced a closed coherent displayed functor. It may not accept a
point functor merely because its endpoints look like `E[k]` and `D[k]`.

### Required evidence

Focused tests must establish:

1. expanded eta has surface type `transfor`, generic-checks, and emits exactly
   the same Core term as compact `:^fd` eta;
2. expanded identity and a two-step displayed-functor chain use the same
   shared factorer and agree with their compact counterparts;
3. applying the expanded result at a closed base object exposes the expected
   fibre functor, whose object and arrow action agree with the compact result;
4. the outer ordinary naturality action is observable through existing
   `tapp1*`/generic Hom action, without an external square;
5. callback evaluation is once, inspections are deeply frozen, and open fibre
   descriptors/tokens cannot escape or cross program instances;
6. mismatched families, mismatched base ordinals, a non-fibre scoped category,
   and an arbitrary unfactored body fail closed; and
7. existing compact `displayedFunctorLambda`, root ordinary
   `transforLambda`, and compact `displayedTransforContextLambda` behavior is
   unchanged.

### Files, validation, and non-effects

Behavior edits are limited to:

- `src/v3_2/categorical_surface.ts`;
- `src/v3_2/categorical_program.ts`;
- one focused
  `tests/v3_2_categorical_compositional_fd_expanded_tests.ts`;
- `tests/main_tests.ts` only if discovery requires it; and
- this plan and the handoff.

Run the focused new test, the nearest compact `:^fd` and ordinary-natural
tests, workspace check, typecheck, changed-file lint, and exact diff hygiene.
Because the shared scoped frontend changes, run one root `check:ts` only after
the bounded tranche is otherwise green, carrying forward already recorded
unrelated digest/README failures and never repeating it for the same boundary.
No kernel CI, browser, print, book, or repository aggregate is authorized.

This slice adds no explicit Core node, generic checker branch, runtime or
proof rule, transfer declaration, Lambdapi edit/owner, placeholder open
`KernelExpression`, curry, cast, coercion, total-context section, external
coherence payload, text syntax, browser behavior, or second-hom expanded
`lambda^n k. lambda^n a` implementation. The second-hom bridge is the
dependency-ready semantic successor if this first-hom architecture is green.

## `COMPOSITIONAL-FD-EXPANDED-1C` Implementation Result

The reviewed architecture is implemented without a kernel or explicit-Core
delta:

1. `fibre(E,k)` returns a branded construction-only scoped fibre category
   when `k` is an active ordinary-natural token. The descriptor contains no
   `KernelExpression`, cannot compile as a closed category, and fails after
   its callback or across program instances.
2. `lambda(a,E[k],D[k],body)` creates the fibre token and delegates identity,
   eta, finite chain, and qualified weakening to the exact helper now shared
   with compact `displayedFunctorLambda`.
3. `transforLambda(k,E,D,...)` retains the expanded
   `Transf_cat K Cat_cat E D` rich type and the shared factorization metadata,
   while its explicit term is byte-identical to compact `Functord_cat E D`.
4. Closed component elimination refines the `Hom_cat Cat_cat` result to the
   expected fibre functor, so object and fibre-arrow action remain iterable.
   The existing outer `tapp1` action is observed through the byte-identical
   compact displayed-functor owner. The separately reserved general ordinary-
   transfor Hom-boundary API is not widened in this slice.

The focused matrix is effectively five of five green. The first full focused
run passed eta/Core parity, identity/chain parity, all negative cases, and
root/compact preservation; it exposed only a misplaced wrapper-metadata
argument in the action group. After the local correction, the formerly
failing closed fibre object/arrow/base-arrow action group passed in isolation.
No semantic group was rerun for reassurance.

Workspace validation, root typecheck, complete changed-file lint, and exact
diff hygiene pass. The mandated root `check:ts` was run exactly once: its
workspace, typecheck, and lint phases pass, and the new behavior reaches the
root runner without a feature failure. The aggregate remains non-green only
on unrelated stale active-kernel digest/source-position and declaration-count
pins plus the already recorded README line-wrap assertion. Those contracts
are outside this semantic tranche, and the aggregate must not be repeated for
this unchanged boundary.

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

## `COMPOSITIONAL-ND-EXPANDED-1D` Audit Result

The second-hom audit finds a representation gap, not a mathematical or kernel
gap.

### Existing authority and reusable machinery

The active kernel already owns all four required boundaries:

```text
Hom_cat (Transf_cat K Cat_cat E D) FF GG
  =proof-time Transfd_cat E D FF GG

Obj (Transfd_cat E D FF GG)
  ->runtime Obj (Hom_cat (Transf_cat K Cat_cat E D) FF GG)

tdapp0_fapp0 k epsilon
  : Transf_cat (FF[k]) (GG[k])

tdapp1_int_cell epsilon p u
  : the internally transported base-arrow/higher cell.
```

No new owner, comparison, action rule, or coherence field is required.
`Hom_catd` and `Transf_catd` remain the separate mixed-variance family
classifiers; neither is used as a replacement for this canonical covariant
second hom.

The TypeScript frontend also already has the required recursive compiler:

1. applying a closed displayed functor `FF` to an active base token `k`
   produces a construction-only `indexed-functor` for `FF[k]` whose closed
   displayed owner remains recoverable;
2. `factorDisplayedTransforPoint` eliminates one natural base ordinal and one
   natural fibre ordinal into a genuine closed `displayed-transfor`;
3. that factorer recognizes exact point eta, generic identity, recursive
   vertical composition, and fixed-head pre/postwhiskering; and
4. `factorDisplayedTransforComponent` already eliminates an indexed whole-
   fibre component at the outer base binder.

The current public `transforLambda` stops before this composition for two
deliberate representation reasons: it accepts only closed ordinary functors at
the root, and the integrated compact contextual binder returns the
`displayed-transfor` facade directly. The missing seam is therefore an open
inner-component wrapper plus a thin expanded outer facade. A second scoped
category/functor descriptor, fake open `KernelExpression`, or total-context
section is unnecessary.

### Selected composition

Use the already open `indexed-functor` endpoints as the inner binder's
construction-only classifier:

```text
closed FF, GG : Functord_cat E D
  -- apply at active k -->
open FF[k], GG[k] : Functor_cat (E[k]) (D[k])
  -- lambda^n a -->
open indexed transformation at k
  -- lambda^n k -->
closed second-hom owner.
```

The inner abstraction must invoke the exact compact point factorer and retain
its recovered whole `Transfd` owner as private construction metadata. The
outer abstraction may eliminate that wrapper only under the matching active
base and endpoint context. It then presents the same closed Core through the
ordinary iterated-Hom facade. Compact `:^nd` continues to present it through
`Transfd_cat`.

As at the first hom, reuse means one internal recursive factorization and one
Core term. It does not require the compact API to call the public expanded
callbacks literally.

## Frozen `COMPOSITIONAL-ND-EXPANDED-1D` Proposal

Gate: `H-DTTLF-USABILITY-COMPOSITIONAL-ND-EXPANDED-01`

Decision:
[`D-DTTLF-USABILITY-077`](./TYPESCRIPT_ELABORATOR_V3_2_COMPOSITIONAL_NATURAL_BINDER_D077_REVIEW.md)
approved from immutable proposal checkpoint
`f176d08b9aa831b05241ef301475379d78e32939`.

### Exact typed surface

Under the existing `compositional-natural-binder-1` profile, qualify this
literal TypeScript composition:

```typescript
emdash.transforLambda('k', FF, GG, k =>
    emdash.transforLambda(
        'a',
        emdash.apply(FF, k, { expectedShape: 'fibre-functor' }),
        emdash.apply(GG, k, { expectedShape: 'fibre-functor' }),
        a => body(k, a)
    )
)
```

Here `FF` and `GG` are parallel closed displayed functors from `E` to `D`.
The outer result has surface type:

```text
Hom_cat (Transf_cat K Cat_cat E D) FF GG.
```

The existing compact presentation remains:

```typescript
emdash.displayedTransforContextLambda(
    'a',
    FF,
    GG,
    a => body(a)
)
```

with surface type `displayed-transfor` at `Transfd_cat E D FF GG`.

Implement the expanded presentation by:

1. dispatching `transforLambda` over parallel closed displayed-functor
   endpoints to the expanded outer second-hom binder;
2. dispatching a nested `transforLambda` over two matching active
   `indexed-functor` endpoints to one construction-only fibre-natural binder;
3. having that inner binder create the fibre token and invoke the exact
   `factorDisplayedTransforPoint` recursion used by compact `:^nd`;
4. retaining the recovered closed displayed transformation as private term
   metadata while returning the matching open `indexed-transfor` component;
5. allowing only the matching outer binder to eliminate that component and
   wrap the byte-identical Core as an ordinary iterated-Hom term; and
6. delegating component and internal higher-action elimination on the
   expanded facade to the retained coherent displayed owner.

The implementation may extract a small shared helper from the compact wrapper
to avoid duplicated evidence construction, but it must preserve the existing
compact factorer and tests as rollback evidence until parity is green.

### Required evidence

One focused suite must establish:

1. expanded eta evaluates each callback once, generic-checks at the ordinary
   iterated-Hom type, retains surface type `hom`, and emits byte-identical Core
   with compact contextual `:^nd` eta;
2. identity, recursive vertical composition, fixed prewhiskering, and fixed
   postwhiskering pass through the same point factorer and agree exactly with
   their compact counterparts;
3. closed base component and fibre point elimination on the expanded result
   agree with compact elimination;
4. `displayedTransforNaturality` on the expanded result reaches the existing
   `tdapp1_int_cell`-backed internal higher action—no pointwise naturality
   equation is accepted or retained;
5. captured base/fibre tokens and open indexed endpoints cannot escape, and
   mismatched bases, families, endpoint ordinals, or non-adjacent endpoints
   fail closed;
6. an arbitrary point arrow or otherwise unfactorable body is rejected; and
7. root ordinary `transforLambda`, expanded first-hom `lambda^n/lambda^f`,
   compact contextual `:^nd`, and the canonical finite telescope remain
   unchanged.

### Files, validation, and non-effects

Behavior edits are limited to:

- `src/v3_2/categorical_surface.ts`;
- `src/v3_2/categorical_program.ts`;
- one focused
  `tests/v3_2_categorical_compositional_nd_expanded_tests.ts`;
- `tests/main_tests.ts` only for runner registration; and
- this plan and the handoff.

Run the focused new suite plus the nearest ordinary-natural, first-hom, and
compact contextual `:^nd` suites; root workspace check, typecheck, complete
changed-file lint, and exact diff hygiene. Because this is a new shared
frontend behavior boundary, run one root `check:ts` only after the bounded
matrix is otherwise green. Carry forward the already recorded unrelated
kernel-pin/count and README-wrap failures, and do not repeat that aggregate
for this boundary. No kernel CI, browser, print, book, or repository aggregate
is authorized.

This slice adds no explicit Core node, checker branch, transfer declaration,
runtime/proof/unification rule, Lambdapi edit or owner, new scoped public
descriptor, curry, cast, coercion, total-context section, external coherence
payload, mixed `Functor_catd`/`Transf_catd` section claim, arbitrary body
synthesis, text syntax, browser behavior, or scale work.

## `COMPOSITIONAL-ND-EXPANDED-1D` Implementation Result

The reviewed second-hom bridge is implemented without a kernel, explicit-Core,
or transfer delta:

1. Applying the closed displayed endpoints `FF` and `GG` at the active outer
   base produces the existing construction-only `indexed-functor` endpoints.
   No fake open `KernelExpression` or new scoped category descriptor is added.
2. The immediately nested ordinary-natural abstraction creates the fibre
   token and calls the exact shared contextual point factorer used by compact
   `displayedTransforContextLambda`. Eta, identity, recursive vertical
   composition, and both fixed whiskering orientations therefore compile by
   the same recursive algorithm.
3. The inner wrapper may escape neither callback nor endpoint context. It
   privately retains only the already recovered coherent `Transfd` owner; an
   arbitrary point arrow still fails closed.
4. The outer abstraction eliminates the base token and presents that same
   Core term at
   `Hom_cat (Transf_cat K Cat_cat E D) FF GG`. Component, fibre-point, and
   `tdapp1_int_cell`-backed higher action delegate to the retained owner.
5. Compact and expanded facades share one internal recursive compiler and one
   Core result. Neither facade literally invokes the other's public callback
   API. Ordinary closed `lambda^n` remains independently reusable, while the
   particular open-fibre inner `lambda^n a` is necessarily scoped beneath its
   matching outer `lambda^n k`.

The corresponding first-hom sharing claim is deliberately narrower than a
universal open/closed functorial bracket. A fixed-category `lambda^f`—closed or
merely nested under an unrelated outer scope—uses `categoricalLambda` and its
`directDiagonal`/`compileContextual` lowering. A genuinely indexed
`lambda^f a : E[k]` dispatches instead to
`contextualDisplayedFunctorLambda`, because both its source and target
classifiers depend on `k`; that path shares `factorDisplayedFunctorBody` with
compact `lambda^fd`. The implementations share lower-level typed terms,
usage/scoping, application, and Core owners, but not one classifier-parametric
top-level functorial body compiler. This is a recorded architectural
non-uniformity, not an external-coherence or soundness defect. A future audit
may determine whether a common classifier-directed bracket engine would
improve scalability; it is not part of the present graduation claim.

That distinction reflects the selected product boundary. The TypeScript layer
is compiling faithfully into the active categorical semantics, where a fixed
`Functor_cat A B` classifier and an open displayed fibre classifier genuinely
have different contextual formation, action, and packaging. It is not trying
to invent a second standalone functorial type theory whose native judgments
erase that distinction. This semantic split does **not** imply that permanent
top-level implementation duplication is desirable or necessary: a future
classifier-indexed recursive engine may share identity, composition,
application chains, occurrence/usage analysis, scoping, and explicit-Core
construction while retaining thin fixed/open validation and result wrappers.
Any such refactor must preserve the presently exact Core and action evidence;
it must not cast an open fibre to a closed category or replace internal action
with external coherence data.

The new focused suite passes 5/5. The nearest ordinary-natural, expanded
first-hom, and compact contextual eta/identity/composition/whiskering matrix
passes 35/35 under bounded six-worker concurrency. The selected canonical
four-layer contextual-telescope preservation case passes 1/1. Workspace
topology, root typecheck, complete changed-file lint, and exact diff hygiene
pass.

The required root `check:ts` was run exactly once after that bounded matrix was
green. Workspace, typecheck, and full lint pass. The aggregate exercised the
registered D-077 suite without an observed feature failure and remains
non-green on the already recorded active-kernel source-digest/source-position/
declaration-count pin family and README line-wrap assertion. This aggregate
must not be repeated for the unchanged boundary.

## `COMPOSITIONAL-NATURAL-TEXT-PARITY-1D` Audit Result

The remaining direct/text gap is resolver routing, not parsing, elaboration,
or categorical semantics:

1. The existing located grammar accepts alphabetic binder modes and nested
   lambda nodes, so both `lambda^n k. lambda^f a. body` and
   `lambda^n k. lambda^n a. body` already have an unambiguous syntax tree.
2. Root mode `^n` currently routes only to the dependent-section expected
   contract. A nested lambda without an explicit recursive expected contract
   deliberately fails as `UNSUPPORTED_NESTED_ABSTRACTION`.
3. The neutral term resolver already supports application, identity,
   `composeCells`, and fixed mapper applications. Compact `^fd` and `^nd`
   tests already exercise those exact body forms.
4. The first expanded typed method needs source/target displayed families so
   it can construct scoped `E[k]` and `D[k]` categories inside its callback.
   The second expanded typed method needs closed displayed-functor endpoints;
   applying them at `k` already produces the indexed functor endpoints for the
   inner natural binder.
5. Therefore no new text AST, parser, application heuristic, Core node,
   checker branch, action table, or kernel owner is needed. Two exact expected
   contracts can select two thin resolver routes which call the public typed
   API literally.

This audit also preserves the clarified implementation boundary: the expanded
first-hom text route targets the specialized open-fibre
`contextualDisplayedFunctorLambda` dispatch and its compact-`:^fd` factorer.
It does not claim that fixed-category `categoricalLambda` and indexed
open-fibre abstraction share one universal top-level compiler.

## Frozen `COMPOSITIONAL-NATURAL-TEXT-PARITY-1D` Proposal

Gate: `H-DTTLF-USABILITY-COMPOSITIONAL-TEXT-PARITY-01`

Decision:
[`D-DTTLF-USABILITY-078`](./TYPESCRIPT_ELABORATOR_V3_2_COMPOSITIONAL_NATURAL_BINDER_D078_REVIEW.md)
approved from immutable proposal checkpoint
`19ec1adb1bd2ee3288338e7069759549c1f282a8`.

Add exactly two public text expected contracts:

```typescript
{
    kind: 'expanded-displayed-functor',
    base: K,
    source: E,
    target: D
}

{
    kind: 'expanded-displayed-transfor',
    base: K,
    sourceFamily: E,
    source: FF,
    target: GG
}
```

Under those contracts, qualify exactly these presentations, with both shown
annotations independently optional:

```text
lambda^n k : K. lambda^f a : E. body(k,a)
lambda^n k : K. lambda^n a : E. body(k,a)
```

Implement the first route by calling:

```typescript
program.transforLambda(kName, E, D, k =>
    program.lambda(
        aName,
        program.fibre(E, k),
        program.fibre(D, k),
        a => resolveBody(k, a)
    )
)
```

Implement the second route by calling:

```typescript
program.transforLambda(kName, FF, GG, k =>
    program.transforLambda(
        aName,
        program.apply(FF, k, { expectedShape: 'fibre-functor' }),
        program.apply(GG, k, { expectedShape: 'fibre-functor' }),
        a => resolveBody(k, a)
    )
)
```

The resolver must:

1. dispatch root `^n` by the exact expected-contract kind;
2. require one immediately nested single-binding `^f` or `^n` lambda as
   appropriate;
3. check an optional outer category annotation and optional inner displayed-
   family annotation through the existing comparison helpers;
4. extend the callback-local environment at each binder and resolve the final
   body recursively through the existing neutral term resolver;
5. preserve the existing error phases, source spans, callback-once behavior,
   scope rejection, and compact/ordinary routes; and
6. advance `CORE_CATEGORICAL_TEXT_REVISION` to
   `COMPOSITIONAL-NATURAL-TEXT-PARITY-1D-CATEGORICAL-TEXT-1`, synchronizing
   every exact revision assertion mechanically.

One focused suite must prove:

- first-hom eta, identity, finite composition, optional annotations, and exact
  Core parity with both direct typed and compact `:^fd` construction;
- second-hom eta, identity, recursive vertical composition, both fixed
  whiskers, optional annotations, and exact Core parity with both direct typed
  and compact `:^nd` construction;
- component, fibre-point, and internal higher-action observations remain
  available on the parsed second-hom facade;
- wrong outer/inner modes, missing immediate nesting, wrong annotation kinds
  and classifiers, endpoint mismatch, arbitrary point data, unsupported
  profiles, and further unqualified nested lambdas fail closed at their
  located spans; and
- existing ordinary `^f`, dependent-section `^n`, compact `^fd/^nd`, grouped
  contextual text, and revision contracts remain unchanged apart from the
  intentional revision value.

Behavior edits are limited to `src/v3_2/categorical_text.ts`, one focused
`tests/v3_2_categorical_compositional_text_parity_tests.ts`, runner
registration, the mechanically synchronized revision assertions, this plan,
and the handoff. Run the focused suite and nearest text/compositional
regressions, then workspace, typecheck, complete changed-file lint, and exact
diff hygiene. Because this changes shared text behavior, run one root
`check:ts` only after the bounded matrix is green and do not repeat it. No
Lambdapi, kernel CI, browser, reviewer, print, book, release, or repository
aggregate is authorized.

## `COMPOSITIONAL-NATURAL-TEXT-PARITY-1D` Implementation Result

The approved adapter-only slice is implemented:

1. Two public expected contracts distinguish the expanded first and second
   displayed Hom presentations. Root `^n` dispatches by those contracts while
   every existing ordinary, dependent-section, compact, and grouped route is
   unchanged.
2. The first route requires one immediate inner `^f`, checks the optional base
   and displayed-family annotations, and calls literal typed
   `transforLambda(k,E,D,k => lambda(a,E[k],D[k],body))`.
3. The second route requires one immediate inner `^n`, applies the two closed
   displayed-functor endpoints at the active base, and calls literal nested
   `transforLambda`. Both routes extend only callback-local environments and
   resolve the final body through the existing neutral resolver.
4. The adapter adds no parser node, Core node, checker branch, action table,
   kernel owner, runtime/proof rule, cast, curry, or external coherence field.
   Open first-Hom text reaches `contextualDisplayedFunctorLambda` and the
   compact-`:^fd` factorer; it does not claim a universal fixed/open `^f`
   compiler.
5. The text revision is exactly
   `COMPOSITIONAL-NATURAL-TEXT-PARITY-1D-CATEGORICAL-TEXT-1`, with every exact
   assertion synchronized mechanically.

Focused evidence is effectively 6/6. The heavyweight run exercised first-Hom
identity/eta/chains, second-Hom eta/identity/composition/both whiskers,
component/point/higher action, the complete annotation/mode/endpoint/body
fail-closed matrix, and predecessor routes. Its only successive diagnostic
failures were stale expected column/capability-code literals after all semantic
assertions had executed; the corrected unsupported-profile leaf then passes
independently 1/1 without rebuilding the expensive profile. The closest prior
text and expanded direct suites pass 24/24 under bounded four-worker
parallelism. Workspace topology, root typecheck, complete changed-file lint,
exact revision search, and diff hygiene pass.

The required root `check:ts` was run once. Workspace, typecheck, and full lint
pass. The monolithic test runner reaches terminal non-green only in the
already-recorded stale active-kernel digest/source-position/declaration-count
pin family and README line-wrap assertion; no D-078 feature failure was
observed. Its middle TAP output was elided by the terminal capture, so no exact
aggregate count is invented here. Do not repeat that aggregate for this
boundary.

## Completed Classifier-Directed Functorial Bracket Audit

After the rollback-safe D-078 checkpoint, the audit compared fixed-category
`categoricalLambda`/`compileContextual` with open-fibre
`contextualDisplayedFunctorLambda`/`factorDisplayedFunctorBody`.

The audit should classify:

- recursive cases already common in semantics and Core construction;
- cases necessarily specialized by fixed versus open classifiers;
- cases present in only one accepted body algebra; and
- the smallest possible classifier-indexed internal engine, if one is
  justified by exact parity evidence.

The audit establishes the following actual implementation map:

| Body operation | Fixed `compileContextual` | Displayed `compileDisplayedContextual` | Narrow compact/open displayed factorer |
|---|---|---|---|
| bound variable / identity | yes | yes, through projection wiring | yes |
| closed unary composition | yes | yes | yes |
| constant body / weakening | any supported closed object | qualified displayed section weakening in its wrapper | qualified displayed section weakening |
| duplicated input / pairing | product pairing plus evaluation | typed fibre pair plus displayed product owners | no |
| general application | recursively varying subject and argument | closed displayed subject plus recursive argument; reviewed fixed/varying displayed evaluation | no |
| nested abstraction | product wiring, exchange, and ordinary curry | only the reviewed exact mixed displayed abstraction | no |
| result packaging | `Functor_cat A B` | `Functord_cat E D` over a hidden base | compact `Functord_cat` or an open ordinary-natural component |

This means that two distinct conclusions must not be conflated:

1. A single erased fixed/open compiler is neither necessary nor currently a
   mechanical refactor. The fixed and displayed classifiers select different
   structural owners, application judgments, scope conditions, and result
   wrappers. A future classifier-indexed traversal remains feasible, but it
   should have separate fixed and displayed algebras rather than pretending
   that an open fibre is a closed category.
2. Consolidation **within the displayed classifier** is already strongly
   qualified. With one binding, `displayedContextLambda` has source family
   exactly that binding's family and recursively invokes
   `compileDisplayedContextual`. A bounded in-memory probe compared it with
   `displayedFunctorLambda` for identity, eta, two-step composition, and exact
   section weakening. All four cases have byte-identical explicit Core,
   byte-identical inferred types, and semantic comparison status `equal`.

The current sharing boundary is therefore historically narrower than the
available semantics: compact `lambda^fd` and expanded
`lambda^n k. lambda^f a` share `factorDisplayedFunctorBody`, while the richer
one- and many-binding displayed bracket already exists beside it. The
high-yield redesign is to extract or parameterize the existing displayed body
driver so that compact and open-displayed wrappers can reuse it while keeping
their distinct scope checks, abstraction evidence, and outer result facades.
This needs no new Lambdapi owner, cast, curry construction, external
coherence field, or standalone functorial-type-theory kernel.

### Selected next candidate: `DISPLAYED-FUNCTOR-CONTEXTUAL-ENGINE-0F`

Before changing behavior, perform one bounded exact-scope audit that:

1. locates the smallest internal helper shared by one-binding
   `displayedContextLambda`, compact `displayedFunctorLambda`, and open
   `contextualDisplayedFunctorLambda`;
2. preserves byte-identical Core, inferred types, evidence classifications,
   and failure behavior for the existing identity/eta/composition/weakening
   corpus;
3. selects one representative body already owned by
   `compileDisplayedContextual` but absent from the narrow factorer—prefer the
   fixed-argument displayed evaluation corresponding to the useful form
   `lambda^f F. F(a0)`—and proves compact/expanded parity plus object and arrow
   action;
4. inventories exact source, test, revision-pin, and public-contract impact;
   and
5. freezes and separately reviews an exact implementation proposal before any
   semantic or public behavior edit.

This candidate is a qualification of existing internalized semantics, not an
authorization to accept arbitrary pointwise functions, erase dependency, or
make fixed and displayed classifiers definitionally identical.

### Exact proposal: `DISPLAYED-FUNCTOR-CONTEXTUAL-ENGINE-1F`

Gate:
`H-DTTLF-USABILITY-DISPLAYED-FUNCTOR-CONTEXTUAL-ENGINE-01`.
Decision:
`D-DTTLF-USABILITY-079`.

The read-only 0F audit selects `compileDisplayedContextual` itself as the
smallest shared recursive engine. No new generic traversal or additional
intermediate AST is justified. The historical compact/open factorer remains
the classifier- and presentation-specific wrapper around that engine.

The exact proposed implementation is:

1. In `src/v3_2/categorical_surface.ts`, extend the displayed-functor
   factorization/evidence rule union with exactly
   `categorical.displayed-functor-contextual` and let the factorization carry
   structural as well as dependent prerequisites.
2. Preserve the existing qualified section-weakening fast path and the exact
   direct identity/eta/closed-chain path, including their current rule names,
   chain lengths, recovered terms, Core, types, and failure behavior.
3. Only when `displayedContextualAbstraction` is enabled and neither old path
   applies, create a one-slot identity wiring for the bound fibre variable and
   invoke the existing `compileDisplayedContextual` recursively. Require its
   source family and target family to match the requested displayed binder
   exactly.
4. Reject every usage ordinal other than the binder's hidden base and exposed
   fibre variable before invoking the richer path. This preserves the current
   no-outer-capture boundary for both compact and expanded wrappers.
5. Merge the existing Sigma/Pi bridge prerequisites with the recursive
   compilation's structural and dependent prerequisites. Add no owner name,
   runtime rule, proof rule, Core node, checker branch, cast, curry, or
   external coherence payload.
6. Route both existing wrappers through that result without changing their
   facades: compact `displayedFunctorLambda` remains a `Functord_cat` surface
   term, while open `contextualDisplayedFunctorLambda` remains the component
   of the enclosing ordinary `Transf_cat` abstraction. The existing one- and
   many-binding `displayedContextLambda` public method remains unchanged.
7. Keep the historical `fibred-binder-1` profile and
   `CORE_CATEGORICAL_FIBRED_BINDER_CONTRACT` unchanged. Because that profile
   does not enable displayed contextual abstraction, its non-chain rejection
   remains exact. The new path is available only in already-later profiles
   that own the reviewed contextual operations.
8. Add
   `tests/v3_2_categorical_displayed_functor_contextual_engine_tests.ts` and
   register it in `tests/main_tests.ts`. Its focused matrix must prove:
   byte-identical old identity/eta/composition/weakening Core and inferred
   types; compact/one-binding/expanded parity for fixed-argument displayed
   evaluation `lambda^f F. F(a0)`; object and consumed base-arrow action;
   compact/one-binding/expanded parity for the one-variable fibre diagonal;
   callback-once/frozen evidence; preservation of the old base-profile
   rejection; and rejection of a genuinely unsupported or escaped body.
9. In
   `tests/v3_2_categorical_compositional_fd_expanded_tests.ts`, remove only
   the superseded assertion that a fibre diagonal is unfactorable; retain all
   wrong-base, wrong-target, cross-fibre, and scope failures. Update the
   `displayedFunctorLambda` comment in
   `src/v3_2/categorical_program.ts` so it distinguishes the historical base
   contract from later contextual profiles.
10. Change no text adapter, browser preset, public method signature,
    historical contract/review module, transfer fragment, active Lambdapi
    file, book artifact, or scale-qualification claim.

Reject the proposal if the fixed-argument evaluation needs a new kernel owner,
if any of the four historical cases changes explicit Core or inferred type,
if the base `fibred-binder-1` profile begins accepting a non-chain body, if an
outer token can escape through the richer path, or if the expanded wrapper no
longer emits the exact compact Core.

Proportional validation is the new focused suite; the existing compositional
FD-expanded, fibred-binder, displayed-bracket, and displayed-evaluation suites
in bounded parallel execution; workspace check; root typecheck; complete
changed-file lint; exact diff hygiene; and one bounded current-kernel check.
Because this changes the shared categorical surface, run one root `check:ts`
after the bounded matrix is green and before the semantic checkpoint. Carry
forward that result and do not rerun it for documentation synchronization.

This proposal is non-self-authorizing. Checkpoint it independently, then
review exactly that immutable proposal under the standing unattended
delegation with immediate human supersession before editing behavior.

## Work Ledger

| Slice | Status | Dependency | Exact boundary |
|---|---|---|---|
| `CONTEXTUAL-ND-TELESCOPE-REVIEWER-1AP` | final-green at `607a026f88bc6d3b9f305ecb21f6630ce7c94950` | D-070 through D-073 | Typed canonical finite `:^nd`, grouped text, lean chain-2A reviewer preset, production/browser evidence, and effective aggregate qualification. |
| `COMPOSITIONAL-NATURAL-BINDER-0A` | complete; read-only | final-green 1AP; user-approved architectural direction | Existing semantic ladder and rich Core are sufficient; exact gap is open ordinary-component lowering. `Pi_cat(Transf_catd)` remains distinct from `Transfd_cat`. |
| `COMPOSITIONAL-NATURAL-BINDER-1B` | final-focused-green at `a0c8c7a77a310ded8c972d2308e47f27c3a8c25d` | completed 0A; D-074 and D-075 | Rich `transfor` assumptions and reusable root `transforLambda` pass eta, identity, recursive composition, both whiskers, arbitrary-arrow rejection, scope/callback/immutability, closed elimination, generic checking, and compact-`:^nd` preservation. The first slice deliberately rejects an outer contextual capture. |
| `COMPOSITIONAL-NATURAL-ACTION-CORRECTION-1B2` | final-focused-green at `a0c8c7a77a310ded8c972d2308e47f27c3a8c25d` | focused 1B failure; D-075; existing `comp_cat_con_fapp1_func` and `comp_cat_cov_fapp1_func` | Imports exactly two existing classifier-exact action signatures and uses them for pre/postwhiskering. Adds zero rules, kernel owners, Core nodes, checker branches, or external coherence fields. |
| `COMPOSITIONAL-NATURAL-BINDER-GRADUATE-0C` | complete; read-only architecture audit | completed 1B/1B2 | Both compact terms recheck unchanged under their expanded facades. Select shared scoped contextual factorization with thin expanded/compact wrappers; literal current-method reuse is blocked only by the absent open-fibre representation. Keep mixed `Functor_catd`/`Transf_catd` distinct. |
| `COMPOSITIONAL-FD-EXPANDED-1C` | final-focused-green at `9a997edb6a34ddc3310f1a9db7e5db8bdd52c8e1` | completed 0C; D-076; existing first-hom runtime bridge | Construction-only scoped fibres and literal typed `transforLambda(k,E,D,k => lambda(a,E[k],D[k],body))` share the compact `:^fd` factorer, preserve byte-identical Core, expose closed fibre object/arrow action, and retain the ordinary `Transf_cat` facade. |
| `COMPOSITIONAL-ND-EXPANDED-1D` | final-focused-green at `b89420d442536544185e8ab5dbe6876bd9980b96` | green 1C; completed audit; D-077 | The existing open `indexed-functor` endpoints and compact point factorer implement literal expanded `lambda^n k. lambda^n a`; the result retains the ordinary iterated-Hom facade, byte-identical compact Core, and internally owned component/base/higher action. |
| `COMPOSITIONAL-NATURAL-TEXT-PARITY-1D` | final-focused-green at `7f7d201948e5f035e516f6fb15554a1aea26029d` | graduated direct typed API; D-077 checkpoint; D-078 | Exactly two expected contracts and thin resolver routes now expose expanded `lambda^n k. lambda^f a` and `lambda^n k. lambda^n a` text. Existing grammar, neutral resolution, typed methods, and compact factorers are reused; no parser/checker/Core/kernel semantics changed. |
| `CLASSIFIER-DIRECTED-FUNCTOR-BRACKET-0E` | complete; read-only | final-green fixed/open compilers and exact compact/expanded Core parity | Fixed and displayed recursive algebras are distinct. One-binding `displayedContextLambda` nevertheless proves exact four-case Core/type parity with the narrow compact factorer, selecting displayed-only consolidation rather than an erased universal compiler. |
| `DISPLAYED-FUNCTOR-CONTEXTUAL-ENGINE-0F` | complete; read-only; exact 1F proposal frozen below | completed 0E; existing `compileDisplayedContextual`; 4/4 exact one-binding parity; fixed-evaluation consumer/action probe | `compileDisplayedContextual` is the smallest existing engine. The sole gap is profile-gated routing from compact/open wrappers; no kernel owner or universal fixed/displayed traversal is needed. |
| `DISPLAYED-FUNCTOR-CONTEXTUAL-ENGINE-1F` | exact proposal frozen; D-079 review pending | completed 0F; historical base-profile preservation | Reuse the existing recursive displayed compiler only in contextual-enabled profiles, preserve all old fast paths, and graduate fixed evaluation plus a fibre diagonal with exact compact/expanded parity and internal action. |

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
- a universal fixed/open functorial compiler, standalone functorial-type-
  theory kernel, or behavior refactor under the candidate 0E audit; or
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

The D-077 implementation has the following final proportional evidence:

- its focused same-Core/action/negative/predecessor suite passes 5/5;
- the six nearest predecessor suites pass 35/35 concurrently, and the selected
  canonical four-layer telescope preservation case passes 1/1;
- workspace topology, root typecheck, complete changed-file lint, and exact
  diff hygiene pass; and
- the single root `check:ts` was run once. Its static phases pass and no D-077
  feature failure was observed; its aggregate remains non-green on the
  already recorded kernel-pin/count family and README-wrap assertion. It must
  not be repeated for this unchanged boundary.

The D-078 implementation has the following final proportional evidence:

- its focused construction/action/negative/predecessor matrix is effectively
  6/6, including the separately green lightweight unsupported-profile leaf;
- the closest prior text and expanded direct suites pass 24/24 concurrently;
- workspace topology, root typecheck, complete changed-file lint, exact
  revision search, and diff hygiene pass; and
- the single root `check:ts` was run once. Its static phases pass and no D-078
  feature failure was observed; its test phase remains non-green only on the
  already recorded kernel pin/count and README-wrap families. It must not be
  repeated for this boundary.

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
checkpoint. Treat read-only
`COMPOSITIONAL-NATURAL-BINDER-GRADUATE-0C` as complete: both compact Core terms
recheck unchanged under the canonical expanded facades, and the selected
architecture is one shared scoped contextual factorer with thin
presentation-specific wrappers. Treat the independently approved
`COMPOSITIONAL-FD-EXPANDED-1C` proposal as final-focused-green after its
rollback-safe semantic checkpoint
`9a997edb6a34ddc3310f1a9db7e5db8bdd52c8e1`. Treat the read-only
`COMPOSITIONAL-ND-EXPANDED-1D` audit as complete and its exact proposal at
`f176d08b9aa831b05241ef301475379d78e32939` as independently approved under
D-077. Treat that bounded second-hom bridge as final-focused-green after its
rollback-safe semantic checkpoint: literal `lambda^n k. lambda^n a` and compact
`:^nd` share the contextual point factorer and exact Core, while their facades
remain distinct and all action delegates to the recovered coherent owner.
Natural transformation bodies must be recursively constructed from internal
owners and fail closed without them. Treat the read-only
`COMPOSITIONAL-NATURAL-TEXT-PARITY-1D` audit as complete and its exact adapter-
only proposal at `19ec1adb1bd2ee3288338e7069759549c1f282a8` as
independently approved under D-078. Treat its two expected contracts, thin
resolver routes, focused tests, and mechanical revision synchronization as
final-focused-green after their rollback-safe checkpoint. They preserve the
fixed/open classifier distinction and add no parser, Core, checker, kernel, or
external-coherence semantics.

Treat the read-only `CLASSIFIER-DIRECTED-FUNCTOR-BRACKET-0E` audit as complete.
It establishes that fixed `compileContextual` and displayed
`compileDisplayedContextual` are recursive but classifier-specific algebras,
while one-binding `displayedContextLambda` already has exact Core/type parity
with the narrow compact displayed factorer on identity, eta, composition, and
weakening. Do not force a universal fixed/displayed compiler.

Route next to the read-only
`DISPLAYED-FUNCTOR-CONTEXTUAL-ENGINE-0F` scope audit. Select the smallest
displayed-only body-driver extraction that can serve one-binding contextual,
compact, and open-displayed wrappers while preserving their scope checks,
evidence, and result facades. Include one representative existing displayed
evaluation body in the proposed parity matrix. Freeze and independently
review an exact proposal before any refactor. Do not invent a standalone
functorial-type-theory kernel, erase open-fibre dependency, or add behavior
under the read-only audit.

Treat that 0F audit as complete once its exact 1F proposal has an immutable
checkpoint. The existing recursive engine is `compileDisplayedContextual`;
the proposed change is only a profile-gated fallback from the compact/open
displayed factorer, preserving all historical paths and wrappers. Before any
behavior edit, independently review exact gate
`H-DTTLF-USABILITY-DISPLAYED-FUNCTOR-CONTEXTUAL-ENGINE-01` as
`D-DTTLF-USABILITY-079` under the standing unattended delegation with
immediate human supersession. Implement only the ten numbered items if that
review approves them.

Use proportional validation and rollback-safe local checkpoints. Preserve
unrelated work. Do not push, merge, rebase, amend, reset, publish, deploy,
remove worktrees, or perform unrelated cleanup without exact authorization.

## Decision Ledger

- **2026-08-02 — H-DTTLF-USABILITY-DISPLAYED-FUNCTOR-CONTEXTUAL-ENGINE-01
  proposal frozen.** The completed 0F audit selects the existing
  `compileDisplayedContextual` recursion rather than a new universal engine.
  A bounded current-profile probe constructs fixed-argument displayed
  evaluation, observes its existing evaluation/constant-section owners, and
  consumes its internally owned base-arrow action; compact and expanded
  wrappers both currently reject at the one identified factorer seam. The
  exact ten-item 1F proposal preserves every historical fast path and the base
  `fibred-binder-1` contract, enables the richer path only in contextual
  profiles, adds one evidence rule and focused tests, and changes no kernel,
  Core, text, browser, transfer, or public-method contract. It awaits a
  separate immutable D-079 review before behavior.

- **2026-08-02 — CLASSIFIER-DIRECTED-FUNCTOR-BRACKET-0E read-only complete.**
  Source comparison finds two recursive, internally coherent but materially
  different algebras: fixed `compileContextual` owns ordinary constants,
  evaluation/duplication, exchange, and curry; displayed
  `compileDisplayedContextual` owns fibre projections/pairs, closed displayed
  application, and reviewed displayed evaluation/nesting. The compact and
  open-displayed wrappers still share the older narrow
  `factorDisplayedFunctorBody`. A bounded one-binding probe proves that the
  richer displayed compiler emits byte-identical Core and inferred types for
  identity, eta, composition, and qualified weakening (4/4; all semantic
  comparisons equal). The selected continuation is therefore displayed-only
  compiler consolidation, not classifier erasure or a universal compiler.
  `DISPLAYED-FUNCTOR-CONTEXTUAL-ENGINE-0F` remains read-only until an exact
  proposal is frozen and independently reviewed.

- **2026-08-03 — COMPOSITIONAL-NATURAL-TEXT-PARITY-1D final-focused-green.**
  Exactly two expected contracts route expanded `lambda^n/lambda^f` and
  `lambda^n/lambda^n` text into the final-green typed APIs. The first route
  preserves the specialized open-fibre/compact-`:^fd` factorer rather than
  claiming a universal fixed/open compiler. Focused evidence is effectively
  6/6, nearest predecessors pass 24/24 in parallel, and all static gates pass.
  The one required root aggregate was run once; its non-green result remains
  confined to the pre-existing kernel pin/count and README-wrap families and
  must not be repeated. Exact rollback-safe semantic checkpoint:
  `7f7d201948e5f035e516f6fb15554a1aea26029d`. The next candidate is a read-only
  classifier-directed functorial bracket audit, not an authorized behavior
  refactor.

- **2026-08-02 — D-DTTLF-USABILITY-078 approved.** A separate review of exact
  proposal checkpoint `19ec1adb1bd2ee3288338e7069759549c1f282a8`
  confirms that the existing grammar and neutral resolver are sufficient and
  that expected-classifier dispatch is the correct disambiguator for the
  three outer-`^n` meanings. The two routes must invoke the public typed
  methods literally and preserve the recorded fixed/open-fibre compiler
  distinction. No parser/Core/checker/kernel/browser expansion is approved.

- **2026-08-02 — H-DTTLF-USABILITY-COMPOSITIONAL-TEXT-PARITY-01 proposal
  frozen.** The located grammar and neutral body resolver already cover both
  expanded nested forms. The exact proposed delta is two expected contracts,
  two public-API resolver routes, one focused suite, and mechanical text-
  revision synchronization. It adds no parser, Core, checker, action, kernel,
  browser, or release behavior and awaits separate D-078 review.

- **2026-08-02 — COMPOSITIONAL-ND-EXPANDED-1D final-focused-green.** Literal
  typed `lambda^n k. lambda^n a` uses the existing indexed endpoints and the
  exact compact contextual point factorer, retaining an ordinary iterated-Hom
  facade over byte-identical compact Core. Component, point, and internal
  higher action delegate to the recovered coherent `Transfd` owner; arbitrary
  point data and scoped-endpoint escape fail closed. Focused 5/5, nearest
  predecessor 35/35, canonical four-layer preservation 1/1, and all static
  gates pass. The single root aggregate was run once and remains non-green on
  the pre-existing kernel-pin/count and README-wrap contracts; it must not be
  repeated. Exact rollback-safe semantic checkpoint:
  `b89420d442536544185e8ab5dbe6876bd9980b96`.

- **2026-08-02 — D-DTTLF-USABILITY-077 approved.** A separate review of exact
  proposal checkpoint `f176d08b9aa831b05241ef301475379d78e32939` confirms
  that the existing open `indexed-functor` view is callback-scoped and cannot
  masquerade as a closed kernel functor. The private inner wrapper may be
  created only after the compact point factorer recovers a coherent `Transfd`
  owner; the expanded outer wrapper retains the ordinary iterated-Hom facade
  and delegates component/higher action to that same owner. No Core/kernel
  semantics, coercion, or external coherence is approved.

- **2026-08-02 — H-DTTLF-USABILITY-COMPOSITIONAL-ND-EXPANDED-01 proposal
  frozen.** The read-only second-hom audit finds that applying `FF` and `GG`
  at the active base already supplies the required open `indexed-functor`
  endpoints. The selected slice adds construction-only inner and outer
  wrappers around the exact compact `factorDisplayedTransforPoint` recursion,
  retaining respectively the ordinary iterated-Hom and compact `Transfd_cat`
  facades. It adds no Core/kernel semantics and remains behind separate D-077
  review.

- **2026-08-02 — COMPOSITIONAL-FD-EXPANDED-1C final-focused-green.** Literal
  typed `lambda^n k. lambda^f a` uses callback-scoped fibre categories and the
  extracted compact `:^fd` factorer. Eta, identity, and finite chains emit
  byte-identical Core under distinct facades; closed fibre object/arrow action,
  internal base-arrow ownership, scope rejection, negative factorization, and
  predecessor preservation pass. Static gates pass. The sole root aggregate
  remains non-green only on unrelated stale kernel pins/counts and the known
  README line-wrap assertion and must not be repeated. The exact semantic
  checkpoint is `9a997edb6a34ddc3310f1a9db7e5db8bdd52c8e1`.
- **2026-08-02 — D-DTTLF-USABILITY-076 approved.** A separate review of exact
  proposal checkpoint `5929b2962ea6fe3465047556f9992bab4a827971` confirms
  that the scoped fibre descriptor adds no LF semantics and cannot escape as a
  closed category. The shared recursive factorer and thin facade wrappers are
  approved for the first-hom `lambda^n k. lambda^f a` bridge. Arbitrary
  point-functor acceptance, second-hom work, and text syntax remain excluded.
- **2026-08-02 — H-DTTLF-USABILITY-COMPOSITIONAL-FD-EXPANDED-01 proposal
  frozen.** The completed 0C audit selects a construction-only scoped fibre
  descriptor, one shared recursive `:^fd` factorer, and thin expanded/compact
  wrappers. The exact first slice exposes literal typed
  `lambda^n k. lambda^f a` composition and retains `Transf_cat`; it does not
  implement the second-hom bridge or refactor compact `:^nd`.
- **2026-08-02 — 0C expanded/compact facade probe complete.** Compact `:^fd`
  and `:^nd` eta witnesses both generic-check unchanged under respectively the
  ordinary `Transf_cat` and iterated-Hom rich types, with byte-identical Core.
  Category presentations remain distinct; the existing second-hom probe stays
  runtime non-equal, proof-time solved, and object-runtime equal. This proves
  the final convergence can share factorization while preserving facade
  identity and rules out a cast or new kernel owner.
- **2026-08-02 — D-DTTLF-USABILITY-075 approved and implemented.** A separate
  immutable review at `36668e00b722ece632353f9636fb8bb083b1db5c` approves
  exactly the two existing classifier-exact action signatures. The final
  focused suite passes 6/6; both whiskers are accepted by the generic checker,
  and the transfer adds no rule or mathematical owner. The combined D-074 and
  D-075 semantic implementation is checkpointed at
  `a0c8c7a77a310ded8c972d2308e47f27c3a8c25d`. The one shared root aggregate
  was not repeated after reporting only existing source-digest and README-wrap
  contracts outside this tranche.
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
