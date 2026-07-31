# TypeScript Elaborator v3.2 Mixed-Mode Displayed Telescope Plan

Date: 2026-07-31

Status: living approved architecture; `MIXED-NEST-0A` is complete and
focused-green at checkpoint
`77f79bf8e139d856965f41733d3aeff9ffefd9d1`; the `MIXED-NEST-1A0`
architecture audit has measured a displayed-curry/introduction dependency at
checkpoint `5c8b79404ead2abc03c51f7e12a48de7cb752bb6`;
the no-active-edit `MIXED-CURRY-0A` design/probe has rejected both ordinary
fibrewise curry and a premature new primitive; `MIXED-NEST-ACTION-0B` is
complete and focused-green at checkpoint
`a31b8927910d32613c7d0fac1862317b08dbf920`; `MIXED-NEST-1A` is implemented
and focused-green at its frozen construction-only recursive factorization
boundary at checkpoint
`1142f723dc41ac336f420429af47d77e21c06fd4`;
`MIXED-NEST-ACTION-1B` is implemented and focused-green at its frozen
existing-conversion result-classifier boundary at checkpoint
`b76baaf75ea332b977d403b6e11c975972466a45`;
`DISPLAYED-TELESCOPE-GENERIC-1` has completed its no-edit architecture audit
and its exact finite canonical-layer fold is frozen under
H-DTTLF-USABILITY-DISPLAYED-TELESCOPE-GENERIC-01 /
D-DTTLF-USABILITY-026; the implementation is focused-green at checkpoint
`6fa6f2ebdafe8f4bc8e80136a4aadcd3e9ae43fa`; the exact
`DISPLAYED-MIXED-GRADUATE-1` boundary is now frozen under
H-DTTLF-USABILITY-DISPLAYED-MIXED-GRADUATE-01 /
D-DTTLF-USABILITY-027 and approved as proposed through the standing
unattended delegation after proposal checkpoint
`ddc78c250970f62c09d822a39a16502f41c75db1`; `TEXT-PARITY-MIXED-1` is the
next dependency-ready row

This is the dedicated successor to the completed bounded work recorded in
[`TYPESCRIPT_ELABORATOR_V3_2_DISPLAYED_BRACKET_PLAN.md`](./TYPESCRIPT_ELABORATOR_V3_2_DISPLAYED_BRACKET_PLAN.md).
It does not rewrite that plan's frozen completion history. It corrects and
continues the still-open claims named there: nested displayed abstraction,
mixed variance, and arbitrary finite telescope depth.

The user approved the corrected architecture and asked that its analysis be
recorded comprehensively before implementation continues. The decision
response is archived for recovery as
`infinity-codex:019fb460-a0c8-7373-926f-f754198d6e51:019fb5aa-316e-7082-9a86-802b25e1bc9d`.
The archive is decision evidence only; active code, the active Lambdapi
kernel, this plan, and repository SOP remain authoritative.

## Objective

Make categorical/displayed variables and binders recursively usable at
arbitrary finite telescope depth, including the mixed variance that appears
as soon as a nested target is itself a varying functor category.

The end state must preserve the project's internalization rule:

- a functorial binder constructs a genuine functor with object and arrow
  action;
- a natural/displayed binder constructs the corresponding coherent internal
  package;
- typed application selects `fapp*`, `tapp*`, `fdapp*`, or `tdapp*`
  projections;
- no pointwise function plus external naturality equations is accepted as a
  substitute; and
- unsupported coherence synthesis fails closed.

String parsing and browser promotion follow semantic TypeScript parity. They
are not architectural prerequisites and are not part of the first tranche.

## Authority And Recovery Order

Use these authorities in order:

1. `emdash2/emdash3_2.lp`;
2. `emdash2/emdash3_2_checks.lp`;
3. `emdash2/reports/REPORT_EMDASH_V3_2_CURRENT_STATUS_AND_SOP_2026-05-26.md`;
4. `emdash2/reports/EMDASH_FOUNDATIONS.md`;
5. `emdash2/reports/REPORT_EMDASH_V3_2_CANONICAL_SURFACE_SYNTAX_2026-06-05.md`;
6. this plan and its decision ledger;
7. the completed displayed-bracket plan and TypeScript handoff;
8. linked decision responses; and
9. raw Infinity Codex archives.

Follow root `AGENTS.md`, `emdash2/AGENTS.md` for every active-kernel action,
and
[`PERSISTENT_GOAL_GIT_EXPERIMENTATION.md`](./PERSISTENT_GOAL_GIT_EXPERIMENTATION.md)
for long-running work and local checkpoints.

## Corrected Architectural Conclusion

### 1. Positive Sigma/product recursion is useful but insufficient

There is a valid positive fragment:

```text
K0 = K
K(i+1) = Sigma_cat(Ki,Ei).
```

Products represent independent sibling blocks, Sigma represents genuine
context extension, pullback represents weakening/substitution, and
projection/pairing represents variable occurrence. Repeating those
constructions is enough to carry object variables through a flat displayed
context. The implemented

```text
a : A;
b : B(a), c : C(a);
d : D(a,b,c)
```

consumer is evidence for this part.

That construction alone does not settle nested categorical abstraction.
Removing a hard-coded two/four-binding guard would graduate only an
uncurried positive context fragment.

### 2. Nested displayed abstraction is inherently mixed-variance

Once the body or target is itself a varying functor category, its source
varies contravariantly while its target varies covariantly. The active kernel
owns:

```text
Functor_catd [K]
  (A : Catd(Op_cat K))
  (B : Catd K)
  : Catd K
```

and:

```text
Hom_catd(Functor_catd A B,FF,GG)
  -> Transf_catd A B FF GG.
```

The canonical nested example is:

```text
k :^n K ; C[k] ⊢
  (z :^n Z ; E[k^-;z] ⊢ D[k;z]).
```

Morally:

```text
C : Catd K
E : K^op ⊢ Catd Z
D : K    ⊢ Catd Z.
```

The inner classifier is not a naive second covariant `Functord_cat`. It is
the family:

```text
Hom_catd
  (Const_catd K (Catd_cat Z))
  Ebar
  Dbar
```

where `Ebar` is a section of the pointwise opposite and `Dbar` a section of
the positive family. The full classifier is:

```text
Functord_cat C
  (Hom_catd
    (Const_catd K (Catd_cat Z))
    Ebar
    Dbar).
```

Therefore:

> Arbitrary context arity alone does not settle arbitrary nested binder
> usability.

Mixed variance is part of the arbitrary-depth architecture, not a detached
later feature.

### 3. `homd_int` is an architecture qualification, not decoration

The active kernel's representative target:

```text
homd_int(id_E)[x](u)
  : Π y :^n K^op,
      E[y^-] ⊢_[y]
      (Hom_K(x,y)^op ⊢ Cat)
```

combines:

- natural variation over `K^op`;
- a contravariant displayed source;
- a displayed functor category;
- an ordinary functor category over an opposite Hom category; and
- the internal projection ladder leading through `Transf_catd` and higher
  cells.

The `homd_int(FF)` owner intentionally retains the displayed-functor argument
so negative and positive action remain inside one internal owner. The
TypeScript graduation must eventually demonstrate that a nested
mixed-variance result can be consumed by `homd_int` or an equivalent
next-Hom projection. Merely serializing the outer object expression is not
enough.

### 4. No separate arrow-only binder is required

The phrase “explicit arrow/cell binders” is rejected as a description of the
ordinary categorical usability requirement.

For:

```text
λ^f x : A. body
```

`x` is the object coordinate of the internal categorical variable. The
abstraction constructs a genuine:

```text
F : Functor_cat A B.
```

The same `F` is then applicable through typed projections:

```text
x : Obj A       -> fapp0 F x
p : Hom A x y   -> fapp1 F p.
```

Arrow action is generated by the abstraction. It is not obtained by
separately binding an arrow variable. The same principle applies to `^fd`:
the result is a genuine `Functord`, whose action on base arrows and fibre
arrows belongs to that internal package.

The elaborator's `cellLevel` is an application/classification axis. It must
not be turned into one binder mode per dimension.

### 5. Modes and polarity are distinct but jointly lowered

- `^f` constructs an ordinary functor.
- `^n` constructs a section or naturally indexed term.
- `^fd` constructs a displayed functor and already combines a hidden
  `k :^n K` base with a fibrewise `a :^f E[k]` input.
- `^nd` constructs a displayed transformation from internally coherent
  components.

Polarity is derived from the expected classifier:

- `A` is positive;
- `Op_cat A` is negative;
- a pointwise opposite displayed family is represented through `Op_catd`;
- a family over an opposite base is represented as `Catd(Op_cat K)`; and
- mixed families are constructed by `Functor_catd`, `Hom_catd`, and
  `Transf_catd`.

An unchecked user “contravariant” flag is not the semantic owner. Surface
notation may expose orientation, but the expected type and explicit opposite
constructors determine lowering.

## Current TypeScript Status

The TypeScript implementation already contains:

- an outer dependent LF with scoped dependent Pi/lambda/application,
  bidirectional checking, metas, rewriting, and proof-time unification;
- backend-neutral explicit Core;
- generic declaration/runtime/proof transfer engines;
- opposite category and pointwise opposite displayed-family ingredients;
- the stable constant-domain `Functor_catd` evaluator;
- contravariant category families and dependent targets;
- generic products, Sigma totals, pullback/reindexing, projections, pairing,
  and one genuine dependency edge;
- direct bounded `^fd` and `^nd` consumers;
- transferred `homd_int` and next-Hom action infrastructure; and
- type-directed ordinary/displayed/higher application.

The missing integration is concrete:

- `Hom_catd` and `Transf_catd` are active in Lambdapi but absent from the
  TypeScript declaration/runtime environment;
- the displayed contextual compiler records only covariant brackets;
- arbitrary mixed-domain evaluation is not implemented;
- an applied displayed-functor subject must still be closed in the bounded
  bracket profile;
- `compileDisplayedContextual` explicitly rejects a nested
  `categorical-abstraction`; and
- the demonstrated dependent presentation is still hard-coded to selected
  binding shapes.

No evidence suggests a Lambdapi kernel redesign. The incomplete boundary is
the TypeScript classifier-directed abstraction interface.

## Selected Architecture

The implementation has two interacting components. They may share code where
natural, but no requirement is imposed that every ordinary and dependent case
use one algorithm.

### A. Generic contextual substitution and presentation

This component owns:

- independent sibling products;
- genuine Sigma extensions;
- pullback weakening and substitution;
- projection/pairing for variables;
- repeated lifting through arbitrary finite dependency graphs; and
- a typed locally nameless contextual representation.

Its output is an explicit context presentation and the projections needed by
the body. It does not decide by itself whether the result is a functor,
section, displayed functor, or displayed transfor.

### B. Classifier-directed abstraction algebra

This component selects an introduction law from the expected classifier:

| Expected classifier | Introduction/lowering route |
| --- | --- |
| `Functor_cat A B` | ordinary functorial bracket/curry |
| `Pi_cat D` | natural section abstraction |
| `Functord_cat E D` | displayed functorial bracket |
| `Transfd_cat FF GG` | displayed transformation bracket |
| varying functor family | `Functor_catd`, respecting the opposite source base |
| hom family between varying endpoints | `Hom_catd` |
| hom in a varying functor family | runtime fold to `Transf_catd` |
| internal dependent hom | `homd_int` and its projection ladder |

The contextual engine supplies free-variable projections. The abstraction
algebra determines how those projections occur in positive and negative
positions. Both components emit only internal kernel owners.

## Required Qualification Evidence

Arbitrary finite displayed depth may be claimed only after both witnesses
below pass.

### Positive deep telescope

```text
a : A;
b : B(a), c : C(a);
d : D(a,b,c);
e : E(a,b,c,d);
...
```

It must cover object action and nested-Sigma arrow action, not only object
projection.

### Canonical mixed-mode nested target

```text
k :^n K ; C[k] ⊢
  (z :^n Z ; E[k^-;z] ⊢ D[k;z])
```

It must lower to the exact `Functord_cat`/`Hom_catd` classifier and verify:

- the negative occurrence is represented by `Op_cat`/`Op_catd`;
- `Hom_catd(Functor_catd A B,FF,GG)` reduces to `Transf_catd A B FF GG`;
- outer base-arrow action reaches the inner construction internally;
- a `homd_int` projection or equivalent next-Hom consumer accepts the
  result;
- no external naturality or variance evidence appears; and
- flattened and nested/curry presentations are compared only at the
  kernel-selected runtime or proof-time boundary.

Runtime equality must not be invented where the active kernel supplies only
proof-time compatibility.

## Scope Boundaries

This plan does not require immediate synthesis of a coherent `Transfd` from
every imaginable pointwise `λ^nd` body. It distinguishes:

1. making `Transf_catd`, `homd_int`, and higher action available wherever
   nested classifier formation requires them; from
2. recursively synthesizing every general `^nd` body.

The first is mandatory for mixed-depth architecture. The second remains
fail-closed outside a qualified family of coherence-owning constructors and
expands consumer by consumer.

Also outside the first tranche:

- a string parser or notation consolidation;
- browser promotion;
- arbitrary mixed-domain evaluation beyond the selected witness;
- groupoidal specialization/closure;
- whole-library Lambdapi transfer;
- a new LF semantic feature;
- a new Lambdapi mathematical owner or rule; and
- remote Git operations, integration, publication, or release.

## Implementation Ledger

| Slice | Status | Dependency | Exact purpose |
| --- | --- | --- | --- |
| `MIXED-NEST-0A` | complete and focused-green at checkpoint `77f79bf8e139d856965f41733d3aeff9ffefd9d1` | completed displayed-ND higher profile and approved architecture | Two existing opaque signatures and four existing runtime rules compile generically in isolated `fibred-displayed-mixed-nest-1`; seven typed constructors build/check the canonical nested classifier and prove its `Transf_catd` fold. The independent constant-`Cat` fold is deferred at its measured nested proof-conversion seam. Zero Lambdapi semantic delta. |
| `MIXED-NEST-1A0` | read-only architecture audit complete at checkpoint `5c8b79404ead2abc03c51f7e12a48de7cb752bb6` | green `MIXED-NEST-0A` | Establish that the existing ordinary `categorical-abstraction` node cannot type the canonical inner `Functord`, that the bounded `displayedFunctorLambda` cannot consume context-varying endpoint families, and that the active kernel names the nested classifier but has no selected general displayed-curry/introduction owner. Add no code or kernel semantics. |
| `MIXED-CURRY-0A` | complete design result; no active-kernel or TypeScript semantic delta | complete `MIXED-NEST-1A0` audit | Ordinary fibrewise curry is ill-typed for a source over `K^op`. A well-typed two-sided total context exists for the plain `Functor_catd` case, but the canonical `Hom_catd(Const(Catd_cat Z),Ebar,Dbar)` target is one enrichment level higher and has no existing general curry. No transparent composite or justified smallest primitive is selected. |
| `MIXED-NEST-ACTION-0B` | complete and focused-green at checkpoint `a31b8927910d32613c7d0fac1862317b08dbf920` | complete `MIXED-CURRY-0A`; green displayed-ND foundation | Nine existing declarations and twelve exact source computations/projections close the dependency path for the direct `homd_int -> homd_src_func -> homd_src_sec -> homd_tgt_func -> homd_` cascade. Two rich typed consumers expose `homd_int(FF)` and its terminal `homd_(FF,x,u,y,v)` family. Zero Lambdapi, intrinsic-owner, checker-branch, external-coherence, proof-fallback, nested-lowering, text, or browser delta. |
| `MIXED-NEST-IR-0C` | exact proposal frozen; delegated implementation approval recorded with human supersession | green `MIXED-NEST-ACTION-0B` and measured existing outer eta | Add one construction-only nested displayed-abstraction node and one construction-only nested application node. Recognize only an indexed object of the canonical `Hom_catd(Const_catd K (Catd_cat Z),Ebar,Dbar)` family, invoke the inner callback once, accept exact eta of that already-coherent object, and factor recursively back to it. Add no Core owner, computation, checker branch, or general curry. |
| `MIXED-NEST-1A` | complete and focused-green at checkpoint `1142f723dc41ac336f420429af47d77e21c06fd4` | green `MIXED-NEST-IR-0C` proposal | The mixed profile now exposes the first explicit nested `^fd` eta through construction-only recursive IR. It preserves outer contextual usage, eliminates only the hidden inner base/fibre slots, compiles back to the same coherent subject, and fails closed for arbitrary pointwise bodies or noncanonical classifiers. Zero Core-owner, kernel, checker-rule, external-coherence, text, or browser delta. |
| `MIXED-NEST-ACTION-1B` | complete and focused-green at checkpoint `b76baaf75ea332b977d403b6e11c975972466a45` | green `MIXED-NEST-1A` and measured no-edit conversion probes | Ordinary object application now refines only the exact canonical `Fibre_cat(Hom_catd(Const_catd K (Catd_cat Z),Ebar,Dbar),y)` target. It preserves the same Core term, derives `Ebar[y^-]` and `Dbar[y]` internally, and checks it as a `Functord_cat` object through existing runtime conversion. Outer base-arrow transport and direct base-object evaluation both feed the refined inner package to `homd_int`. Zero coercion, cast API, owner, rule, or external-evidence delta. |
| `DISPLAYED-TELESCOPE-GENERIC-1` | complete and focused-green at checkpoint `6fa6f2ebdafe8f4bc8e80136a4aadcd3e9ae43fa` | mixed nested action plus current positive compiler | The mixed successor now derives arbitrary finite canonical sibling layers from literal family bases, validates their exact dependency plan, and folds existing product/projection and one-level Sigma/pullback lifting machinery. The four-layer `[A]; [B,C]; [D]; [E,F]` witness checks early/middle/final occurrences, pairing, an internal base-arrow cell, nested mixed factorization, and `homd_int`; predecessor profiles and their two/four-binding explicit Core remain exact. |
| `DISPLAYED-MIXED-GRADUATE-1` | complete; D-DTTLF-USABILITY-027 approved as proposed after checkpoint `ddc78c250970f62c09d822a39a16502f41c75db1` | generic positive and mixed witnesses | Graduates arbitrary finite depth/width only for the canonical positive sibling-layer/Sigma normal form, together with the exact final canonical mixed classifier, nested eta, internal base-arrow cell, and `homd_int` consumer. Retains explicit performance, general-curry, arbitrary-variance, pullback-hidden-classifier, arbitrary-DAG, and unrestricted-`:^nd` non-claims. |
| `MIXED-CONST-FOLD-0B` | deferred; not on the usability critical path | a concrete consumer or generic proof-conversion qualification | Transfer the active constant-`Cat` Hom fold only through a generic proof-aware nested conversion path. Do not add mirrors, coercions, owner-specific checker logic, or an external oracle. |
| `TEXT-PARITY-MIXED-1` | pending | semantic graduation | Bring the text adapter to parity with the graduated mathematical API and fail closed outside it. |
| `DISPLAYED-ND-CONSUMERS-N` | future, consumer-led | concrete requested coherent bodies | Expand recursively supported `^nd` body constructors while preserving internal coherence ownership. |

## Frozen `MIXED-NEST-0A` Boundary

The first slice is deliberately smaller than the final nested binder.

It may:

- transfer the existing opaque `Hom_catd` and `Transf_catd` signatures;
- transfer exactly their two fibre-projection rules, the
  `Hom_catd(Functor_catd(...))` family fold, and the existing `Op_catd` fibre
  projection required to type the negative endpoint;
- reuse the existing `Functor_catd`, `Op_catd`, `Op_func`, `Pi_cat`,
  `piapp0`, `Functord_cat`, `Transf_cat`, and generic action owners;
- add one isolated root-only successor profile;
- add typed constructors for:
  - `Catd_cat Z`,
  - `Op_cat K`,
  - a contravariant section of `Op_catd E`,
  - a general mixed `Functor_catd A B`,
  - `Hom_catd E X Y`,
  - and the rich `Functord_cat C H` category;
- construct the exact canonical nested classifier; and
- demonstrate the `Hom_catd(Functor_catd(...))` to `Transf_catd` runtime
  fold in the TypeScript kernel.

It may not:

- edit `emdash3_2.lp`;
- add a new mathematical owner or computation;
- claim that constructing the classifier is already recursive binder
  elaboration;
- add a second AST, checker, evaluator, or external coherence witness;
- weaken existing fail-closed behavior;
- alter earlier profiles; or
- promote the new profile to the browser/text product.

If an exact active declaration or rule fails generic subject checking, stop
and record the minimal dependency/refinement gap. Do not patch the checker or
duplicate a semantic body merely to force the slice through.

## Validation Policy

Use proportional gates:

1. focused transfer and canonical-classifier tests;
2. focused negative/profile-isolation tests;
3. root typecheck/lint;
4. the bounded active-kernel check when active names/computation are relied
   upon;
5. focused Lambdapi conformance only for the promoted mixed judgments; and
6. the aggregate root suite only at a coherent semantic checkpoint, not
   after documentation-only or small follow-up edits.

Do not repeatedly run the repository's long aggregate gate. Record and reuse
an unchanged green checkpoint when the changed surface cannot affect it.

## `MIXED-NEST-0A` Implementation Result

The first slice is implemented at checkpoint
`77f79bf8e139d856965f41733d3aeff9ffefd9d1` without an active-kernel edit.

The generic transfer adds:

- opaque existing `Hom_catd` and `Transf_catd` declarations;
- the existing `Op_catd` fibre projection needed by negative sections;
- the existing `Hom_catd` and `Transf_catd` fibre projections; and
- the existing
  `Hom_catd(Functor_catd(A,B),FF,GG) -> Transf_catd(A,B,FF,GG)`
  fold.

All four rules report `typescript-checked`. No external subject-reduction
oracle, proof-time mirror, intrinsic owner, or owner-specific checker path is
used.

The isolated root profile adds seven typed direct-TypeScript operations:

- `oppositeCategory`;
- `displayedCategoryCategory`;
- `oppositeDisplayedFamily`;
- `mixedDisplayedFunctorFamily`;
- `mixedDisplayedHomFamily`;
- `mixedDisplayedTransforFamily`; and
- `displayedFunctorCategory`.

Together with existing `constantDisplayedFamily`, `section`, and
`displayedFunctor`, they construct and check:

```text
Functord_cat C
  (Hom_catd
    (Const_catd K (Catd_cat Z))
    Ebar
    Dbar).
```

A second witness constructs `Functor_catd(A,B)`, its negative/positive
sections `FF` and `GG`, and observes the exact mixed-family runtime fold to
`Transf_catd(A,B,FF,GG)`.

This is classifier qualification, not yet recursive lowering of a nested
surface abstraction. `compileDisplayedContextual` remains fail-closed on the
nested abstraction node until `MIXED-NEST-1A`.

Focused validation:

- 4/4 generic transfer tests pass;
- 3/3 canonical classifier/fold/profile-isolation tests pass;
- 6/6 syntax-parity inventory tests pass after classifying the seven new
  constructors as the already-deferred typed-resolver seam;
- affected ESLint passes;
- root TypeScript typecheck passes; and
- the pre-edit bounded active-kernel `make check` passes.

The first cold inherited compilation took approximately 84-96 seconds; the
three profile tests took 104.3 seconds inside their test process. Compilation
is cached within a process. No performance redesign is included in this
semantic tranche.

The pre-edit root `check:ts` aggregate reached its known long CPU-bound phase
and then failed after approximately 25 minutes in the unrelated
`v3_2_release_completion_tests.ts` README assertion: current `README.md`
does not contain the older `release-ready exact profile` phrase. Neither file
is changed by this tranche. The failure is recorded as baseline evidence and
the long aggregate is not repeated here.

## `MIXED-NEST-1A0` Architecture Audit

The post-`MIXED-NEST-0A` source audit corrects the original wording of the
next row. The existing rejected `categorical-abstraction` node is the
ordinary `^f` node:

```text
lambda^f x : A. body : Functor_cat A B.
```

It is recursively lowered by ordinary product/curry structure. It cannot be
reused as the canonical inner abstraction:

```text
z :^n Z ; E[k^-;z] |- D[k;z],
```

whose result is a displayed functor, hence an object of:

```text
Functord_cat (E[k^-]) (D[k])
  = Hom_cat (Catd_cat Z) (E[k^-]) (D[k]).
```

Treating that result as an ordinary `Functor_cat` object would lose the
displayed base-arrow/fibre-arrow action and would violate the internalization
rule.

The existing `displayedFunctorLambda` is also not already the missing
solution. It:

- receives closed `KernelExpression` source and target families over one
  fixed base;
- hides one base token and one fibre token;
- lowers only identity, eta, finite closed displayed-functor composition, and
  the qualified section weakening; and
- returns a closed `Functord_cat E D` term.

Inside the canonical outer context, however, `Ebar[k^-]` and `Dbar[k]` are
context-indexed objects of `Catd_cat Z`, not closed
`CoreCategoricalDisplayedFamily` handles. The current IR has no sound route
that feeds those open endpoint objects into `displayedFunctorLambda` while
also synthesizing their dependence on the outer fibre variable.

The active Lambdapi kernel establishes the type but not a general
introduction law:

- `Nested_telescope_catd` is the transparent
  `Hom_catd(Const_catd K (Catd_cat Z),Ebar,Dbar)` classifier;
- `Nested_telescope_cat` is the corresponding
  `Functord_cat C (...)` category;
- `Hom_catd` supplies the mixed-variance family and fibre projection;
- `Functor_catd_func` internalizes formation of the mixed functor family;
- `Eval_funcd` supplies only the documented constant-domain evaluation
  direction; and
- `homd_int` supplies one important already-coherent internal-hom consumer.

There is no selected general displayed-curry/introduction owner in the
active source that converts an open inner displayed abstraction into an
inhabitant of `Nested_telescope_cat`. The Foundations explicitly leave
arbitrary mixed-domain evaluation and general contravariant occurrence
lowering open. A TypeScript-only case would therefore have to do one of the
following unsound or unscalable things:

1. reinterpret an ordinary functor as a displayed functor;
2. accept pointwise object functions plus external naturality evidence;
3. fabricate the missing base-arrow action;
4. hide an unreviewed coercion between contextual endpoint terms and closed
   family handles; or
5. recognize only eta of an already coherent term and mislabel it general
   nested abstraction.

All five are rejected.

### Architectural consequence

The broad architecture remains valid, but its next dependency is now
measured precisely:

> The classifier-directed abstraction algebra needs a displayed
> curry/introduction operation before the contextual compiler can soundly
> accept the canonical nested abstraction node.

This is not evidence that `Hom_catd`, `Functor_catd`, or the existing
displayed kernel is inconsistent. It is a closure/usability operation not
yet selected by the kernel library. The next design must first decide whether
that operation is:

- a transparent composite of existing pullback, fibrewise product, Sigma,
  evaluation, ordinary/internal Hom, and generic action owners;
- a sequential-totalization/external-product construction whose intermediate
  family is worth naming; or
- one smallest new functor-level semantic owner with projection rules.

The preference order is exactly the SOP order: derive a semantic composite
first; add a stable primitive only after a concrete consumer and an
owner-position probe show that the composite cannot expose the required
computation.

### Frozen `MIXED-CURRY-0A` design/probe boundary

`MIXED-CURRY-0A` may:

- inventory and type-check the existing ingredients in ignored temporary
  probes;
- formulate the canonical uncurried input and curried output at the
  `Catd_cat`/`Hom_catd` level;
- compare direct displayed curry, sequential totalization, and repeated
  pullback/Sigma presentations;
- test a transparent candidate at its intended owner position in a temporary
  full-file copy;
- require one point projection and one base-arrow consumer;
- require the result to remain iterable through generic `fapp*`/`tapp*` and a
  later `homd_int` consumer; and
- produce a separate exact implementation proposal.

It may not:

- edit `emdash3_2.lp` or `emdash3_2_checks.lp`;
- add a TypeScript nested-abstraction case;
- select a primitive merely because it is easier to transfer;
- add external coherence equations;
- claim arbitrary nested depth; or
- authorize the eventual active-kernel implementation.

The design result must state:

1. the complete type of the uncurried input;
2. the complete type of the curried output;
3. how negative endpoint variation is owned;
4. the point/object projection;
5. the base-arrow action route;
6. how higher action remains under generic owners;
7. a negative case that must not collapse; and
8. whether the implementation is transparent-derived or genuinely primitive.

The proposed gate is
`H-DTTLF-USABILITY-MIXED-CURRY-01 /
D-DTTLF-USABILITY-022`. It authorizes only this bounded design and temporary
probe tranche. Any active mathematical owner/rule remains a later,
separately reviewed decision.

## `MIXED-CURRY-0A` Result And Architecture Correction

The deeper owner-position audit rejects the assumption that one ordinary
displayed curry is already latent in the fixed-base product closure.

### 1. The naive uncurried input is not well-typed

For the plain mixed family:

```text
A : Catd(Op_cat K)
B C : Catd K
Functor_catd(A,B)[k] = Functor(A[k^-],B[k]),
```

the desired curried output would be:

```text
Functord_cat C (Functor_catd A B).
```

An ordinary displayed-curry attempt would need an input resembling:

```text
Functord_cat (P(C,?A)) B,
```

where `?A : Catd K`. There is no canonical such `?A`. `Op_catd A` reverses
the fibre categories but retains the base `Op_cat K`; it does not turn a
family over `K^op` into a family over `K`. `Pullback_catd` can change a base
only along an explicitly supplied functor, and arbitrary `K` has no canonical
functor `K -> K^op`. Reusing `A` as a covariant sibling would therefore erase
exactly the variance that `Functor_catd` owns.

This is also the required negative non-collapse case:

```text
F[k] : Functor(A[k^-],B[k])
a[k] : A[k^-]
```

does not define a covariantly natural `F[k](a[k])` for arbitrary varying
`a`. Along `p : k -> k'`, `A` supplies `A[p] : A[k'] -> A[k]`, not the
forward argument transport that ordinary displayed evaluation would require.
The constant-domain `Eval_funcd` is sound precisely because this obstruction
disappears for a constant `A`.

### 2. Sequential totalization identifies a real two-sided context, but not
the canonical curry

At the plain Cat-valued level, existing owners type the following
Grothendieck-style **candidate context** without changing the active kernel:

```text
Aint
  = Op_cat(Sigma_cat(Op_catd A))

qA
  = Op_func(Sigma_proj1_func(Op_catd A))
  : Functor(Aint,K)

M(C,A)
  = Sigma_cat(Pullback_catd C qA)

r
  = qA o Sigma_proj1_func(Pullback_catd C qA)
  : Functor(M(C,A),K).
```

Objects of `M(C,A)` have the expected shape `(k,a,c)`. Its arrows combine:

- a base arrow `p : k -> k'`;
- the contravariant source relation from `a` to `A[p](a')`; and
- the covariant relation from `C[p](c)` to `c'`.

Consequently, the following is a well-typed candidate input:

```text
s : Obj(Pi_cat(Pullback_catd B r))
```

It appears to contain the two-sided uncurried data required by a prospective
map:

```text
mixed-curry(s)
  : Obj(Functord_cat C (Functor_catd A B)).
```

Its point equation would have the shape:

```text
mixed-curry(s)[k](c)(a)
  = s[(k,a,c)].
```

The base-arrow action would come from the section action of `s` on the
canonical mixed-total arrow, and higher action would remain under generic
`piapp*`, `fapp*`, and `tapp*` owners.

This is a useful design discovery, not yet an emdash theorem or an
implementation authorization. The current audit has established that the
context and candidate source/target types are meaningful; it has not proved
the universal correspondence, its inverse, or all object/base-arrow/higher
computations. The active kernel has no owner that maps the section on the
left to the displayed functor on the right, nor a selected computational
projection equating the two. Adding one would first require a mathematical
qualification tranche. It would be a new closure operation, not a TypeScript
transfer detail, but its present absence is not evidence of impossibility or
inconsistency.

### 3. The canonical nested telescope is one enrichment level higher

The actual witness is:

```text
Functord_cat C
  (Hom_catd
    (Const_catd K (Catd_cat Z))
    Ebar
    Dbar).
```

Its inner fibre is:

```text
Hom_cat (Catd_cat Z) Ebar[k^-] Dbar[k]
  = Functord_cat Ebar[k^-] Dbar[k],
```

not merely `Functor_cat A[k^-] B[k]` for Cat-valued `A` and `B`. The
constant-`Cat` fold:

```text
Hom_catd(Const_catd K Cat_cat,X,Y)
  -> Functor_catd(Op_func X,Y)
```

therefore does not apply to `Const_catd K (Catd_cat Z)`. A general curry here
would require the corresponding Cat-enriched/tensored or recursively mixed
context construction for the category `Catd_cat Z`, together with its
object, base-arrow, and higher projections. Such a construction is
mathematically plausible, but its exact type and laws have not yet been
settled. Neither ordinary product curry, the constant-domain `Eval_funcd`,
nor the one-way `sigma_functord_sec` bridge supplies it today.

### 4. Selected result

`MIXED-CURRY-0A` therefore selects none of the three premature
implementations:

1. no ordinary product/displayed curry, because its input is ill-typed;
2. no sequential-Sigma term mislabeled as the canonical enriched curry,
   because the final introduction map is absent; and
3. no new opaque primitive merely to make the TypeScript case pass.

The long-term recursive architecture remains classifier-directed. A nested
surface abstraction may factor an expression back to an already-coherent
internal term—eta, composition, projection, pairing, evaluation, and later
qualified owners—without accepting pointwise functions or external
naturality equations. The first `MIXED-NEST-1A` implementation must begin
with such recursive eta/factorization and fail closed outside the selected
constructor algebra. A future general mixed-context/tensor-hom closure may
broaden that algebra, but it is a separate mathematical plan rather than an
implicit requirement of the TypeScript frontend.

This separates semantic feasibility from frontend feasibility:

- qualifying a general two-sided or enriched curry is the non-mechanical
  mathematical task;
- once that owner and its computations exist, TypeScript construction-IR
  lowering to it is expected to be systematic and comparatively mechanical;
- before that qualification, recursive factorization is already sound and
  mechanically extensible over each internally coherent constructor in the
  selected algebra, but it must not claim arbitrary-body abstraction.

### 5. Dependency-ready action slice

Before freezing the new contextual IR, TypeScript can close an existing
authority gap needed by every later action witness. The active kernel already
owns:

```text
homd_int(FF)[x]
  -> homd_src_func(FF,x)

homd_src_func(FF,x)[u]
  -> homd_src_sec(FF,x,u)

homd_src_sec(FF,x,u)[y]
  -> homd_tgt_func(FF,x,u,y)

homd_tgt_func(FF,x,u,y)[v]
  -> homd_(FF,x,u,y,v).
```

The TypeScript displayed-ND foundation transfers `Homd_target_catd` and
`homd_int`, but not this direct projection cascade.

Implementation measured the complete dependency closure rather than hiding
it behind local mirrors or a derived shortcut:

- nine declarations:
  `hom_con`, `hom_`, `fib_cov_tapp0_func`, `homd_`,
  `Functor_catd_fapp0_func`, `Homd_target_section_catd`,
  `homd_src_func`, `homd_src_sec`, and `homd_tgt_func`;
- the four direct `homd` projections above;
- the two existing `Functor_catd_func` object projections;
- the existing `Op_catd_func`, `Op_func`, `hom_int`, `hom_`, and generic
  identity object projections needed to compute
  `HomPresheaf_Z(x)[y]` internally to
  `Functor_cat(Op_cat(Hom_cat Z x y),Cat_cat)`; and
- the exact transparent
  `Functor(A,B) ≔ Obj(Functor_cat(A,B))` classifier computation.

`Fibre_cat` remains a transparent notation and is expanded to canonical
`fapp0` in the transfer record rather than duplicated by a local alias.
The inferred source and target arguments of the `Op_func` and `homd`
projection patterns remain typed wildcards, matching the active kernel's
stable-head discipline across opposite-category normalization.

All twelve runtime entries typecheck directly through the generic transfer
runtime. Once the complete source computation prefix was present, the earlier
category-presentation proof fallback became unnecessary and was deliberately
removed. No external oracle, proof-time exception, declaration-refinement
feature, owner-specific checker/evaluator branch, or new mathematical rule is
used.

The root `fibred-displayed-mixed-nest-1` profile now exposes:

```text
displayedInternalHom(FF)
  : Functord(Op_catd(E),Homd_target_catd(D))

displayedInternalHomEndpointFamily(FF,x,u,y,v)
  : Catd(Op_cat(Hom_cat K x y)).
```

The second constructor returns the direct internally coherent
`homd_(FF,x,u,y,v)` family after checking
`u : E[x]` and `v : D[y]`. The first and final runtime projections are
exercised explicitly in the regression suite. These operations are recorded
in the syntax-parity inventory as typed resolver seams; no text syntax is
promoted in this slice.

This completion does not provide the rejected general displayed curry, a
recursive nested-abstraction IR, arbitrary-depth lowering, or unrestricted
`:^nd`. It establishes that the existing internal object/base-arrow action
package needed by those later designs is executable in TypeScript.

The frozen proposal gate is:

```text
H-DTTLF-USABILITY-MIXED-ACTION-01 /
D-DTTLF-USABILITY-023
```

Under the user's standing unattended delegation, this bounded
existing-authority transfer may proceed after exact staged review. Human
supersession remains authoritative.

## Frozen `MIXED-NEST-IR-0C` Recursive Factorization Boundary

The post-action code audit and one bounded executable probe establish an
important simplification. The outer coherent eta already works:

```text
H = Hom_catd
      (Const_catd K (Catd_cat Z))
      Ebar
      Dbar

nested : Functord_cat C H

displayedContextLambda(c : C, H, nested[c])
  ==> nested.
```

The TypeScript probe compiled the result as a checked `displayed-functor`
whose explicit Core was exactly the original `nested` reference. Therefore:

- the generic displayed contextual compiler already owns the outer
  `λ^fd c. nested[c]` eta;
- no new outer curry, product, Sigma, or contextual compiler is required for
  that case; and
- the missing usability datum is the explicit **inner** displayed
  abstraction
  `λ^fd e. nested[c](e)`, whose result remains the same coherent object of
  `H[k]`.

### Selected construction-only IR

The first implementation adds only the following first-order construction
forms:

1. a nested source-object classifier carrying:
   - outer base `K` and its locally nameless index;
   - inner base `Z` and its locally nameless index;
   - the constant classifier family
     `Const_catd K (Catd_cat Z)`;
   - negative source section `Ebar`;
   - positive target section `Dbar`; and
   - source versus target endpoint polarity;
2. a typed nested displayed-application node recording the coherent
   indexed subject, hidden inner base token, and inner fibre token; and
3. a nested displayed-abstraction node recording the callback-once body and
   the already-coherent subject to which eta factors.

These forms are contextual frontend data only. They introduce no explicit
Core owner and cannot escape an enclosing contextual abstraction.

### Selected typed API shape

The direct TypeScript witness has the shape:

```ts
displayedContextLambda([{ name: 'c', family: C }], H, ([c]) => {
    const inner = apply(nested, c);
    return nestedDisplayedFunctorLambda(
        'e',
        inner,
        e => apply(inner, e)
    );
});
```

`nestedDisplayedFunctorLambda` derives the complete classifier from
`inner`. It does not accept caller-supplied variance or naturality evidence.
It is enabled only when:

- `inner` is an open `indexed-object` at the active outer base;
- its family has the exact stable shape
  `Hom_catd(Const_catd K (Catd_cat Z),Ebar,Dbar)`;
- the constant family and `Catd_cat Z` indices match;
- the callback returns the typed application of that same coherent `inner`
  subject to the fresh inner fibre token; and
- the hidden inner base and fibre tokens occur exactly in that eta
  application.

The callback is evaluated exactly once and discarded. Normalized evidence
uses locally nameless indices and is deeply frozen.

### Lowering

The nested abstraction removes only its fresh inner base/fibre usage and
retains the outer `k,c` usage of the factored subject. The displayed
contextual compiler handles the new node by recursively compiling that
subject through the already-working outer wiring. Consequently:

```text
λ^fd c. (λ^fd e. nested[c](e))
```

lowers to the same internal `nested` package. Its object, base-arrow, and
higher behavior remain owned by `nested : Functord_cat C H`; the frontend
does not reconstruct any of them pointwise.

### Rejected cases

The first slice fails closed for:

- a family that is not the canonical `Hom_catd`/`Catd_cat` shape;
- a different coherent subject in the body;
- a constant, source token, pair, composition, or other pointwise body;
- escaped or foreign inner tokens;
- caller-selected variance;
- an arbitrary contextual `Functord` body requiring the absent general
  displayed curry; and
- unrestricted nested `:^nd`.

The construction IR is intentionally recursive, but this slice proves one
explicit inner eta layer only. Iteration, constructor composition, arbitrary
finite mixed depth, and action consumption remain subsequent measured
tranches.

The frozen gate is:

```text
H-DTTLF-USABILITY-MIXED-NEST-02 /
D-DTTLF-USABILITY-024
```

Under the user's standing unattended delegation, this exact no-new-semantics
implementation may proceed after the proposal checkpoint and exact staged
review. Human supersession remains authoritative.

## `MIXED-NEST-1A` Implementation Result

The frozen construction-only slice is implemented without adding the absent
general displayed curry. The public mixed profile accepts the exact
TypeScript construction:

```text
displayedContextLambda([{ name: 'c', family: C }], H, ([c]) => {
    const inner = apply(nested, c);
    return nestedDisplayedFunctorLambda(
        'e',
        inner,
        e => apply(inner, e)
    );
});
```

where:

```text
H      = Hom_catd(Const_catd K (Catd_cat Z),Ebar,Dbar)
nested : Functord_cat C H.
```

The scoped builder now has:

- a construction-only `nested-indexed-object` classifier carrying both the
  outer contextual index and hidden inner base index;
- one `typed-nested-displayed-application` node that distinguishes the
  negative source endpoint from the positive target endpoint;
- one `nested-displayed-abstraction` node that eliminates only the hidden
  inner base/fibre slots; and
- the exact `categorical.mixed-nested-displayed-eta` evidence row, normalized
  with locally nameless indices and deeply frozen.

The callback is invoked exactly once. It must return the application of the
same coherent `inner` subject to the fresh fibre token. The displayed
contextual compiler recursively compiles that subject through the established
outer wiring, so the checked explicit result is exactly:

```text
free nested
```

with inferred and expected Core types equal. This is the intended semantic
result: `nested` already owns its object, base-arrow, and higher action. The
frontend exposes one explicit inner eta without reconstructing those actions
pointwise.

Focused negatives reject a noncanonical target family, a pointwise body, a
different coherent subject, escaped/foreign tokens, and use outside the mixed
profile. The executable syntax-parity inventory records the new mathematical
API method but does not claim text syntax for it.

Validation is proportional to the shared TypeScript delta:

- the new focused suite passes 5/5;
- the existing mixed-profile and syntax-parity suites pass 9/9 together;
- root typechecking and targeted lint pass;
- `git diff --check` passes; and
- the single required `./scripts/pnpmw run check:ts` completed workspace
  validation, typechecking, and full lint, then reported only the same two
  unrelated stale README phrase assertions already recorded for
  `MIXED-NEST-ACTION-0B`.

No aggregate rerun is required. `MIXED-NEST-1A` proves one explicit inner
factorization layer. It does not yet prove iteration, arbitrary finite mixed
depth, general displayed curry, unrestricted `:^nd`, or consumption of the
factored package's internal base-arrow/higher action. Those are the measured
dependencies of `MIXED-NEST-ACTION-1B` and later rows.

## `MIXED-NEST-ACTION-1B` Audit And Frozen Boundary

Two no-edit probes distinguish the already-working outer package from the
missing nested consumer.

First:

```text
displayedInternalHom(factored)
```

already checks. This applies `homd_int` to:

```text
factored : Functord_cat C H
```

and therefore consumes the outer displayed functor. It does not prove that
an object produced inside the mixed family `H` is recognized as the inner
displayed functor that `H[y]` denotes.

The stronger probe forms:

```text
p       : Hom K x y
c       : C[x]
move    = apply(factored,p) : Functor(C[x],H[y])
inner   = apply(move,c)     : Obj(H[y])
```

where:

```text
H = Hom_catd(Const_catd K (Catd_cat Z),Ebar,Dbar).
```

The existing Core checker accepts `move`. It infers `inner` at:

```text
Obj(Fibre_cat H y).
```

The active runtime then supplies the exact conversion chain:

```text
Fibre_cat(Hom_catd(Const_catd K (Catd_cat Z),Ebar,Dbar),y)
  -> Hom_cat
       (Fibre_cat(Const_catd K (Catd_cat Z),y))
       (Ebar[y^-])
       (Dbar[y])
  -> Hom_cat (Catd_cat Z) (Ebar[y^-]) (Dbar[y])
  -> Functord_cat Z (Ebar[y^-]) (Dbar[y]).
```

The current surface retains only the generic classifier:

```text
inner : object(Fibre_cat H y),
```

so `displayedInternalHom(inner)` rejects early with
`EXPECTED_DISPLAYED_FUNCTOR`. This is a frontend result-classifier gap, not a
missing action, curry, or kernel theorem.

A bounded no-edit probe reclassified the same Core term with the derived
displayed-functor classifier. The existing Core checker accepted the
definitionally convertible expected type, and `displayedInternalHom` accepted
the result. No coercion term or new rewrite was needed. Syntactic inferred and
expected types need not be identical; checked definitional conversion is the
relevant boundary.

### Exact implementation

`MIXED-NEST-ACTION-1B` may:

- recognize only a `functor-object` result category whose family has the exact
  canonical mixed shape already recognized by `MIXED-NEST-1A`;
- require the constant classifier
  `Const_catd K (Catd_cat Z)`;
- derive the negative and positive endpoint families by the existing internal
  section projections `Ebar[y^-]` and `Dbar[y]`;
- classify the unchanged application term as:

  ```text
  displayed-functor
    (base Z)
    (source Ebar[y^-])
    (target Dbar[y]);
  ```

- let the ordinary final Core checker validate the conversion through the
  existing runtime;
- expose that refinement automatically from the typed application result,
  with no user cast or caller-supplied endpoint families;
- compile one outer base-arrow transport through the factored package; and
- pass the transported inner result to the existing `homd_int` typed consumer.

It must not:

- add a Core expression, coercion, cast, proof, or mirror;
- add or change a Lambdapi owner, runtime rule, or unification rule;
- infer a displayed-functor classifier for an arbitrary object category;
- normalize and guess arbitrary category heads;
- accept a noncanonical `Hom_catd`, a constant fibre other than
  `Catd_cat Z`, or caller-supplied variance/coherence data;
- reconstruct object or arrow action pointwise;
- add a new public convenience method, text syntax, or browser behavior; or
- claim general displayed curry, arbitrary mixed depth, or unrestricted
  `:^nd`.

Focused evidence must show:

1. the exact nested eta still lowers to the original coherent `nested`;
2. outer base-arrow application compiles through the existing displayed
   transport owner;
3. applying that transport to `c : C[x]` has the internally derived
   `displayed-functor` classifier over `Z`;
4. the unchanged Core term checks against the derived `Functord_cat` type by
   existing conversion;
5. `displayedInternalHom(inner)` compiles through the existing `homd_int`
   owner; and
6. noncanonical target families retain the generic `object` classifier and
   fail closed at the displayed consumer.

The frozen gate is:

```text
H-DTTLF-USABILITY-MIXED-NEST-ACTION-01 /
D-DTTLF-USABILITY-025
```

This is an existing-authority, no-new-semantics correction. Under the user's
standing unattended delegation, it may proceed after the proposal checkpoint
and exact staged review, with human supersession.

## `MIXED-NEST-ACTION-1B` Implementation Result

The frozen result-classifier refinement is implemented in the scoped
categorical surface. It is intentionally not a new public operation.

When ordinary functor object application has the exact target:

```text
Fibre_cat
  (Hom_catd(Const_catd K (Catd_cat Z),Ebar,Dbar))
  y,
```

the surface now derives:

```text
source = piapp0 (Op_catd
                   (Const_catd K (Catd_cat Z)))
                Ebar y
target = piapp0 (Const_catd K (Catd_cat Z)) Dbar y
```

and retains the application term with classifier:

```text
displayed-functor Z source target.
```

The term is not wrapped, rewritten, or cast. Its final compilation asks the
ordinary Core checker to check the inferred:

```text
Obj(Fibre_cat H y)
```

against:

```text
Obj(Functord_cat Z source target).
```

The existing mixed-family fibre, constant-family fibre, and
`Hom_cat(Catd_cat)` runtime rules establish that conversion. Thus the
TypeScript surface recovers information already present in the target
classifier while the generic checker remains the trust boundary.

The executable witness now performs:

```text
factored                         : Functord_cat C H
move     = factored[p : x -> y] : Functor(C[x],H[y])
inner    = move(c)               : Functord_cat Z Ebar[y^-] Dbar[y]
homd_int(inner)                  : internal next-Hom package.
```

Direct object projection `factored[y](c)` receives the same refinement.
A `Hom_catd` over a constant category other than `Catd_cat Z` remains a
generic object and is rejected by `displayedInternalHom` with
`EXPECTED_DISPLAYED_FUNCTOR`.

Measured deltas are:

- zero active Lambdapi owners, rules, or unification clauses;
- zero Core terms, intrinsic owners, checker branches, or evaluator branches;
- zero coercion/cast terms or user-supplied endpoint/coherence data;
- zero public program methods, text syntax, or browser behavior; and
- one bounded construction-time classifier recognizer plus its use at typed
  ordinary object application.

Validation is:

- the new focused suite passes 3/3;
- the new suite plus the existing mixed transfer, mixed profile, and nested
  factorization suites pass 16/16;
- root typechecking, targeted lint, and `git diff --check` pass; and
- the single required `./scripts/pnpmw run check:ts` passes workspace
  validation, root typechecking, and full lint. Its aggregate test phase
  reports only the same two unrelated stale README phrase assertions already
  recorded for the preceding tranches.

The aggregate is not rerun. No active Lambdapi file changed, so the recent
green kernel authority/conformance evidence is carried forward.

This completes the first actual inner-action consumer. It still does not
prove a general curry, arbitrary mixed nesting, arbitrary category-head
refinement, or unrestricted displayed coherence. The next dependency-ready
work is the generic dependency-plan fold for arbitrary finite positive and
qualified mixed telescope depth.

## `DISPLAYED-TELESCOPE-GENERIC-1` Audit And Frozen Boundary

The implementation audit finds no new semantic owner between the completed
two-binding and four-binding presentations and arbitrary finite **canonical
layered** depth. Those two implementations are instances of one recursion
which is already present in the scoped builder:

- `displayedFamilyTree` forms an arbitrary nonempty left-associated
  fibrewise product and `displayedProjectionWiring` derives every factor
  projection;
- `liftDisplayedCompilationThroughNextFamily` carries any already compiled
  displayed map through one later Sigma context by the existing
  `sigma_functord_sec`, Sigma projection, pullback, and section-weakening
  owners; and
- `compileDisplayedContextual` recursively compiles supported typed
  occurrences, pairing, application, evaluation, nested factorization, and
  the other already qualified body nodes.

The current two-binding path spells out one lift. The current
`a; b,c; d` path spells out a product projection followed by one or two
lifts. Repeating the same generic helper is therefore an orchestration fold,
not a new curry, pointwise action synthesis, or mathematical closure.

The active kernel check is green with the 60-second bounded timeout. No
Lambdapi source, owner, rule, or unification clause changes in this slice.

### Canonical finite layer grammar

The qualified input is a nonempty sequence of nonempty sibling layers:

```text
L0 = A00, ..., A0m
L1 = A10, ..., A1n
...
Lr = Ar0, ..., Arq
```

with `r >= 1`. Let:

```text
K0 = K
Pi = Productd(Ai0,...,Aik)        -- left-associated when k > 0
K(i+1) = Sigma_cat Ki Pi.
```

Every family in `Li` is literally based on `Ki`. The next layer is admitted
only when its family base is exactly `K(i+1)`. The final layer `Lr` is not
totalized: the abstraction is a displayed functor over `Kr`, from `Pr` to a
target family also based on `Kr`.

The existing flat `displayedDependentContextLambda` input determines these
layers without caller flags:

1. consecutive families with the current literal base form one independent
   sibling layer;
2. the first different base must equal the Sigma total of the current
   layer's product; and
3. any other base transition fails closed with
   `DISPLAYED_BASE_MISMATCH`.

This is the usual contextual-presentation discipline. A family which depends
on only part of an earlier context must first be weakened or pulled back to
the complete current base. Bindings in one layer may be exchanged, paired,
or contracted through the already qualified fibrewise product structure.
Bindings on opposite sides of a genuine dependency transition are not
exchanged.

This grammar contains the completed cases:

```text
[A]; [B]
[A]; [B,C]; [D]
```

and extends them mechanically to such presentations as:

```text
[A,B]; [C]; [D,E,F]; [G,H].
```

It does not claim that every arbitrary dependency DAG has a canonical
presentation without explicit weakening/reindexing. It claims arbitrary
finite depth and finite sibling width for this dependency-plan normal form.

### Dependency-plan validation

The public program layer must still validate the semantic presentation before
the scoped builder runs.

For binding position `i` in layer `Lj`, its dependency evidence consists of:

- the root context position `0`; and
- every binding position in layers strictly before `Lj`;
- never another position in `Lj`.

The locally nameless reference from absolute dependency position `d` to the
prefix of absolute binding position `i` is `i - d - 1`. Every multi-binding
layer is submitted as one sibling group. The generic dependency planner must
return exactly:

- the root/prior-layer edge set just described;
- one `shared-minimal-base-siblings` group for every layer of width greater
  than one; and
- the complete prior-layer dependency chain for every binding.

The program rejects any mismatch. Callers cannot assert independence,
dependency, variance, or exchange by supplying a boolean flag.

### Generic lowering fold

For each layer, the scoped builder:

1. builds its left-associated displayed-family product tree;
2. derives a displayed projection compilation for every binding in that
   layer, using identity for a singleton;
3. carries each projection through every strictly later layer by repeated
   `liftDisplayedCompilationThroughNextFamily`;
4. creates the callback's indexed tokens at the final base, classified by
   those fully lifted target families;
5. maps every token ordinal to its final lifted compilation;
6. evaluates the callback exactly once and recursively compiles its body with
   `compileDisplayedContextual`; and
7. checks that the result is a displayed functor from the final layer product
   to the requested target family.

The same internal displayed owners determine object, base-arrow, and higher
action. The fold does not manufacture arrow variables, pointwise functions,
or external functoriality/naturality equations. Its normalized evidence uses
arrays of layers, bindings, original families, lifted families, and
locally-nameless body data rather than another fixed-arity tuple.

For the exact two-binding and four-binding canonical presentations, the new
mixed-profile path must emit the same explicit Core term as the completed
predecessor paths. This is a regression requirement, not a compatibility
alias: the older profiles retain their existing route, evidence rule, and
arity boundary unchanged.

### Mixed variance boundary

The context-presentation fold itself is positive/covariant. This does not
separate arbitrary depth from the mixed-variance requirement. The final layer
may target the already qualified canonical classifier:

```text
Hom_catd
  (Const_catd Kr (Catd_cat Z))
  Ebar
  Dbar.
```

Within that target, the negative endpoint, positive endpoint, base-arrow
action, `Transf_catd` fold, nested `^fd` eta, and `homd_int` consumption remain
owned by the completed classifier-directed mixed path. The generic telescope
must host that path at arbitrary positive contextual depth and must preserve
its unchanged Core/action package.

This slice does **not** recognize a canonical mixed classifier after an
arbitrary pullback or opaque equivalent presentation. It does not introduce
general two-sided/enriched curry, unrestricted mixed classifiers at every
earlier binding, contravariant context transitions, or general `:^nd`
coherence. Those need a separately qualified internal constructor or a
concrete consumer; syntactic normalization is not used to guess them.

### Profile and API boundary

Only the existing successor profile
`fibred-displayed-mixed-nest-1` enables the generic fold. In that profile,
`displayedDependentContextLambda` routes every canonical input with at least
two layers through the generic implementation.

The completed `fibred-displayed-chain-1`,
`fibred-displayed-chain-2a`, and
`fibred-displayed-nd-higher-1` profiles preserve their exact two/four-binding
behavior and evidence. One independent sibling layer remains the job of
`displayedContextLambda`; it is not silently reinterpreted as a dependent
telescope.

No new public construction method, string syntax, browser behavior, Core
expression, checker/evaluator branch, transfer declaration, runtime rule,
proof fallback, cast, or coherence datum is added.

### Required evidence

Focused evidence must establish:

1. generic two-binding lowering is explicit-Core-identical to
   DISPLAYED-CHAIN-1A;
2. generic four-binding lowering is explicit-Core-identical to
   DISPLAYED-CHAIN-2A;
3. a telescope beyond the selected arities, with at least four layers and
   more than one sibling block, compiles early-, middle-, and final-layer
   occurrences plus recursive pairing;
4. the beyond-arity result exposes a genuine displayed-functor classifier
   and its existing internalized base-arrow/cell consumer checks;
5. a canonical mixed target at the final layer still supports nested
   factorization and the completed internally derived `homd_int` path;
6. the callback executes exactly once and its generic layer/body evidence is
   deeply frozen;
7. wrong next bases, target-base drift, duplicate names, one-layer misuse,
   and unsupported mixed shapes fail closed; and
8. predecessor profiles continue rejecting presentations beyond their
   completed boundary.

Validation is proportional: new and affected displayed/mixed suites,
typechecking, targeted lint, and one final `check:ts` because shared surface
behavior changes. Recent green Lambdapi and unchanged cross-layer evidence is
carried forward; the repository-wide aggregate is not a routine gate.

The frozen gate is:

```text
H-DTTLF-USABILITY-DISPLAYED-TELESCOPE-GENERIC-01 /
D-DTTLF-USABILITY-026
```

This is a bounded no-new-mathematics implementation inside the already
approved arbitrary-finite/mixed continuation. Under the user's standing
unattended delegation, it may proceed after the proposal checkpoint and
exact staged review, with human supersession.

## `DISPLAYED-TELESCOPE-GENERIC-1` Implementation Result

The D-026 fold is implemented in the existing
`fibred-displayed-mixed-nest-1` profile. The public API remains
`displayedDependentContextLambda`; no second telescope constructor or caller
layer annotations were added.

The program now:

1. checks family ownership and duplicate names;
2. partitions the flat source-ordered bindings into consecutive literal-base
   sibling layers;
3. requires every base transition to be the Sigma total of the previous
   layer's left-associated product;
4. requires the target at the final layer base;
5. constructs locally nameless root/prior-layer dependency evidence;
6. submits every non-singleton layer as an independent sibling group; and
7. rejects the presentation unless the generic dependency planner returns the
   exact edge, chain, and sibling-group partition.

The scoped builder receives those same literal bases and independently
rechecks the canonical layer partition. For every binding it obtains the
factor projection from its own layer product and repeatedly applies the
existing one-level lifting helper through all later layer products. The
callback then sees all bindings as indexed objects at the final base with
their fully lifted families. The existing recursive contextual compiler
lowers the body from the final layer product to the target.

The new normalized evidence rule is:

```text
categorical.displayed-generic-dependent-context-bracket
```

It records arbitrary arrays of layer bases, sibling names, original families,
layer products, fully lifted binding families, and the locally nameless body.
The callback executes exactly once and the complete evidence tree is deeply
frozen.

The executable stress telescope is:

```text
[A]; [B,C]; [D]; [E,F].
```

It demonstrates:

- early `a`, middle `d`, and final `e,f` occurrences;
- recursive final-layer pairing;
- an internally checked base-arrow cell from the early projection;
- a final canonical
  `Hom_catd(Const_catd(Sigma(D),Catd_cat Z),Ebar,Dbar)` target;
- nested `^fd` eta inside that target; and
- outer base-arrow transport whose derived inner displayed functor is
  consumed by the existing `homd_int`.

The generic two-binding and four-binding routes serialize to the same lowered
explicit Core as the completed DISPLAYED-CHAIN-1A and DISPLAYED-CHAIN-2A
routes. Those predecessor profiles still take their old paths and still
reject the six-binding presentation.

Negative evidence rejects:

- a next family not based on the preceding layer total;
- a target at the wrong base;
- duplicate names;
- using the dependent constructor for one sibling layer; and
- predecessor-profile arity overreach.

Measured semantic deltas are:

- zero Lambdapi declarations, definitions, runtime rules, unification rules,
  or warning interactions;
- zero explicit Core owners or expression forms;
- zero checker, evaluator, transfer, proof, coercion, or external-oracle
  branches;
- zero public program methods, text syntax, or browser behavior; and
- one generic dependency-plan/lowering path plus its finite-layer evidence
  shape.

Validation is:

- the dedicated generic suite passes 6/6;
- the two predecessor and two mixed nested/action suites pass 22/22;
- root typechecking, targeted lint, full lint, workspace validation, and
  `git diff --check` pass;
- the bounded active Lambdapi check passes with no source change; and
- the one required `check:ts` reaches 1,256 tests: 1,201 pass, 51 are
  intentionally skipped, and four unrelated frozen-document/inventory
  assertions fail.

The four aggregate failures are exact baseline drift outside D-026:

1. the unchanged text-graduation audit still asserts that its unchanged
   parity inventory contains 68 methods, while that committed inventory now
   contains 78;
2. the unchanged migration-readiness test's broad retired-API regex matches
   current standalone reviewer fixture prose/source;
3. the unchanged release-policy test expects the retired
   `emdash-v3.2-mvp-1` README phrase; and
4. the unchanged release-completion test expects the retired
   `release-ready exact profile` README phrase.

The parity-audit source and all three publication/fixture boundaries are
unchanged from the D-026 baseline. The hour-long aggregate is not rerun.

The focused generic suite reports about 62.5 seconds of test-body work and
about 216.7 seconds wall time including two isolated profile constructions.
The complete buffered `check:ts` run reports about 3,693 seconds. This is a
measured validation-runner/performance boundary, not a semantic failure.
Further runner parallelism/caching remains in the existing deferred
test-parallelism plan; it is not folded into this usability tranche.

The exact implementation checkpoint is:

```text
6fa6f2ebdafe8f4bc8e80136a4aadcd3e9ae43fa
```

This completes arbitrary finite depth and finite sibling width for the
canonical positive layer normal form, including one canonical mixed target
at the final layer. It still does not graduate arbitrary dependency DAGs
without explicit weakening, arbitrary variance transitions, mixed
classifiers hidden behind pullbacks/equivalences, a general enriched curry,
or unrestricted `:^nd`. `DISPLAYED-MIXED-GRADUATE-1` is now the next
dependency-ready row.

## `DISPLAYED-MIXED-GRADUATE-1` Frozen Graduation Boundary

The post-implementation review finds no additional semantic owner or
frontend algorithm between D-026 and the exact arbitrary-finite claim. The
claim is justified parametrically:

1. every nonempty finite sibling layer has a left-associated product tree
   and one projection compilation for each factor;
2. `liftDisplayedCompilationThroughNextFamily` maps any compilation over
   layer `i` to the canonical pulled-back compilation over layer `i+1`;
3. finite iteration carries every binding projection to the final base;
4. the recursive contextual compiler consumes the resulting finite wiring
   map without inspecting telescope arity; and
5. the ordinary explicit-Core checker validates the resulting displayed
   functor and its internal action package.

The previous two-binding case exercises one lift. The previous four-binding
case exercises products and up to two lifts. The D-026
`[A]; [B,C]; [D]; [E,F]` witness crosses both former presentation
boundaries, includes two sibling products, and exercises three successive
Sigma transitions. The implementation loops over arrays; it contains no
remaining selected-arity branch in the mixed successor.

### Proposed exact graduation

Approve the following statement:

> In the `fibred-displayed-mixed-nest-1` TypeScript profile,
> `displayedDependentContextLambda` supports arbitrary finite depth and
> finite sibling width for the canonical positive displayed-context normal
> form. Consecutive same-base families form a sibling layer; every next layer
> is literally based on the Sigma total of the previous layer product; the
> final layer is the abstraction source. Variables may occur recursively in
> the already qualified typed contextual IR. Object/base-arrow/higher action
> is supplied by internal emdash owners. At the final layer, the exact
> canonical
> `Hom_catd(Const_catd K (Catd_cat Z),Ebar,Dbar)` result supports the
> qualified mixed classifier, nested displayed eta, `Transf_catd` conversion,
> and `homd_int` consumer.

This graduates a semantic/API architecture, not a string grammar, deployed
browser profile, whole-library transfer workflow, or global metatheory.

### Evidence retained by the graduation

The positive evidence is:

- arbitrary finite independent siblings through
  `displayedFamilyTree`/`displayedProjectionWiring`;
- arbitrary finite canonical layer iteration through the existing one-step
  lift;
- exact lowered-Core agreement with the completed two- and four-binding
  paths;
- a checked four-layer/two-sibling-block body containing early, middle, final,
  and paired occurrences;
- a checked internalized base-arrow cell at that depth;
- a checked canonical mixed final target with explicit nested `^fd` eta;
- base-arrow transport into an internally classified displayed functor; and
- successful consumption of that inner package by `homd_int`.

The negative evidence is:

- wrong next-layer base rejection;
- wrong final target-base rejection;
- duplicate binding rejection;
- one-layer dependent-constructor rejection;
- predecessor-profile overreach rejection;
- noncanonical mixed classifier rejection;
- pointwise/different-subject nested-body rejection; and
- no caller-provided dependency, variance, naturality, or coherence evidence.

The authority evidence is:

- the active Lambdapi v3.2 kernel remains the mathematical owner;
- its bounded check is green;
- the generic TypeScript LF checker validates the explicit Core without an
  oracle or owner-specific branch;
- the two/four predecessor profiles remain unchanged; and
- the exact implementation and ledger checkpoints are recorded.

### Explicit non-claims

The graduation must not be read as any of:

- arbitrary dependency DAG syntax without explicit weakening/reindexing to a
  canonical current base;
- exchange across a genuine dependency transition;
- contravariant or otherwise arbitrary context-layer transitions;
- recognition of a mixed classifier hidden behind arbitrary pullback,
  opaque definition, equivalence, or normalization search;
- arbitrary mixed classifiers at arbitrary earlier bindings;
- a general two-sided, enriched, or displayed curry;
- arbitrary pointwise nested `:^fd` body abstraction;
- unrestricted general `:^nd` coherence or all higher-cell consumers;
- groupoidal DTT closure;
- a proof of normalization, confluence, canonicity, consistency, or semantic
  soundness for the combined calculus;
- whole-library mechanical Lambdapi transfer;
- string-parser parity;
- browser/deployed-profile promotion; or
- a production-time or asymptotic performance guarantee.

The plain Cat-valued two-sided curry remains mathematically plausible but
absent as a selected active owner. The enriched curry needed for the full
canonical nested Hom setting remains less settled. If later qualified, its
TypeScript construction/lowering is expected to be systematic; neither is
required by or silently simulated in this graduation.

### Performance boundary

The finite algorithm terminates structurally on the number of layers and
bindings. That establishes mechanical semantic scalability, not efficient
normalization of every expanded term.

The checked four-layer witness is tractable but produces large explicit
pullback/product terms. The focused suite and complete aggregate measurements
show that current profile construction, serialization/checking, and the
single-process test runner are expensive. No constant-time, polynomial-size,
interactive-latency, or arbitrary-depth resource claim is made. DAG sharing,
declaration reuse, caching, and test parallelism remain performance work
separate from the sound layer-fold architecture.

### Downstream text boundary

After approval, `TEXT-PARITY-MIXED-1` may expose only this graduated
mathematical API:

- the existing `displayedDependentContextLambda` target semantics;
- canonical finite layer inference from declared family bases;
- already qualified recursive body forms;
- the exact canonical mixed final target and nested eta forms; and
- source-located failure for everything outside the graduated envelope.

Text parity must not invent a generic curry or parse its way around failed
internal factorization.

The exact gate is:

```text
H-DTTLF-USABILITY-DISPLAYED-MIXED-GRADUATE-01 /
D-DTTLF-USABILITY-027
```

Approve as proposed to record the exact graduation above and make
`TEXT-PARITY-MIXED-1` dependency-ready. Approval authorizes no new semantic
owner/rule, runtime behavior, parser implementation, browser promotion, or
remote Git operation.

## Git And Approval Boundary

Work in the existing dedicated
`goal/typescript-elaborator-v3.2` worktree/branch. The user has authorized
bounded local checkpoint commits for coherent green tranches and has
delegated approval of a presented bounded proposal when no immediate human
response arrives, always with human supersession.

Before each checkpoint:

- synchronize this ledger and affected handoff;
- inspect staged and unstaged diffs separately;
- exclude unrelated files;
- run `git diff --cached --check`; and
- record proportional validation.

This authorizes no push, PR, merge to `main`, publication, release, amend,
rebase, reset, squash, history rewrite, branch/worktree removal, or unrelated
cleanup.

## Persistent `/goal` Launch Prompt

```text
Continue implementing
docs/TYPESCRIPT_ELABORATOR_V3_2_MIXED_MODE_DISPLAYED_TELESCOPE_PLAN.md and
treat its Persistent /goal Launch Prompt as part of the objective.

Recover actual worktrees, branch ancestry, staged and unstaged changes,
active authority, completed displayed-bracket/ND-higher evidence, this
plan's living ledger, and linked decisions. Follow root AGENTS.md,
emdash2/AGENTS.md, and docs/PERSISTENT_GOAL_GIT_EXPERIMENTATION.md.

Advance the next dependency-ready slice toward genuinely usable arbitrary
finite displayed telescopes with classifier-directed mixed variance.
Prioritize the canonical nested
Functord_cat/Hom_catd/Transf_catd/homd_int witness before generalizing
presentation arity. Preserve the distinction between contextual
Sigma/product/pullback recursion and classifier-directed abstraction. Every
binder must construct an internal action package; never introduce external
naturality or variance evidence, and fail closed for unsupported coherence.

Treat the active Lambdapi v3.2 kernel as mathematical authority. A missing
TypeScript route is not permission for a new kernel rule. Audit existing
owners and dependencies first, use generic transfer/checking engines, and
make any genuine Lambdapi delta a separate measured proposal under the
nested SOP.

Keep string parsing, browser promotion, groupoidal closure, bulk
whole-library transfer, and unrestricted general :^nd outside this goal
until their dependency rows become ready. Use proportional focused gates;
do not repeat long aggregate validation for documentation-only or
semantically irrelevant changes.

The user authorizes bounded local checkpoint commits in the existing
goal/typescript-elaborator-v3.2 branch after a coherent tranche is green,
the living ledgers are synchronized, the exact staged diff is clean, and
unrelated work is excluded. If a newly frozen bounded proposal receives no
immediate human response, the standing unattended delegation may record a
separate approval/review with human supersession. No push, PR, merge,
publication, release, destructive history operation, branch/worktree
removal, or unrelated cleanup is authorized.

Continue through dependency-ready rows with minimal human supervision,
updating this plan whenever evidence changes the architecture. Stop for a
new mathematical owner/rule, a broader semantic claim, an unresolved
authority conflict, or an operation outside the stated Git boundary.
```

## Decision Ledger

- **2026-07-31 — mixed-mode correction approved.** The user agreed that the
  earlier separation of arbitrary depth from variance was too sharp and that
  “explicit arrow/cell binder” was misleading. Mixed variance and the
  complete internal action package are now graduation requirements.
- **2026-07-31 — dedicated successor selected.** The completed
  displayed-bracket plan remains historical authority for its bounded
  envelope. This file owns the mixed-mode/arbitrary-depth continuation.
- **2026-07-31 — `MIXED-NEST-0A` selected first.** The smallest executable
  dependency-ready slice is the existing-authority `Hom_catd`/`Transf_catd`
  transfer plus canonical typed classifier witness. It is intentionally not
  labeled completed nested abstraction.
- **2026-07-31 — negative-fibre dependency measured.** Generic subject
  checking found that TypeScript had the active `Op_catd` signature and
  involution but not its active fibre projection. `MIXED-NEST-0A` therefore
  includes that exact existing rule as a prerequisite, for two signatures
  and four transferred runtime rules total, with zero Lambdapi delta.
- **2026-07-31 — constant-`Cat` fold deferred at a generic seam.** The active
  `Hom_catd(Const_catd K Cat_cat,X,Y)` fold uses the proof-time
  `Pi_cat(Const_catd K A) ≡ Functor_cat K A` comparison inside the
  `Op_func(X)` argument. The generic runtime compiler can proof-check a whole
  subject comparison but does not use proof conversion while inferring that
  nested argument. This fold is not required by the canonical nested
  classifier or the selected `Transf_catd` witness, so `MIXED-NEST-0A`
  records it as a later generic proof-conversion qualification rather than
  adding a mirror, coercion, checker branch, or external oracle.
- **2026-07-31 — `MIXED-NEST-0A` implemented and focused-green.** The exact
  two-signature/four-rule generic closure, isolated profile, seven typed
  constructors, canonical nested classifier, and `Transf_catd` fold pass
  focused validation. The result deliberately leaves the recursive nested
  abstraction node to `MIXED-NEST-1A`. The bounded implementation checkpoint
  is `77f79bf8e139d856965f41733d3aeff9ffefd9d1`.
- **2026-07-31 — `MIXED-NEST-1A0` measured an introduction dependency.**
  The rejected ordinary `categorical-abstraction` node produces
  `Functor_cat`, whereas the canonical inner term is an object of
  `Functord_cat`. The existing direct displayed lambda accepts closed endpoint
  families and cannot soundly consume `Ebar[k^-]`/`Dbar[k]` as open family
  handles. The active kernel names the complete nested classifier but has no
  selected general displayed-curry/introduction owner. No TypeScript shortcut
  is implemented. The audit checkpoint is
  `5c8b79404ead2abc03c51f7e12a48de7cb752bb6`.
- **2026-07-31 — `MIXED-CURRY-0A` proposed.** The next bounded tranche is a
  no-active-edit design and owner-position probe comparing a transparent
  existing-owner composite, sequential totalization, and one smallest
  functor-level semantic owner. It must freeze object, base-arrow, and higher
  action before any active kernel or TypeScript implementation.
- **2026-07-31 — `MIXED-CURRY-0A` delegated approval recorded.** After the
  frozen bounded proposal was presented with no immediate human
  supersession, the user's standing unattended delegation authorizes its
  design and ignored temporary-probe scope. It does not authorize an active
  Lambdapi owner/rule or TypeScript lowering.
- **2026-07-31 — `MIXED-CURRY-0A` rejects ordinary curry.** `Op_catd`
  retains the opposite base, so the negative endpoint cannot be inserted as
  a covariant fibrewise-product sibling. A well-typed two-sided total context
  can be assembled for the plain Cat-valued `Functor_catd` case, but the
  final curry map is not an active owner and the canonical
  `Hom_catd(Const(Catd_cat Z),Ebar,Dbar)` target is one enrichment level
  higher. No active kernel or TypeScript semantic edit is made.
- **2026-07-31 — `MIXED-NEST-ACTION-0B` proposed and delegated approval
  recorded.** The next executable slice transfers only the active
  `homd_int` direct projection cascade and a typed consumer. It is a bounded
  existing-authority closure with zero Lambdapi delta. Under the user's
  standing unattended delegation it may proceed, subject to exact staged
  review and human supersession.
- **2026-07-31 — `MIXED-NEST-ACTION-0B` implemented and focused-green.**
  The measured closure is nine existing declarations and twelve exact source
  computation/projection rules. The initially expected four direct `homd`
  folds also require the existing transparent/internal
  `Functor`, `Functor_catd_func`, `Op_catd_func`, `Op_func`, `hom_int`,
  `hom_`, and generic identity object computations; no derived shortcut or
  local semantic mirror is installed. All entries compile through the
  generic declaration/runtime engines with direct TypeScript subject
  checking and no proof or external-oracle fallback. The mixed profile
  exposes rich `displayedInternalHom` and
  `displayedInternalHomEndpointFamily` consumers, and focused tests exercise
  the first and final folds. This does not implement nested abstraction.
  The bounded implementation checkpoint is
  `a31b8927910d32613c7d0fac1862317b08dbf920`; the required shared TypeScript
  gate and its unrelated baseline exception are recorded below.
- **2026-07-31 — `MIXED-NEST-ACTION-0B` validation boundary measured.**
  The new five-test transfer/consumer suite passed; its initially redundant
  whole-environment revalidation was then removed because the generic
  compiler had already subject-checked every new declaration and rule.
  Existing mixed-profile tests passed 3/3, the updated executable
  syntax-parity inventory passed 6/6, targeted lint passed, and
  `git diff --check` passed. The single required
  `./scripts/pnpmw run check:ts` completed workspace validation, typechecking,
  and full lint successfully. Its test phase reported only two unrelated
  pre-existing failures: the clean committed `README.md` from the later
  reader-first/reviewer publication commits no longer contains the obsolete
  `emdash-v3.2-mvp-1` and `release-ready exact profile` phrases still pinned
  by `v3_2_release_policy_tests.ts` and
  `v3_2_release_completion_tests.ts`. A focused rerun confirmed 9/11 release
  tests pass and exactly those two unchanged README assertions fail. No file
  in that release-document boundary belongs to this tranche, so no
  unrelated repair or aggregate rerun is folded into the checkpoint.
- **2026-07-31 — existing outer nested eta measured.** A bounded executable
  probe constructed the canonical
  `H = Hom_catd(Const(Catd_cat Z),Ebar,Dbar)` family and
  `nested : Functord_cat C H`, then compiled
  `displayedContextLambda(c : C,H,nested[c])`. The checked explicit Core was
  exactly the original `nested` reference. This rules out adding a duplicate
  outer curry or compiler and localizes the missing IR to the explicit inner
  displayed binder.
- **2026-07-31 — `MIXED-NEST-IR-0C` frozen and delegated approval
  recorded.** The exact first implementation is construction-only recursive
  eta/factorization for an already-coherent indexed object of the canonical
  `Hom_catd(Const_catd K (Catd_cat Z),Ebar,Dbar)` family. It introduces fresh
  inner base/fibre tokens, records one typed nested application, evaluates
  its callback once, and factors back to the same coherent subject. It adds
  no Core owner, kernel rule, general curry, external coherence, parser, or
  browser behavior. The user's standing unattended delegation authorizes
  this bounded implementation with human supersession.
- **2026-07-31 — `MIXED-NEST-1A` implemented and focused-green.** The mixed
  profile now records both locally nameless indices and source/target
  polarity for one explicit inner `^fd` eta, invokes its callback once, and
  recursively lowers to the same already-coherent `Functord` subject. Five
  focused tests cover exact output, frozen evidence, indices/polarity,
  noncanonical targets, pointwise/different subjects, and the profile gate.
  The existing mixed-profile and syntax-parity suites pass 9/9 together.
  Root typechecking and lint pass. The single required shared TypeScript gate
  again reaches only the same two unrelated stale README phrase assertions;
  it is not rerun. The bounded implementation checkpoint is
  `1142f723dc41ac336f420429af47d77e21c06fd4`.
- **2026-07-31 — `MIXED-NEST-ACTION-1B` gap measured.** Applying the
  factored nested package over `p : x -> y` and then `c : C[x]` produces the
  correct Core term at `Obj(Fibre_cat H y)`, but the TypeScript surface keeps
  only the generic `object` tag. Consequently the existing `homd_int`
  consumer rejects before Core conversion. A no-coercion probe gave that
  same term the internally derived
  `Functord_cat Z Ebar[y^-] Dbar[y]` classifier; the existing checker accepted
  the definitional conversion and `homd_int` then checked.
- **2026-07-31 — `MIXED-NEST-ACTION-1B` frozen and delegated approval
  recorded.** The implementation is limited to automatic classifier
  refinement for the exact canonical `Fibre_cat(Hom_catd(Const_catd
  K (Catd_cat Z),Ebar,Dbar),y)` result shape. It preserves the Core term and
  derives endpoints internally. It adds no cast, owner, rule, external
  coherence, text, or browser behavior. The user's standing unattended
  delegation authorizes this bounded implementation with human supersession.
- **2026-07-31 — `MIXED-NEST-ACTION-1B` implemented and focused-green.**
  Ordinary object application now recognizes only the exact canonical mixed
  fibre result and derives its `Functord_cat` classifier internally. The Core
  term remains unchanged and the existing checker validates the definitional
  conversion. Both outer base-arrow transport and direct base-object
  evaluation feed the refined result to `homd_int`; the non-`Catd_cat`
  constant-fibre negative remains an object and rejects. The focused suite
  passes 3/3 and all four affected mixed suites pass 16/16. Typechecking and
  lint pass. The required shared TypeScript gate again reaches only the same
  two unrelated stale README phrase assertions and is not rerun. The bounded
  implementation checkpoint is
  `b76baaf75ea332b977d403b6e11c975972466a45`.
- **2026-07-31 — `DISPLAYED-TELESCOPE-GENERIC-1` audit found a finite
  fold, not a missing curry.** The completed two-binding and four-binding
  lowerers already use the arbitrary sibling-product/projection tree, the
  recursive typed body compiler, and a reusable one-layer
  `sigma_functord_sec`/pullback lifting helper. A canonical sequence of
  nonempty sibling layers can repeat that helper to arbitrary finite depth
  with existing internal object/base-arrow/higher action. The active
  Lambdapi check is green and no new owner is indicated.
- **2026-07-31 — `DISPLAYED-TELESCOPE-GENERIC-1` frozen and delegated
  approval recorded.** D-DTTLF-USABILITY-026 selects only the literal
  product/Sigma layer normal form, exact generic dependency-plan validation,
  repeated existing-owner lifting, generic frozen evidence, and the existing
  mixed successor profile. Predecessor profiles remain exact. Arbitrary
  dependency DAGs without explicit weakening, pullback-hidden mixed
  classifiers, general curry, unrestricted `:^nd`, text, browser, Core,
  kernel, checker, and transfer deltas remain outside the slice. The user's
  standing unattended delegation authorizes this bounded implementation
  after the proposal checkpoint, with human supersession.
- **2026-07-31 — `DISPLAYED-TELESCOPE-GENERIC-1` implemented and
  focused-green.** The mixed successor derives arbitrary finite canonical
  sibling layers, validates their exact locally nameless dependency plan,
  and repeatedly lifts existing layer projections through later Sigma
  products. The four-layer/two-sibling-block witness compiles ordinary
  occurrences, pairing, an internal base-arrow cell, nested mixed eta, and
  `homd_int`. The dedicated suite passes 6/6 and the nearest predecessor and
  mixed suites pass 22/22. Typechecking and lint pass. The one required
  aggregate reaches 1,201 passes and only four unrelated committed
  inventory/publication assertions; it is not rerun. The exact
  implementation checkpoint is
  `6fa6f2ebdafe8f4bc8e80136a4aadcd3e9ae43fa`.
- **2026-07-31 — `DISPLAYED-MIXED-GRADUATE-1` audit finds no semantic
  dependency.** Finite sibling projections plus repeated one-layer lifting
  form a structural induction over canonical layer count. The beyond-arity
  mixed witness checks the induction's internal action consumer. Graduation
  therefore needs an exact claim/performance boundary, not another curry,
  kernel owner, checker rule, or presentation special case.
- **2026-07-31 — `DISPLAYED-MIXED-GRADUATE-1` frozen.** The exact
  H-DTTLF-USABILITY-DISPLAYED-MIXED-GRADUATE-01 /
  D-DTTLF-USABILITY-027 proposal graduates arbitrary finite canonical
  positive layers plus the final canonical mixed classifier/action only.
  General curry, arbitrary variance/DAGs, pullback-hidden classifiers,
  unrestricted `:^nd`, metatheory, transfer, text, browser, and performance
  claims remain withheld. The proposal is non-self-authorizing; the user's
  standing unattended delegation may record a separate approval after its
  checkpoint, with human supersession.
- **2026-07-31 — D-DTTLF-USABILITY-027 approved as proposed.** The frozen
  proposal was checkpointed independently at
  `ddc78c250970f62c09d822a39a16502f41c75db1`. With no immediate contrary
  human response, the user's standing unattended delegation records the
  exact plan-level graduation with human supersession. This adds no semantic
  owner, runtime/checker behavior, parser route, browser behavior, or remote
  Git authority. `TEXT-PARITY-MIXED-1` is dependency-ready.
