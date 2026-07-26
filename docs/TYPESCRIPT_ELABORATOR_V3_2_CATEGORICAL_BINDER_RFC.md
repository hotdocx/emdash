# TypeScript emdash v3.2 Categorical Binder And Application RFC

Status: accepted implementation specification for `USABILITY-1A`

Implementation: `USABILITY-1B` ordinary contextual eta/application slice is
complete; `USABILITY-1C` structural bracket abstraction is next

Plan: `TS-ELAB-V3.2-USABILITY`

Executable artifact:
`src/v3_2/categorical_surface_spec.ts`

Authority audited: `emdash2/emdash3_2.lp` on 2026-07-26

## Decision

The TypeScript elaborator has two distinct abstraction mechanisms:

1. **outer dependent-LF abstraction**, represented by `KernelLambda`, checked
   against an LF `KernelPi`, and eliminated by ordinary Core call; and
2. **categorical abstraction**, checked against an ordinary or displayed
   categorical classifier and compiled through a typed contextual/wiring IR
   to explicit active emdash combinators.

`BinderMode.variation` on a `KernelLambda` is metadata for the outer LF
binder. It does not turn that lambda into a categorical functor. Conversely,
a categorical abstraction may use an ergonomic TypeScript callback at its
API boundary, but the callback result is immediately reified into a
first-order locally nameless contextual IR. Stored Core does not contain a
JavaScript closure.

Application is also type-directed rather than owner-named. The elaborator
classifies:

- the subject;
- whether the subject is a concrete term or a classifier family;
- the argument dimension;
- the expected result/action shape;
- ordinary versus displayed dependency; and
- polarity and cell level from the contextual classifiers.

That information selects one explicit backend-neutral Core owner. If it does
not select exactly one authorized owner, elaboration fails with the inferred
classifier, argument dimension, expectation, candidate owners, and source
provenance. It never guesses.

This settles the frontend architecture needed before more library
acquisition. It does not claim that all categorical structural owners have
already been transferred. Those exact prerequisites are enumerated below and
are the implementation input to `USABILITY-1B` and `USABILITY-1C`.

## Architectural Boundary

Let `Δ` be the ordinary dependent-LF context and `Γ` an ordered categorical
input context. The elaborator uses separate judgments:

```text
Δ ⊢LF e ⇒ A ⇝ c

Δ ; Γ ⊢CAT e ⇒ Q ; U ⇝ w
```

The LF judgment synthesizes LF type `A` and explicit Core `c`.

The categorical judgment synthesizes categorical classifier `Q`, free-slot
usage `U`, and contextual/wiring term `w`. `U` is not merely an optimization:
discard, duplication, and permutation of categorical inputs must become
explicit weakening, contraction, and exchange.

The corresponding checking judgments are:

```text
Δ ⊢LF e ⇐ A ⇝ c

Δ ; Γ ⊢CAT e ⇐ Q ⇝ w
```

Checking information may recover implicit endpoints and distinguish a full
action package from its value at one argument. It may not manufacture an
unavailable action.

### Outer LF abstraction

```text
Δ, x : A ⊢LF t ⇐ B ⇝ c
────────────────────────────────────────────── LF-LAM
Δ ⊢LF (λ x : A. t) ⇐ (Π x : A. B) ⇝ KernelLambda(c)
```

Its elimination is:

```text
Δ ⊢LF f ⇒ Π x : A. B ⇝ cf
Δ ⊢LF a ⇐ A ⇝ ca
────────────────────────────────────────────── LF-APP
Δ ⊢LF f a ⇒ B[a/x] ⇝ KernelCall(cf, ca)
```

This is genuine outer dependent type theory and is already implemented.

### Categorical abstraction

For an ordinary functorial input, the target judgment is conceptually:

```text
Δ ; Γ, x :^functorial A ⊢CAT e ⇐ Obj(B) ⇝ w
abstractA,B(x,w) = F
────────────────────────────────────────────── CAT-LAM
Δ ; Γ ⊢CAT (λcat x : A. e) ⇐ Functor(A,B) ⇝ F
```

`abstractA,B` is typed categorical bracket abstraction. Its result is an
actual object of `Functor_cat A B`, not an LF function from `τ (Obj A)`.
The lowering must provide a coherent arrow action by construction from active
functorial combinators. An object-only body cannot be promoted silently.

The source spelling `λcat` above is explanatory notation only. The first
product API is a TypeScript AST/builder API; string parsing and final textual
notation remain separate.

## Orthogonal Binder Information

Binder information is not one large enum and is not derived from the names of
`fapp*`, `tapp*`, or displayed projection owners.

| Axis | Values in the first specification | Source of information |
| --- | --- | --- |
| plicity | explicit, implicit | surface constructor or expected telescope |
| variation capability | functorial, natural, object-only | binder capability |
| polarity | covariant, contravariant | classifier, `Op_cat`, and active opposite convention |
| cell level | object, arrow, transfor, higher | inferred classifier and argument |
| dependency | ordinary, displayed | classifier and categorical context |

These axes have deliberately different meanings:

- Plicity controls argument recovery; it does not determine variation.
- Object-only means that no arrow action is available. It does not mean
  “groupoidal.”
- A variable over a groupoidal classifier can still vary functorially along
  invertible arrows.
- Contravariance is represented through an opposite classifier and the
  active polarity convention, not by inventing a new application primitive.
- Displayed dependency belongs to the classifier/context; it is not another
  spelling for naturality.
- Object/arrow/transfor/higher is usually inferred and does not create one
  binder mode per projection owner.

The active canonical syntax settles `:^n` for natural/indexed variation.
`functorial` and `object-only` are stable internal TypeScript mode names in
this RFC. It does not standardize final Lambdapi spellings such as `:^f` or
`:^o`.

## Type-Directed Application Judgment

Application selection has the abstract form:

```text
Δ ; Γ ⊢CAT h ⇒ S ⇝ wh
Δ ; Γ ⊢CAT a ⇒ T ⇝ wa
select(layer(S), classifier(S), form(S),
       dimension(T), expected, dependency(S,T)) = r
──────────────────────────────────────────────────────── CAT-APP
Δ ; Γ ⊢CAT h · a ⇒ result(r) ⇝ apply(r, wh, wa)
```

The selected `r` is a semantic owner identifier. Backend spelling is a
separate conformance binding.

A whole action is not the same operation as applying an action to one value.
The contextual IR therefore has a typed `hom-boundary`/whole-action request.
This prevents a concrete term from being silently discarded merely because
the expected result is a functor.

For example, the full transfor point evaluator depends on the source/target
functor family but not on one concrete transfor. Its selection subject is a
`classifier-family`. A concrete transfor at a point selects the capped
component instead.

### Exact initial selection matrix

| Subject and form | Argument/request | Expected shape | Semantic target | Active spelling/evidence | Surface status |
| --- | --- | --- | --- | --- | --- |
| outer LF Pi term | LF term | LF value | `outer-lf-call` | Core call | eligible |
| ordinary functor term | object | object value | `functor-object` | `fapp0` | eligible |
| ordinary functor term | hom boundary | whole hom action | `functor-hom-full` | `fapp1_func` | eligible |
| ordinary functor term | arrow | arrow value | `functor-hom-capped` | `fapp1_fapp0` | eligible |
| ordinary transfor family | object | whole point evaluator | `transfor-component-full` | `tapp0_func` | eligible |
| ordinary transfor term | object | point component | `transfor-component-capped` | `tapp0_fapp0` | eligible |
| ordinary transfor term | hom boundary | whole off-diagonal action | `transfor-hom-full` | `tapp1_func` | naturality gate |
| ordinary transfor term | arrow | off-diagonal value | `transfor-hom-capped` | `tapp1_fapp0` | naturality gate |
| dependent section term | base object | dependent object | `section-object-evaluation` | reviewed `piapp0` continuation | eligible |
| dependent section term | hom boundary | whole section action | `section-hom-full` | active `piapp1_func` | transfer required |
| dependent section term | base arrow | dependent arrow | `section-hom-capped` | active `piapp1_fapp0` | transfer required |
| displayed functor term | base object | fibre functor | `displayed-functor-fibre` | active `Fibre_func` | `USABILITY-2A` |
| displayed functor term | base arrow | transport functor | `displayed-functor-transport` | active `functord_transport_func` | `USABILITY-2A` |
| displayed functor term | base arrow | whole laxity transfor | `displayed-functor-laxity` | deliberately deferred `functord_laxity_transf` | unsupported |
| displayed transfor family | base object | whole component evaluator | `displayed-transfor-component-full` | active `tdapp0_func` | `USABILITY-2A` |
| displayed transfor term | base object | component | `displayed-transfor-component-capped` | active `tdapp0_fapp0` | `USABILITY-2A` |

The ordinary off-diagonal targets already exist in the explicit Core catalog,
but the active kernel calls `tapp1_fapp0` a reserved capped ordinary
hom-action surface and says to keep it abstract until the external ordinary
naturality API is promoted. Representability in explicit Core is therefore
not sufficient authorization for convenient surface exposure. Both
off-diagonal rows fail with `RESERVED_NATURALITY_ACTION` for now.

The section object row is different: `DIRECTED-1C` already reviewed and
integrated the exact `piapp0` signature as the backend-neutral
`section-object-evaluation` continuation owner. The runnable dependent demo
uses it. Section arrow action exists in the active kernel but is not yet part
of that reviewed TypeScript continuation.

## The User's Eta Example

For explanatory internal notation:

```text
h = λ x :^functorial A. F[x]
```

typed bracket abstraction recognizes the eta case and produces:

```text
h ⇝ F : Functor(A,B)
```

Application then uses the argument classifier:

```text
y : Obj(A)
h[y] ⇝ functor-object(h,y)
     ⇝ functor-object(F,y)
```

where the Lambdapi conformance backend renders `functor-object` as `fapp0`.

For:

```text
p : Hom(A,x,y)
h[p] ⇝ functor-hom-capped(h,p)
     ⇝ functor-hom-capped(F,p)
```

the backend renders the capped semantic owner as `fapp1_fapp0`.

If the expected result is the complete functor:

```text
Hom_cat(A,x,y) ⊢ Hom_cat(B,F[x],F[y])
```

the typed whole-action request selects `functor-hom-full`, rendered as
`fapp1_func`. It does not pretend that the whole functor is an arrow value.

This is the intended “flow of typing information”: the convenient surface
does not ask the user to choose an owner name, but the elaborated Core always
contains the exact owner.

## Contextual/Wiring IR

The first contextual IR is deliberately small and first order.

### Nodes

- `slot-reference`
- `explicit-core-term`
- `typed-application`
- `typed-pair`
- `typed-composition`

### Required annotations

Every node carries or synthesizes:

- its ordered categorical context;
- its free-slot usage;
- its result classifier;
- its cell level;
- polarity;
- ordinary/displayed dependency; and
- source provenance.

An ergonomic builder may expose:

```ts
categoricalLambda("x", A, x => body(x))
```

but `x` is an opaque slot token and the callback result is immediately
converted to the first-order representation. The callback itself is not Core,
is not serialized, and is not part of equality or hashing.

The initial implementation may use a tree. A DAG/string-diagram
representation is a later sharing and visualization improvement. Graph
sharing must not erase semantic contraction: using the same categorical input
twice still lowers through an explicit diagonal.

## Typed Bracket Abstraction

For one categorical input `x : A`, lowering is driven by free-slot usage and
the inferred result classifier.

### Identity

```text
[x]x = id_func(A)
```

### Weakening

If `x` is unused and `b : Obj(B)`:

```text
[x]b = fapp0(Const_func_func(A,B), b)
```

The semantic compiler will reference backend-neutral structural targets; the
formula above shows the active authority.

### Exchange

Reordering nested ordinary inputs uses `sym_func_func`. Source-variable
renaming or a De Bruijn shift is not categorical exchange.

### Contraction

When the body uses `x` twice:

```text
[x]H[x][x]
```

lowering uses `diag_func_func`. Reusing one IR node without a diagonal would
lose the categorical action and is invalid.

### Application

For a functor-valued `u` and compatible object-valued `v`:

```text
[x](u v)
```

lowers by:

1. bracket-abstracting `u` and `v`;
2. pairing the two results in the product context; and
3. composing with `Eval_func`.

The application owner itself remains selected by the typed application
matrix. `Eval_func` is the internal categorical wiring for a variable body,
not an owner-specific source node.

### Composition

Sequential ordinary functorial wiring lowers through `comp_cat_fapp0`.

### Nested abstraction

Nested ordinary categorical abstraction uses the active product/curry
packages, principally `curry_func_func`; `uncurry_func_func` is the inverse
direction needed by contextual normalization and explicit consumers.

### Multiple inputs

Multiple input contexts use `Product_cat`, `Product_projL_func`,
`Product_projR_func`, `Product_pair`, and `Product_map_func`. The active
kernel's product-valued functor normal form means that pairing is represented
componentwise; the compiler must follow that normal form rather than invent a
new paired-functor owner.

## Exact Structural Transfer Prerequisites

The frozen base `CORE_OWNER_SCHEMAS` catalog does not yet contain the ordinary
bracket-abstraction basis. `USABILITY-1A` therefore records it separately so
the completed MVP profile and its hashes do not drift accidentally.

| Semantic prerequisite | Active authority | First use |
| --- | --- | --- |
| `identity-functor` | `id_func` | variable/identity |
| `constant-functor-abstraction` | `Const_func_func` | weakening |
| `exchange-functor-abstraction` | `sym_func_func` | exchange |
| `diagonal-functor-abstraction` | `diag_func_func` | contraction |
| `product-category` | `Product_cat` | contextual product |
| `product-left-projection` | `Product_projL_func` | context projection |
| `product-right-projection` | `Product_projR_func` | context projection |
| `product-pair` | `Product_pair` | context pairing |
| `product-map` | `Product_map_func` | componentwise maps |
| `evaluation-functor` | `Eval_func` | categorical application |
| `functor-composition` | `comp_cat_fapp0` | composition |
| `curry-package` | `curry_func_func` | nested abstraction |
| `uncurry-package` | `uncurry_func_func` | nested normalization |

All thirteen are active kernel declarations. They are marked
`active-kernel-untransferred` rather than being inserted into the frozen Core
catalog by this RFC. `USABILITY-1C` must transfer the smallest exact subset
needed by each bracket rule, with signatures, linkage, runtime/proof behavior,
and conformance evidence as required by the existing transfer architecture.

This is direct typed transfer. It does not require a generic Lambdapi parser.

## Natural And Displayed Frontier

The displayed side is not one mechanical renaming of ordinary `fapp*`.
Active v3.2 separates at least:

- fibre projection of a displayed functor (`Fibre_func`);
- heterogeneous transport over a base arrow
  (`functord_transport_func`);
- full and capped displayed-transfor components
  (`tdapp0_func`, `tdapp0_fapp0`);
- component-level displayed internal action and laxity cells
  (`fdapp1_int_*`, including `fdapp1_int_cell`);
- section object evaluation (`piapp0`); and
- full/capped section action (`piapp1_func`, `piapp1_fapp0`).

The active source also documents a desired whole displayed laxity transfor,
`functord_laxity_transf`, but deliberately leaves the symbol inactive until
the internalized component can support it computationally. The frontend must
not reconstruct that absent whole action from its name or from
component-level cells.

Accordingly:

- `USABILITY-1B` and `USABILITY-1C` implement ordinary functorial abstraction;
- `USABILITY-1D` stabilizes the ergonomic API and conformance corpus;
- `USABILITY-2A` qualifies one natural/indexed or displayed dependent
  example through the same contextual IR;
- missing displayed structure produces a precise diagnostic rather than an
  ad hoc owner-specific compiler path; and
- groupoidal DTT specialization/closure remains later kernel and transfer
  work, not a substitute for the existing directed/categorical DTT.

## Diagnostics

The executable specification freezes these fail-closed codes and payload
requirements:

| Code | Meaning |
| --- | --- |
| `AMBIGUOUS_ABSTRACTION_LAYER` | expected information does not distinguish outer LF from categorical abstraction |
| `MISSING_EXPECTED_ACTION_SHAPE` | classifier and argument leave more than one full/capped or displayed action |
| `CLASSIFIER_ARGUMENT_MISMATCH` | no owner judgment matches subject, argument, expectation, and dependency |
| `OBJECT_ONLY_ARROW_USE` | an object-only binder is required to act on an arrow or higher cell |
| `POLARITY_MISMATCH` | covariant/contravariant contextual use disagrees |
| `MISSING_STRUCTURAL_OWNER` | bracket lowering reaches an active but untransferred prerequisite |
| `UNAVAILABLE_DEPENDENT_ACTION` | a section action exists but is outside the reviewed TypeScript continuation |
| `UNAVAILABLE_DISPLAYED_ACTION` | displayed action awaits qualification or is absent in the active authority |
| `RESERVED_NATURALITY_ACTION` | explicit Core can represent an action whose external surface remains reserved |

Diagnostics must include source provenance. Owner availability errors also
include semantic owner, implementation status, and the next qualifying
stage. An unsupported action is never encoded as an opaque free constant.

## Relationship To The Older TypeScript Prototype

The root prototype on `main` remains useful generic implementation evidence
for:

- ergonomic HOAS/PHOAS construction;
- binder metadata;
- bidirectional checking;
- holes, metavariables, and unification;
- rewriting and proof-state machinery; and
- explicit action/coherence checks.

It is not v3.2 category-theory authority. In particular, its mode-aware
lambda path built an LF lambda/Pi and checked metadata; it did not implement
the categorical bracket abstraction specified here against the current
structural owners.

The new frontend may port or reimplement the generic builder and
bidirectional techniques. It may not restore the stale category-specific AST,
mutable global rule arrays, named-HOAS storage, retired D0/D1 API, or
fail-soft unsupported terms.

HOAS versus De Bruijn is an implementation boundary rather than the main
architecture decision:

- callback syntax can remain ergonomic;
- callback tokens are immediately reified;
- contextual IR and explicit Core are first order and name independent; and
- provenance retains user-facing names and source locations for diagnostics.

## Implementation Contract

### `USABILITY-1B`

Implement:

- the minimal contextual IR and its invariant checker;
- an ergonomic ordinary categorical lambda constructor;
- the eta abstraction case;
- type-directed object application;
- type-directed capped arrow application;
- whole hom-action selection; and
- negative cases for layer ambiguity, object-only arrow use, classifier
  mismatch, and unavailable action.

This slice may reuse the existing seven integrated ordinary projection owners
and return the underlying functor directly for eta. It need not transfer the
whole structural basis before demonstrating the first categorical lambda.

### `USABILITY-1C`

Transfer and use the exact ordinary structural prerequisites required for:

- unused-variable weakening;
- exchange;
- contraction;
- evaluation after pairing;
- composition; and
- nested abstraction/curry.

Each transfer remains backend-neutral in Core, keeps Lambdapi spelling in its
backend binding, and carries exact signature/rule/proof evidence according to
the qualified transfer pipeline.

### `USABILITY-1D`

Consolidate:

- stable TypeScript surface constructors;
- deterministic explicit-Core serialization;
- source-located diagnostics;
- end-user examples;
- focused TypeScript tests; and
- Lambdapi conformance probes for the emitted explicit Core.

No string parser is required.

### `USABILITY-2A`

Use the same contextual machinery for one representative
natural/indexed/displayed dependent example. Transfer only the active owners
it needs. Stop at the first absent structural capability with the exact
`UNAVAILABLE_DISPLAYED_ACTION` evidence; do not synthesize a missing whole
laxity theorem.

## Executable Evidence

`src/v3_2/categorical_surface_spec.ts` freezes:

- the five axes;
- four abstraction judgments;
- sixteen application-selection rows;
- the contextual IR annotation contract;
- thirteen structural prerequisites;
- nine diagnostic contracts;
- semantic/backend separation; and
- non-effects on notation, parsing, Core owners, the MVP manifest, and the
  browser entry point.

Its selector demonstrates that the ordinary eta consumer can resolve
`functor-object`, `functor-hom-capped`, and `functor-hom-full`, while section
arrow, displayed action, reserved naturality, ambiguous displayed action, and
classifier mismatch fail with their recorded codes.

The separate Lambdapi evidence table relocates every candidate and structural
prerequisite by declaration fragment in `emdash2/emdash3_2.lp`. Validation
also checks the reviewed `DIRECTED-1C` prerequisite, existing Core owner
membership and backend bindings, exact content, unique selection keys, and
the absence of backend spellings from semantic data.

The artifact is root-only and deliberately absent from `src/v3_2/browser.ts`.
It specifies the compiler boundary; it does not yet expose a browser product
API.

## Explicit Non-Effects

This RFC:

- does not reinterpret `KernelLambda`;
- does not add a second DTT theory competing with the directed categorical
  kernel;
- does not claim the groupoidal specialization is complete;
- does not standardize `:^f` or `:^o`;
- does not promote the reserved ordinary off-diagonal naturality surface;
- does not pretend the absent whole displayed laxity transfor is active;
- does not mutate the frozen MVP owner/rule catalog;
- does not parse `.lp` files;
- does not make bulk acquisition a demo prerequisite; and
- does not authorize owner-named frontend shortcuts.

## `USABILITY-1A` Completion Boundary

`USABILITY-1A` is complete when:

1. this RFC and the executable artifact agree;
2. exact active owner evidence is relocated successfully;
3. ordinary object/arrow/full selection and fail-closed unavailable cases are
   tested;
4. the existing Core/MVP/browser boundaries remain unchanged;
5. the TypeScript gate and bounded active-kernel gate pass; and
6. the living usability plan records the validated checkpoint and advances
   the next dependency-ready slice to `USABILITY-1B`.
