# TypeScript emdash v3.2 Categorical Binder And Application RFC

Status: accepted implementation specification for `USABILITY-1A`

Implementation: `USABILITY-1B` ordinary contextual eta/application and
`USABILITY-1C` structural bracket abstraction plus `USABILITY-1D`
API/serialization/diagnostic/example consolidation are complete;
`USABILITY-2A0/2A1` closed displayed application and indexed section eta are
complete; the exact `USABILITY-GRADUATE-1` proposal is separately
reviewed-approved under
H-DTTLF-USABILITY-GRADUATE/D-DTTLF-USABILITY-002
for its exact bounded envelope; the separate
H-DTTLF-USABILITY-DEPENDENT/D-DTTLF-USABILITY-003 decision is
reviewed-approved and the bounded `USABILITY-DEPENDENT-1A` non-eta
section-composition continuation is complete

Plan: `TS-ELAB-V3.2-USABILITY`

Executable artifacts:
`src/v3_2/categorical_surface_spec.ts`,
`src/v3_2/categorical_surface.ts`,
`src/v3_2/categorical_program.ts`, and
`src/v3_2/core_serialization.ts`; the runnable witnesses are
`src/v3_2/categorical_bracket_demo.ts` and
`src/v3_2/categorical_dependent_eta_demo.ts`, plus
`src/v3_2/categorical_dependent_composition_demo.ts`; the minimal
section-composition transfer closure is
`src/v3_2/categorical_dependent_composition_transfer.ts`; the
non-authorizing graduation
artifact is
`src/v3_2/categorical_usability_graduation_proposal.ts`; its separate
approval record is
`src/v3_2/categorical_usability_graduation_review.ts`; the dependent
continuation's immutable proposal and separate exact approval are
`src/v3_2/categorical_dependent_usability_proposal.ts` and
`src/v3_2/categorical_dependent_usability_review.ts`

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

This defines the frontend architecture to qualify before more library
acquisition. The completed ordinary and indexed-eta witnesses were enough for
USABILITY-GRADUATE-1 to recommend that architecture only within its exact
first-order envelope. D-DTTLF-USABILITY-002 now approves that qualified
recommendation through a separate immutable review; the historical proposal
remains non-self-authorizing. The decision does not claim that all
categorical structural owners have been transferred. Those exact
prerequisites and boundaries are enumerated below.

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
catalog by this USABILITY-1A snapshot. USABILITY-1C subsequently transferred
all thirteen as direct typed root-only candidate declarations, plus the
supporting `Functor_cat` signature and exact intrinsic transparent `Functor`
equation. The implementation is in
`src/v3_2/categorical_structural_transfer.ts`; it does not insert those
owners into the frozen intrinsic catalog. The separate transfer artifact,
rather than this historical status field, is the current implementation
ledger.

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
- `USABILITY-1D` stabilizes the ergonomic API, explicit-Core inspection,
  diagnostics, demo, and conformance corpus;
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

Completed: transferred and used the exact ordinary structural prerequisites
required for:

- unused-variable weakening;
- exchange;
- contraction;
- evaluation after pairing;
- composition; and
- nested abstraction/curry.

Each transfer remains backend-neutral in Core, keeps Lambdapi spelling in its
backend binding, and carries exact signature/rule/proof evidence according to
the qualified transfer pipeline. The one required conversion,
`Functor_cat X (Product_cat A B)` to the product of functor categories, is an
exact active rule compiled by the generic runtime engine. Identity,
weakening, composition, explicit diagonal, evaluation after `Product_pair`,
exchange, and product-context curry all pass the generic LF checker and the
bounded positive/negative Lambdapi corpus. No owner-specific checker or
evaluator case was added.

### `USABILITY-1D`

Completed:

- `CoreCategoricalProgram` provides program-local category handles,
  category/object/functor/Hom assumptions, derived functor/product
  categories, whole-Hom boundaries, uniform type-directed application,
  functorial categorical lambda, contextual inspection, and checked
  compilation;
- `EMDASH-CORE-SEXP-1` deterministically serializes backend-neutral explicit
  Core while omitting provenance and binder hints, retaining owner/free
  identity, plicity, variation, locally nameless indices, and meta sharing;
- presentation-only free-reference labels replace compiler-private
  structural names with stable `emdash.categorical.*` identities without
  selecting a backend;
- existing surface/declaration/checker/program exceptions normalize to
  immutable phase/code/message/detail/span/location diagnostics;
- the fixed identity and pointwise fixtures, alpha/provenance invariance,
  object/capped-arrow/whole-Hom actions, source diagnostics, and browser
  exclusion are tested;
- `demo:categorical-bracket` checks pointwise application, diagonal, and
  exchange, prints canonical Core plus inferred classifiers and structural
  evidence, and rejects one wrong-category input at its supplied source; and
- the bounded USABILITY-1C Lambdapi corpus remains the exact conformance
  oracle for all emitted structural prerequisites and the relevant negative.

No string parser, production Lambdapi process, owner-specific semantic path,
browser export, or profile expansion was added.

### `USABILITY-2A`

Implement in two dependency-ordered slices:

1. `USABILITY-2A0` transfers exact active `Fibre_func` and
   `functord_transport_func` signatures and reuses reviewed `piapp0` for
   closed-index section, fibre-functor, and base-arrow transport application.
   The deliberately inactive whole displayed laxity transfor must fail with
   `UNAVAILABLE_DISPLAYED_ACTION`.
2. `USABILITY-2A1` adds a first-order indexed contextual classifier and one
   genuine natural/displayed Pi/Sigma eta or binder witness through the same
   callback-once IR. An open classifier such as `E[k]` must refer to the
   contextual slot explicitly; it may not smuggle an unscoped Core bound
   variable into a closed `CoreType`.

Closed application in 2A0 is prerequisite evidence, not completion of the
dependent-binder architecture. Transfer only active owners the witness needs.
Stop at the first active-but-untransferred action with
`UNAVAILABLE_DEPENDENT_ACTION`, or at a mathematically absent capability with
`UNAVAILABLE_DISPLAYED_ACTION`; do not conflate those states or synthesize a
missing theorem.

#### `USABILITY-2A0` implementation result

The closed-index slice is complete. The generic LF transfer path now compiles
the exact active `Fibre_func` and `functord_transport_func` signatures over
the existing ordinary structural environment. Both are root-only opaque
candidate declarations: their Lambdapi transparent bodies remain authority,
and no runtime/proof rule or owner-specific checker/evaluator case was added.

`CoreCategoricalProgram` now admits program-local displayed-family handles,
fibre categories, dependent-section assumptions, and displayed-functor
assumptions. Its uniform application method checks and emits:

- reviewed `section-object-evaluation` for `s[k]`;
- transferred `displayed-functor-fibre` for `FF[k]`; and
- transferred `displayed-functor-transport` for `FF[p]`.

The resulting `FF[k]` is an ordinary functor between exact fibres and reuses
ordinary application without a displayed shortcut. The first-order
inspection IR retains the selected dependent prerequisite under nested
ordinary application, and deterministic Core serialization uses semantic
presentation labels rather than backend spellings.

The USABILITY-1A specification is intentionally still a frozen snapshot of
the pre-transfer availability state. Selection accepts a narrow
post-transfer qualification overlay only for an
`active-kernel-untransferred` row named by the transferred target. The
overlay cannot promote the `not-active` whole-laxity row or a reserved
naturality row. Source-located negatives cover that absent laxity, mismatched
and foreign displayed families, and open callback-slot application.

In particular, the open negative demonstrates the remaining architectural
work accurately: `FF[k]` for a contextual slot needs a classifier whose fibre
mentions that slot. The current closed `CoreType` cannot represent this
honestly, and the implementation refuses to insert an unscoped Core bound
index. `USABILITY-2A1` must extend the first-order contextual classifier and
then qualify a genuine natural/displayed eta or binder witness. Therefore
2A0 is not an architecture-graduation result.

The focused 30-test TypeScript corpus (29 pass, one opt-in skip), eight-case
live Lambdapi corpus, 634-test full TypeScript gate, and bounded complete
active-kernel check pass.

#### `USABILITY-2A1` implementation result

The indexed binder slice is complete for one exact section-eta rule. The
contextual frontend classifier is now a disjoint union of closed `CoreType`
and a first-order indexed object:

```text
IndexedObject {
  baseCategory: K,
  family: E,
  index: locally-nameless contextual slot
}
```

The internal builder tracks an opaque slot ordinal and normalizes it to the
public locally nameless index only in retained contextual evidence. The
classifier is not a Core term: it cannot cross the closed checker boundary,
cannot become an unscoped `KernelBound`, and is rejected explicitly by
closed fibre/Hom APIs.

Open application of a closed dependent section to one direct contextual base
slot produces this classifier. `dependentLambda` then selects the frozen
`natural-indexed-abstraction` row, runs its callback once, checks natural
variation/displayed dependency and exact base/family/usage, and qualifies
only:

```text
λ k :^n K. s[k]
```

The result eta-lowers to explicit Core `s` with type `Obj(Pi_cat E)`. A
frozen `categorical.dependent-eta` evidence record retains the original
`section-object-evaluation` body, indexed classifier, slot index, provenance,
and dependent prerequisite. Compilation merges that evidence with
prerequisites visible in the surviving result IR, so eta reduction does not
make the selected owner unauditable.

`demo:categorical-dependent` presents the typed input, contextual classifier,
explicit Core, inferred/expected type, and prerequisite without a parser or
production Lambdapi process. Its first next-action negative is `s[p]`:
`piapp1_fapp0` is active in Lambdapi but remains untransferred, so the facade
reports `UNAVAILABLE_DEPENDENT_ACTION` at the supplied source. The
deliberately inactive whole displayed laxity from 2A0 remains a distinct
`UNAVAILABLE_DISPLAYED_ACTION` authority gap.

Wrong-family, non-natural mode, and escaped-index tests fail closed. Binder
renaming and provenance changes leave explicit Core and its type invariant.
The focused 19-case corpus has 17 passes and two opt-in skips; the eight-case
live 2A1 corpus passes, including an active Pi/component signature and a
wrong-family result negative; the 645-test root gate and bounded active-kernel
check pass.

This result validates the surface-callback → locally nameless contextual IR →
classifier-directed lowering → explicit Core → generic LF checker shape for
both ordinary bracket abstraction and one genuine indexed displayed-Pi
witness. It does not implement general dependent bracket abstraction,
displayed weakening/contraction/reindexing/coherence, section-arrow action,
groupoidal closure, bulk library acquisition, or final notation/parsing.
Those boundaries are retained in the separate graduation review.

### `USABILITY-GRADUATE-1`

Proposal preparation and separate review are complete. The deeply frozen
historical proposal recommends, and the reviewed approval settles, the
architecture only for this exact envelope:

```text
outer dependent LF
  + ordinary first-order structural bracket abstraction
  + direct-slot natural/displayed section eta
```

It snapshots the callback-once surface, opaque slot identities,
closed/indexed classifier split, five-node locally nameless contextual IR,
classifier/argument/expected-shape selection, bracket-or-eta lowering,
backend-neutral explicit Core, generic LF checking/evaluation, and bounded
Lambdapi conformance.

The proposal accounts for all sixteen application judgments:

- nine are eligible or exactly post-transfer qualified;
- the two ordinary transfor Hom actions remain behind their naturality gate;
- four section/displayed-transfor actions have active Lambdapi owners but
  remain untransferred; and
- the whole displayed-functor laxity action is deliberately inactive.

The four untransferred rows name `piapp1_func`, `piapp1_fapp0`,
`tdapp0_func`, and `tdapp0_fapp0`. The inactive row names
`functord_laxity_transf`. A complete general displayed bracket basis is
recorded separately as an owner-coverage question, not falsely grouped with
those transfers.

Within the qualified envelope, another ordinary term or direct-slot section
eta is data/contextual-wiring work and requires no checker/evaluator
algorithm change. General non-eta dependent bracket abstraction, composite
open reindexing, displayed weakening/exchange/contraction, contravariant,
object-only, and higher displayed abstraction remain algorithmic gaps. Bulk
library coverage, acquisition automation, notation/string parsing,
groupoidal closure, and browser/product promotion remain separate work.

The proposal remains root-only with `authorityAuthorized: false`; evidence
does not approve itself. The separate
`categorical_usability_graduation_review.ts` snapshots it exactly and records
the user's exact
H-DTTLF-USABILITY-GRADUATE/D-DTTLF-USABILITY-002 approval. That review makes
the feasibility boundary explicit:

- general outer-LF dependent binding is implemented;
- ordinary first-order categorical binding is implemented and qualified;
- displayed/dependent categorical binding is implemented and qualified only
  for direct-slot indexed-section eta; and
- general displayed/dependent bracket abstraction is not implemented or yet
  mechanically confirmed.

If general displayed/dependent binder usability is a product requirement, it
therefore requires a separately selected consumer-led tranche. The approval
does not change the frozen MVP or directed profiles, production trust,
Lambdapi source, any owner/rule, acquisition strategy, or browser surface,
and it does not resume bulk transfer. The exact green proposal checkpoint is
`f77af05a8f58cbef74d2008fb445a4e7af707f07`; the review implementation
checkpoint is `735ad90fbc99024b0e01ef3f76666fd715652c5b`. The exact green
USABILITY-DEPENDENT-1A implementation checkpoint is
`62ef5b37ac9fcd26cec144ee2efeb4e5009be41b`.

### General binder continuation

The reviewed envelope is a milestone, not a decision about the required code
shape of ordinary and dependent frontend algorithms. The controlling
H-01/D-007 decision remains semantically dependent-first:

```text
Γ                  category
A over Γ           Catd Γ
t : A              section / Obj(Pi_cat A)
σ : Δ → Γ          functor
A[σ]               Pullback_catd A σ
ordinary B         Const_catd Γ B plus its classified bridge
```

The completed starting continuation reuses contextual representation, locally
nameless scoping, dependency/substitution analysis, application
classification, and diagnostics where that is sound. Its lowering remains
authority-aware: constant-family terms may use the existing ordinary bracket
basis through the recorded bridge, while genuinely varying families use
active displayed and section owners. Neither identical functions nor an
identical stored IR is an acceptance requirement, and deliberate separation
is not required either; shared or distinct lowering is chosen from concrete
dependency and owner evidence. Proof-time comparisons must not be
misrepresented as runtime collapse.

The actual acceptance criterion is a usable, deterministic frontend for both
ordinary and displayed/dependent binding that preserves dependency and
substitution, emits authority-backed Core, agrees with bounded conformance
evidence, and fails closed on unsupported structure. Uniform implementation
is only a possible means to that end.

The first completed non-eta witness is:

```text
λ k :^n K. FF[k](s[k])
```

for `FF : Functord E D` and `s : Obj(Pi_cat E)`. The implementation
represents `FF[k]` and `s[k]` by first-order locally nameless indexed
classifiers, recognizes their typed semantic composition, and emits generic
`comp_fapp0` in `Catd_cat K` without an owner-named AST or evaluator
shortcut. The active kernel already owned the mathematics; the TypeScript
program acquired only `Terminal_cat`, `comp_fapp0`, and the two existing
Hom/section classifier reductions through generic transfer engines. The
reductions live at the stable Core `Hom`/`Obj` heads; generic congruence, not
a witness-specific decoded rewrite, transports them into checked types.

Both the TypeScript checker and a bounded live Lambdapi test establish type
`Obj(Pi_cat D)` and pointwise computation
`Fibre_func(FF,k)[piapp0(s,k)]`. The old eta-only program remains the default;
the completed continuation is an explicit opt-in reviewed profile and its
application judgment remains outside the frozen historical sixteen-row
partition.

This USABILITY-DEPENDENT-1A slice needs no new Lambdapi mathematical
owner/rule and does not require complete displayed structural logic. It
demonstrates one natural factoring—shared scoping/classification/IR plus an
authority-specific semantic lowering law—but does not prescribe that
factoring for later consumers. The alternatives retained for future evidence
are a progressively shared compiler, one frontend with distinct
authority-specific lowerers, and a later data-driven contextual-law table.
Dependent weakening, exchange, contraction, curry, composite reindexing, and
general dependent bracket abstraction stay consumer-led and human-gated.

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

Its base selector demonstrates that the ordinary eta consumer can resolve
`functor-object`, `functor-hom-capped`, and `functor-hom-full`, while section
arrow, displayed action, reserved naturality, ambiguous displayed action, and
classifier mismatch fail with their recorded codes. The USABILITY-2A0
target-exact qualification overlay additionally resolves only the two
transferred displayed-functor rows; the deliberately inactive whole-laxity
row remains unavailable even if named in an attempted overlay.

The separate Lambdapi evidence table relocates every candidate and structural
prerequisite by declaration fragment in `emdash2/emdash3_2.lp`. Validation
also checks the reviewed `DIRECTED-1C` prerequisite, existing Core owner
membership and backend bindings, exact content, unique selection keys, and
the absence of backend spellings from semantic data.

The specification, contextual builder, program facade, serializer, and demos
are root-only and deliberately absent from `src/v3_2/browser.ts`. They
implement and qualify the reviewed compiler boundary; they do not expose a
browser product API or establish anything beyond the exact
USABILITY-GRADUATE verdict.

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
