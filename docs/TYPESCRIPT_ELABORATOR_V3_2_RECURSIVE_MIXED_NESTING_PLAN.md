# TypeScript Elaborator v3.2 Recursive Mixed Nesting Plan

Date: 2026-07-31

Status: approved living successor; the architecture and first bounded
implementation gate are frozen below under
H-DTTLF-USABILITY-RECURSIVE-MIXED-NESTING-01 /
D-DTTLF-USABILITY-029. The proposal-only checkpoint is `6828225`. The user
approved the consolidated direction, asked that implementation continue, and
has granted a standing unattended approval delegation with human
supersession. The separate review recorded below approves exactly D-029 and
its non-effects; implementation is dependency-ready.

This is the dedicated successor to the completed bounded work in
[`TYPESCRIPT_ELABORATOR_V3_2_MIXED_MODE_DISPLAYED_TELESCOPE_PLAN.md`](./TYPESCRIPT_ELABORATOR_V3_2_MIXED_MODE_DISPLAYED_TELESCOPE_PLAN.md).
It does not rewrite that plan's completion history. That predecessor
graduated arbitrary finite *positive contextual layers* plus one exact final
mixed classifier and text route. This plan addresses the narrower but deeper
remaining question: recursively recovering and consuming mixed
`Hom_catd`/`Functord_cat`/`Transfd_cat` classifier structure at arbitrary
finite qualified nesting depth.

The user's consolidated decision response is archived as
`infinity-codex:019fb460-a0c8-7373-926f-f754198d6e51:019fb9e1-34f8-7c01-b493-3863c84fd7a4`.
That archive is recovery evidence only. Active code, the active Lambdapi
v3.2 kernel, this living plan, the handoff, and repository SOP remain the
authority order.

## Objective

Make the mixed displayed classifier ladder mechanically reusable rather than
recognizing one hard-coded final shape:

```text
infer explicit Core/LF type
  -> bounded beta/delta/runtime weak-head normalization
  -> recursive reification of the canonical category former
  -> ordinary generic LF checking of the unchanged term
```

The result must support representative arbitrary finite iterated-hom
nesting, beginning with the already-active
`Nested_transfd_telescope_catd`, while preserving all of these boundaries:

- internalized object, base-arrow, transfor, and next-hom action is owned by
  the active emdash kernel;
- no pointwise function is accepted together with external naturality,
  functoriality, variance, or coherence equations;
- runtime definitional computation and proof-time unification remain
  distinct;
- unknown, noncanonical, or insufficiently internalized classifiers fail
  closed;
- type formation and elimination of already coherent nested terms are not
  confused with the still-missing general mixed curry/introduction
  construction; and
- a readable product facade is audited independently and cannot block the
  recursive nesting critical path.

## Consolidated Assessment

### Classifier refinement is sound but presently one-off

The current mixed profile can infer a term such as:

```text
inner : Obj(Fibre_cat H y)

H = Hom_catd
      (Const_catd K (Catd_cat Z))
      Ebar
      Dbar.
```

The active runtime computes:

```text
Fibre_cat H y
  -> Hom_cat (Catd_cat Z) Ebar[y^-] Dbar[y]
  -> Functord_cat Z Ebar[y^-] Dbar[y].
```

The current TypeScript construction layer recognizes exactly the original
canonical syntax and records the richer surface view:

```text
inner : displayed-functor Ebar[y^-] Dbar[y].
```

This is hard-coded *view recovery*, not hard-coded semantic conversion:

- `mixedNestedDisplayedFunctorShape` recognizes the exact family syntax;
- `mixedNestedFibreDisplayedFunctorType` reconstructs the rich metadata;
- the Core term is unchanged and no cast/coercion node is inserted; and
- `CoreCategoricalProgram.compile` finally asks the generic LF checker to
  validate the unchanged term against that rich expected type using the
  transferred runtime program.

Consequently the current route cannot make an ill-typed term pass. It is
nevertheless intentionally incomplete and does not scale by itself: an
equivalent presentation, the next `Transfd_cat` layer, or a classifier hidden
behind a supported transparent definition is not generically reified.

### Runtime conversion, not unrestricted proof-rule search

The exact current conversion is supplied by transferred runtime rules. The
mixed transfer contributes four runtime rules and zero proof rules. The
ordinary TypeScript LF checker intentionally performs definitional
conversion and does not blindly execute Lambdapi `unif_rule`s during
inference.

That is the right default. Proof-time rules are bidirectional; some are
non-transitive stable-facade comparisons; and they do not in general select a
canonical normal form. Allowing the whole proof-rule inventory to drive
classifier inference would turn reification into an ambiguous search and
could erase meaningful presentation/variance distinctions.

The scalable correction is therefore bounded runtime normalization followed
by canonical reification. A proof-time view may be added only after an
owner-position audit identifies one exact comparison that cannot be selected
by runtime computation. Such a view remains explicit, reviewed, and separate
from normal inference.

### Current capability boundary

| Capability | Current status before this plan |
| --- | --- |
| Arbitrary finite ordinary `^f` nesting | Implemented recursively through ordinary product/curry |
| Mixed `Hom_catd`/`Functor_catd`/`Transf_catd` formation | Implemented for transferred owners |
| Arbitrary finite positive displayed contexts | Implemented for canonical sibling/Sigma layers |
| Deeper nested transformation-family formation | Present in the kernel and directly constructible |
| Rich classifier recovery at every nested level | Not implemented; one exact `Catd_cat Z` shape is recognized |
| General mixed displayed lambda bodies | Not implemented |
| Exact eta of an already coherent nested term | Implemented |
| Pullback-hidden/equivalent classifier presentations | Not recognized automatically |
| General mixed curry/introduction | Not implemented |

The frontend therefore accepts a bounded algebra of internally coherent
nested expressions, while the kernel already supports more type formation
and elimination than that frontend exposes.

## The Representative Existing-Authority Ladder

The active kernel already defines:

```text
Nested_telescope_catd
  = Hom_catd
      (Const_catd K (Catd_cat Z))
      Ebar
      Dbar
```

and one level higher:

```text
Nested_transfd_telescope_catd
  = Hom_catd
      (Const_catd K (Functord_cat Z E D))
      FFbar
      GGbar.
```

The second family's fibre computes through existing owners to:

```text
Hom_cat
  (Functord_cat Z E D)
  FFbar[k^-]
  GGbar[k]

-> Transfd_cat Z E D FFbar[k^-] GGbar[k].
```

It is therefore the next high-yield stress test. It exercises one genuine
enrichment/nesting step beyond the existing `displayed-functor` view while
requiring no new mathematical owner, no general curry, and no external
coherence evidence.

The first implementation must demonstrate more than a tag change:

1. direct outer object/fibre projection;
2. outer base-arrow action through an existing internal owner;
3. rich `displayed-transfor` recovery with internally derived endpoint
   families and functors;
4. component/`tdapp*` consumption through the existing generic application
   ladder; and
5. one next-hom consumer or one further iterated `Hom_cat` whose type remains
   internally checked.

## Nesting And Curry Are Related But Distinct

Forming nested types does not require curry. One can recursively form:

```text
H1[k]
  = Hom_(Catd_cat Z)(E-[k],D+[k])
  = Functord_cat(E-[k],D+[k])

H2[k]
  = Hom_(Functord_cat(E,D))(FF-[k],GG+[k])
  = Transfd_cat(FF-[k],GG+[k])

H3[k]
  = Hom_(Transfd_cat(...))(alpha-[k],beta+[k])

...
```

Elimination/application of an already coherent nested term can likewise use
the existing `fapp*`, `tapp*`, `fdapp*`, and `tdapp*` packages.

Introduction is different. Constructing:

```text
lambda f. lambda p. f p
```

is semantically curried evaluation. Ordinary category theory has
`Eval_func`, `curry_func_func`, and `uncurry_func_func`. The general directed
displayed analogue still needs a qualified two-sided mixed curry owner and
its laws. This plan must not fake that missing owner with a TypeScript
whole-body recognizer.

The notation `f p` must also retain its classifier-directed meaning:

- if `f` is an object of `Functor_cat(P,Q)`, it can be evaluated at an object
  or arrow of `P` through the functor action;
- if `f` is merely an arrow in `Hom_cat(P,Q)`, an application to `p` is not
  generally meaningful.

## `Functord_cat`, `Pi_cat`, And Directed Variance

One useful relation is already active at proof time:

```text
Pi_cat F
  ~=proof
Functord_cat (Terminal_catd K) F.
```

Thus `Pi_cat(Functor_catd A B)` is proof-time comparable with a
terminal-source `Functord_cat`. It is not generally the same construction as
`Functord_cat E D`.

The variance obstruction is essential:

```text
Functor_catd A B
```

requires `A : Catd(Op K)` and `B : Catd K`, whereas:

```text
Functord_cat E D
```

requires both `E,D : Catd K`. Therefore the tempting formula:

```text
Functord_cat(Product_catd E D) P
  -> Functord_cat E (Functor_catd D P)
```

is not well-typed in general. If `D` is covariant, the right side is invalid;
if `D` is contravariant, the same-base displayed product on the left is
invalid.

The plausible directed mixed curry instead uses the already studied
two-sided Sigma/pullback total context. Schematically, for:

```text
C : Catd K
A : Catd(Op K)
B : Catd K,
```

one seeks an explicit functor of the shape:

```text
Pi_cat(Pullback_catd B r)
  -> Functord_cat C (Functor_catd A B).
```

It is an explicit mathematical map, not a global category equality. It is a
later Lambdapi-first task after recursive type formation and elimination are
graduated.

## Fibrewise Product Facade Audit

For `B,C : Catd K`, the active kernel represents their fibrewise product by
the transparent semantic composite:

```text
P(B,C)
  = uncurry(Product_cat_func) o Struct_sigma(B,C).
```

It then declares stable structural owners such as
`Product_projL_funcd`, `Product_projR_funcd`, and `Product_pair_funcd` whose
types repeat that composite. The earlier FIBRED-PRODUCT audit correctly
established that a new *injective primitive* `Product_catd` was not needed
for the first product/transport consumer: the transparent family plus two
narrow existing-owner computation rules had zero warning delta, while the
new stable head duplicated semantics and introduced additional overlaps.

That result does not completely settle the facade question raised by the
user. There are three distinct choices:

1. continue spelling the transparent composite at every owner boundary;
2. add a transparent defined/alias symbol `Product_catd` and use that as the
   sole public source spelling, retaining delta-unfolding to the existing
   semantic composite; or
3. add a stable/injective primitive head with its own computation package.

Choice 3 remains unjustified without a new measured semantic need. Choice 2
may improve uniformity, diagnostics, transfer records, and maintainability
without changing mathematics. In particular, it would avoid making every
projection/pairing declaration repeat a long implementation expression.
But a second unused synonym would make the facade worse, and even a
transparent alias can affect definition unfolding, rule presentation,
source digests, warning/performance measurements, and which spelling the
transfer layer treats as canonical.

`PRODUCT-FACADE-0A` must therefore be a separate read-only audit. It will
compare the present repeated composite, a transparent alias adopted
consistently in structural owner types, and a stable head. It must test fibre
and base-arrow computations, projection/pairing/higher action, delta
behavior, warning/performance deltas, and TypeScript transfer ergonomics.
The likely default is the transparent alias if and only if it is a genuine
single facade and not an extra competing representation. This audit is not
on the nesting critical path and authorizes no kernel edit.

### Why primitive projections do not force a primitive type former

`Product_projL_funcd` being primitive while its source family is definable
is not by itself semantically inconsistent. The structural owner packages an
elimination/action boundary that was not obtainable from the transparent
composite at the required higher-action seam. A definable object can have a
named primitive eliminator when computation and coherence require a stable
owner.

The maintainability concern is still legitimate: public owner types should
not expose avoidable implementation noise. That is precisely what the
transparent-facade audit will decide.

## Curry And Uncurry Representation Audit

Both ordinary `curry_func_func` and `uncurry_func_func` are transparent
defined semantic packages in the active kernel. There is no general
category-theoretic requirement that exactly one be primitive and the other
defined. Given chosen products and evaluation, both directions can be
constructed explicitly, and keeping both transparent can expose their
object computations without adding opaque heads.

The real open boundary is not primitive symmetry. The source explicitly
records that full product/curry adjunction coherence remains future work,
and the transfor action of semantic uncurry still depends on a deferred
higher arrow-action seam of `Product_cat_func`.

Accordingly a later `CURRY-PACKAGE-0A` audit should ask:

- do both packages expose the required object, hom, transfor, and next-hom
  action internally;
- are beta, eta, naturality, and adjunction/equivalence laws represented at
  the correct level;
- does transparent unfolding remain computationally manageable; and
- is a stable primitive justified by a measured failure of the transparent
  package rather than by a stylistic expectation of asymmetry?

That audit may coordinate with future mixed curry, but it must not delay the
existing-authority nesting slice.

## Terminal Products Remain Explicitly Unital

This plan does not add a global rewrite or proof rule identifying
`Product_cat Terminal_cat B` with `B`. Such a collapse changes object normal
forms from `(star,b)` to `b` and interacts with objects, homs, pairing,
projections, functor categories, transformations, injectivity, and internal
action. A broad `unif_rule` would also have a rigid product head against an
arbitrary right side, would not make projections compute on unpaired
objects, and could introduce ambiguous/non-transitive proof behavior.

The natural interface is explicit unitors:

```text
1 x B -> B      = Product_projR_func
B -> 1 x B      = pair(Terminal_func,id)

P(1_K,D) -> D   = Product_projR_funcd
D -> P(1_K,D)   = Product_pair_funcd(Terminal_funcd(D),id_funcd(D)).
```

Remaining inverse/eta laws should be transformations or isomorphisms. A
terminal specialization of future curry can be derived through these
unitors rather than duplicating a curry primitive or erasing `1 x X`.

## Transformation Action Should Follow Generic Hom Action

A future mixed curry should preferably be one functor:

```text
MixedCurry : Functor(UncurriedCategory,CurriedCategory).
```

Its generic hom action then maps transformations and higher cells.
`Transf_catd`/`Transfd_cat` should appear through existing next-hom/fibre
projections such as:

```text
Hom_catd(Functor_catd A B,FF,GG)
  -> Transf_catd A B FF GG.
```

A transformation-specific curry owner is justified only if a measured
projection seam cannot expose the generic functor action. Duplicating
naturality or functoriality in separate pointwise primitives is outside the
architecture.

## Implementation Architecture

### One runtime-backed reifier seam

The mixed `CoreCategoricalProgram` already compiles its declaration
environment and composed runtime before constructing its scoped surface
builder. The bounded implementation therefore passes one immutable
reification capability into that builder. It contains:

- the exact compiled declaration environment;
- the exact composed reviewed runtime;
- an explicit weak-head step limit; and
- no proof-rule search API.

The builder uses `coreLfCombinedWeakHead`, which already interleaves bounded
beta, transparent delta, and reviewed runtime reduction. Direct standalone
builders without this capability retain their existing behavior.

### Recursive canonical views

After weak-head normalization, the reifier recognizes only exact active
category former heads:

- `Catd_cat K` / `Functord_cat K E D` as the existing rich displayed views;
- `Transfd_cat K E D FF GG` as `displayed-transfor`;
- ordinary `Functor_cat`, `Hom_cat`, and `Transf_cat` through the existing
  generic Core type views; and
- any later approved former through an explicit registry-like clause rather
  than a whole-program special case.

Each richer view stores the normalized active owner arguments. It never
changes the term. The final generic checker remains the soundness boundary
and must validate the rich expected type by the same runtime conversion.

Unknown heads remain plain category objects. A weak-head budget exhaustion
or stuck reduction fails closed with a source-located diagnostic when rich
classification is required; it must not fall back to proof search or an
external oracle.

### Structural induction claim

Arbitrary finite qualified nesting is earned from the recursive algorithm,
not from a large fixed-depth example. The proof argument is:

1. the base category formers already have rich reifiers;
2. `Hom_catd` fibre computation exposes an ordinary `Hom_cat` at the current
   fibre;
3. the active hom-fold rules select `Functord_cat`, `Transfd_cat`, or the
   next generic hom category when their hypotheses hold;
4. the reifier recursively classifies that canonical result; and
5. generic application/hom action consumes the result without new
   pointwise evidence.

Tests must include at least the existing displayed-functor level, the
`Nested_transfd_telescope_catd` level, one further hom level, and a negative
unknown head. This graduates only the exact constructor grammar whose heads
and reductions were transferred. It does not claim arbitrary semantic
equivalence, arbitrary variance DAGs, or general introduction.

## Work Ledger

| Row | Status | Dependencies | Exact scope |
| --- | --- | --- | --- |
| `RECURSIVE-MIXED-REFLECT-0A` | architecture frozen in this plan | completed mixed-mode profile and D-028 text parity | Replace the one-off conceptual shape rule with the bounded runtime-normalize-and-reify design; inventory exact existing heads/rules and freeze negatives. No behavior change. |
| `RECURSIVE-MIXED-REFLECT-1A` | approved under D-DTTLF-USABILITY-029; implementation dependency-ready | approved `REFLECT-0A` | Pass the existing environment/composed runtime into the mixed scoped builder; weak-head normalize category-object targets; reify exact canonical `Functord_cat` and `Transfd_cat` views recursively; retain generic views and final checking. No kernel/transfer/proof-rule delta. |
| `RECURSIVE-MIXED-TRANSFD-1B` | approved as the first consumer in the same bounded tranche | `REFLECT-1A`; active `Nested_transfd_telescope_catd` owners | Add direct TypeScript evidence for object projection, internal outer arrow action, rich displayed-transfor endpoints, component/`tdapp*`, and one next-hom/further-hom consumer. |
| `RECURSIVE-MIXED-GRADUATE-1C` | pending evidence | green `TRANSFD-1B` plus a further iterated hom | Record the structural-induction boundary for arbitrary finite nesting over the exact transferred grammar; retain fail-closed nonclaims. |
| `TEXT-PARITY-RECURSIVE-MIXED-1D` | deferred until semantic graduation | `GRADUATE-1C` | Mechanically route only the newly graduated semantic constructors through the existing text adapter. No parser-led semantics. |
| `PRODUCT-FACADE-0A` | deferred independent read-only audit | a concrete maintainability priority after nesting | Compare repeated composite, consistently adopted transparent alias, and stable primitive. No active kernel edit without a new gate. |
| `CURRY-PACKAGE-0A` | deferred independent audit | measured higher-action or mixed-introduction consumer | Audit ordinary curry/uncurry computation and adjunction coherence; do not infer primitive asymmetry from style. |
| `MIXED-CURRY-1` | deferred mathematical/kernel work | recursive nesting graduation and two-sided context design | Lambdapi-first explicit mixed curry functor with object/base-arrow/higher action and laws. Separate owner-position proposal required. |

## Frozen First Gate

### H-DTTLF-USABILITY-RECURSIVE-MIXED-NESTING-01 /
### D-DTTLF-USABILITY-029

Approve the following bounded TypeScript-only implementation:

1. Add one optional, immutable runtime classifier-reification capability to
   `CoreCategoricalScopedBuilderOptions`, supplied only by the existing mixed
   program profile from its already compiled declaration environment and
   composed runtime.
2. Replace the one-off final `Catd_cat Z` result refinement with bounded
   `coreLfCombinedWeakHead` normalization followed by canonical reification.
3. Preserve the existing `displayed-functor` result and additionally recover
   the active `Transfd_cat K E D FF GG` head as a rich
   `displayed-transfor` result.
4. Add a `Nested_transfd_telescope_catd`-shaped TypeScript consumer covering
   direct object projection, internally owned outer base-arrow action,
   displayed-transfor component action, and one next-hom/further-hom
   judgment.
5. Keep final generic LF checking mandatory and add focused positive,
   step-bound/fail-closed, unknown-head, earlier-profile, and no-cast tests.
6. Use only existing generic runtime/checker/application engines and active
   transferred owners.

The gate explicitly has these non-effects:

- no Lambdapi source change;
- no new emdash mathematical owner, primitive, definition, rewrite rule, or
  `unif_rule`;
- no transfer declaration or runtime/proof-rule inventory change;
- no proof-time rule search during classifier inference;
- no coercion/cast term or external coherence evidence;
- no general mixed curry or arbitrary pointwise lambda body;
- no `Product_catd` alias/primitive and no curry/uncurry edit;
- no pullback-hidden classifier recognition;
- no unrestricted `:^nd`, arbitrary variance DAG, groupoidal, or metatheory
  claim;
- no text/browser/public-profile promotion in this tranche; and
- no bulk transfer, release, publication, push, merge, or cleanup.

The user has already approved the consolidated direction represented by this
gate. Under the standing unattended delegation, after this proposal is
checkpointed separately and receives no immediate human supersession, a
separate review may record exact D-DTTLF-USABILITY-029 approval and begin
implementation. Human correction always supersedes that review.

## Validation And Checkpoint Policy

For the plan-only checkpoint:

- inspect staged and unstaged diffs separately;
- run Markdown/link and `git diff --check` hygiene only; and
- commit only the dedicated plan, predecessor successor notice, and handoff
  route.

For `REFLECT-1A`/`TRANSFD-1B`:

- run the new focused tests and nearest mixed nested regressions;
- run root workspace check, typecheck, and lint as relevant;
- because shared categorical surface/program behavior changes, run exactly
  one complete `./scripts/pnpmw run check:ts` after focused work is green;
- carry forward the unchanged bounded Lambdapi authority evidence rather than
  rerunning `check:all`; and
- stage only the coherent implementation, tests, and synchronized plan.

The user authorizes bounded local checkpoint commits in the existing
`goal/typescript-elaborator-v3.2` worktree after each coherent green tranche.
No push, PR, merge to `main`, publication, release, amend, rebase, reset,
squash, history rewrite, branch/worktree removal, or unrelated cleanup is
authorized by this plan.

## Persistent `/goal` Launch Prompt

```text
Continue implementing
docs/TYPESCRIPT_ELABORATOR_V3_2_RECURSIVE_MIXED_NESTING_PLAN.md and treat its
Persistent /goal Launch Prompt and living Work/Decision Ledgers as part of the
objective.

Recover actual worktrees, branch ancestry, staged and unstaged changes,
active authority, predecessor completion evidence, linked decisions, and the
current dependency-ready row. Follow root AGENTS.md, emdash2/AGENTS.md when
the active kernel is involved, and
docs/PERSISTENT_GOAL_GIT_EXPERIMENTATION.md.

Advance the next dependency-ready slice toward recursive runtime-normalized
classifier reification and arbitrary finite qualified mixed nesting. Begin
with the active Nested_transfd_telescope_catd representative and retain
object, internal base-arrow, component/tdapp, and next-hom evidence. Preserve
the distinction between type formation/elimination and the deferred general
mixed curry/introduction problem.

Treat the active Lambdapi v3.2 kernel as mathematical authority. Infer with
bounded beta/delta/reviewed-runtime normalization and reify only canonical
active heads; do not let unrestricted proof-time unification drive inference.
Every categorical action must be internalized by existing owners. Never add
external naturality, variance, or coherence evidence, and fail closed for
unknown or unsupported classifiers.

Keep PRODUCT-FACADE-0A and CURRY-PACKAGE-0A as independent audits unless the
living dependency ledger makes one ready. Do not add a Product_catd primitive
or alias, mixed curry owner, kernel rule, transfer inventory, text/browser
promotion, bulk scale work, or broad semantic claim without a separately
frozen and approved gate.

Use proportional focused validation. Run one check:ts only when a bounded
shared-TypeScript tranche is otherwise green; do not run check:all or repeat
long aggregates for documentation-only or unchanged boundaries.

The user authorizes bounded local checkpoint commits in the existing
goal/typescript-elaborator-v3.2 branch after a coherent tranche is green, its
living ledgers are synchronized, the exact staged diff is clean, and unrelated
work is excluded. If a newly frozen bounded proposal receives no immediate
human response, the standing unattended delegation may record a separate
approval/review with human supersession. No push, PR, merge, publication,
release, destructive history operation, branch/worktree removal, or unrelated
cleanup is authorized.

Continue through dependency-ready rows with minimal human supervision and
update the living plan whenever evidence corrects the architecture. Stop for
a new mathematical owner/rule, a broader semantic claim, an unresolved
authority conflict, or an operation outside the stated Git boundary.
```

## Decision Ledger

- **2026-07-31 — consolidated recursive direction approved.** The user
  agreed that recursive mixed classifier reflection/nesting should precede
  general curry, and requested this dedicated plan plus continued
  implementation under a persistent goal.
- **2026-07-31 — classifier-refinement semantics clarified.** Current
  refinement is sound unchanged-term view recovery checked by the generic LF
  checker, but its exact syntax recognizer is not a scalable final
  architecture.
- **2026-07-31 — runtime/proof boundary retained.** Bounded
  beta/delta/runtime normalization selects canonical heads; unrestricted
  `unif_rule` search does not drive ordinary inference.
- **2026-07-31 — `Nested_transfd_telescope_catd` selected.** The active
  kernel already owns the next representative enrichment level, making it a
  high-yield, zero-kernel-delta stress test.
- **2026-07-31 — mixed curry remains later work.** The naive same-base
  product curry is ill-typed under directed variance; a future explicit map
  must use the two-sided Sigma/pullback context and receive its own
  Lambdapi-first gate.
- **2026-07-31 — product facade question reopened narrowly.** The prior audit
  still rejects an unjustified injective `Product_catd` primitive, but does
  not fully settle a consistently adopted transparent alias. A separate
  read-only audit will decide that maintainability question without blocking
  nesting.
- **2026-07-31 — curry/uncurry representation clarified.** Both ordinary
  directions may legitimately be transparent definitions. The real gap is
  full action and adjunction coherence, not a requirement that exactly one
  direction be primitive.
- **2026-07-31 — D-DTTLF-USABILITY-029 frozen.** The first implementation
  gate is the TypeScript-only runtime-backed reifier plus
  `Nested_transfd_telescope_catd` consumer above. It is non-self-authorizing
  until separately reviewed/checkpointed under the standing delegation.
- **2026-07-31 — D-DTTLF-USABILITY-029 approved exactly as proposed.** The
  proposal-only plan was independently checkpointed at `6828225`. The user's
  explicit direction to continue plus standing unattended delegation records
  a separate approval with human supersession. This authorizes only
  `RECURSIVE-MIXED-REFLECT-1A` and its first
  `RECURSIVE-MIXED-TRANSFD-1B` consumer, preserving every frozen non-effect;
  it adds no remote Git or kernel authority.
