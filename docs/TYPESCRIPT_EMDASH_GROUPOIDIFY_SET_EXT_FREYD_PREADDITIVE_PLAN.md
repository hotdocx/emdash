# TypeScript/emdash Set-Target Groupoidification Extensionality and Freyd Preadditivity Plan

Date: 2026-09-01

Plan-ID: `TS-EMDASH-GROUPOIDIFY-SET-EXT-FREYD-PREADDITIVE`

Status: active on a dedicated branch/worktree; initial plan checkpoint
`c412793`

Baseline: `0e8b390060c926757dd8fae8cbf95dd49b90da09`

Branch: `goal/groupoidify-set-extensionality-freyd-preadditive-v3.2`

Worktree: `/home/user1/emdash1-groupoidify-set-ext-freyd-v1`

Decision-Response-Evidence:

- `infinity-codex:01a02f68-6142-7e53-993a-4505aa8e2cbe:01a05ce3-8c7d-7c90-ba16-5397b8334012`

## Purpose

This plan supplies the exact generic extensionality principle required to
promote the completed Freyd class laws to arbitrary quotient-Hom points, then
packages the resulting first honest preadditive category:

```text
pointwise paths on Groupoidify generators into a set
  -> one whole transformation between restricted path-valued functors
  -> whole action of groupoidify extension
  -> set-target map extensionality
  -> arbitrary quotient-point additive and bilinearity laws
  -> generic PreadditiveCategory structure
  -> CommRingFreydPresentation_cat instance.
```

The primary mathematical point is that a full dependent eliminator for
`Groupoidify` is probably unnecessary. Every outstanding Freyd law takes
values in `CommRingFreydHomSet`, which is already a set. The smaller theorem
needed by the concrete consumer is approximately:

```text
groupoidify_set_map_ext

  S is a set
  h,k : Groupoidify(C) -> S

  (Pi x : Obj(C), h(unit(x)) = k(unit(x)))
  ------------------------------------------------
                     h = k.
```

This is a generic computational-and-internal bridge. It does not add an
external proof certificate, a user-written naturality square, a full
dependent HIT eliminator, or a source-functorial `Groupoidify` package.

## Operational Baseline And Git Boundary

The branch starts from the completed Freyd preadditive-descent checkpoint
`0e8b390`. Historical `main` remains at `85f459a`; this goal does not mutate
it. Orthogonal path-cubical and global-strictness worktrees remain excluded.

The user explicitly authorized this dedicated branch/worktree, a persistent
goal, and the established local validated-checkpoint workflow. Local commits
are permitted only after a bounded tranche is green, this ledger is
synchronized, and the exact staged diff excludes unrelated work. This does
not authorize push, merge, publication, release, PR creation, amend, rebase,
reset, history rewriting, branch deletion, or worktree removal.

Initial state is clean and the baseline is an ancestor of `HEAD`. The fresh
worktree was bootstrapped with the pinned workspace dependency graph.

Focused baseline evidence:

- `timeout 90s lambdapi check emdash3_2_groupoidification_universality.lp`:
  green;
- `timeout 90s lambdapi check
  emdash3_2_commutative_algebra_freyd_preadditive_class_laws.lp`: green; and
- no repository-wide aggregate was run.

## Existing Generic Owners

The implementation must reuse the current whole universal-property surface:

- `groupoidify_unit_func(C) : C -> Path_cat(Groupoidify(C))`;
- `groupoidify_extend_func(C,G)`, including its retained Hom action;
- `groupoidify_restrict_func(C,G)` and `groupoidify_restrict_hom_func`;
- `groupoidify_restrict_at_path(h)`;
- `groupoidify_extend_restrict_eta_at_path(h)`;
- `groupoidification_hom_omega`;
- `path_equiv_along` and ordinary equality action;
- strict pointwise whole-transformation/equivalence infrastructure;
- `is_prop_pi` and `is_trunc_pi`; and
- the restricted dependent `trunc_ind_ambient` eliminator.

The completed Freyd layer already supplies:

- groupoidified agreement categories and 0-truncated Hom sets;
- quotient zero, addition, negation, identity, and composition;
- sethood of each `CommRingFreydHomSet`;
- all additive-group and composition-distributivity laws on generating raw
  classes; and
- a deliberately limited `CommRingFreydClassPreadditiveEvidence` package.

The missing step is therefore generic extensionality/descent, not another
matrix or agreement algorithm.

## Pointwise Paths Into A Set As A Whole Transformation

### Required mathematical operation

For `F,G : C -> Path_cat(S)` and sethood evidence for `S`, define the data

```text
SetPathPointwiseData(S,F,G)
  := Pi x : Obj(C), F[x] = G[x].
```

The first owner audit must decide whether the current whole transformation
constructors can derive the following operation without a new stable symbol:

```text
set_path_pointwise_transf
  : SetPathPointwiseData(S,F,G)
    -> Transf(C,Path_cat(S),F,G).
```

If the primitive `Transf` classifier provides no constructor capable of this
assembly, add one narrowly scoped stable owner. Its component observation is

```text
tapp0(set_path_pointwise_transf(p),x) -> p(x).
```

Its whole transformation type retains all higher action. It must not ask a
consumer to supply a naturality square: because `S` is a set, the relevant
path spaces are propositions, so the naturality and higher coherence data are
unique. This is the same stable-whole-owner rationale already used where a
primitive transformation classifier cannot be assembled from independently
proved components.

The owner requires:

- one constructor-visible component beta;
- a noncollapse reviewer showing arbitrary pointwise paths are not identified;
- a retained next-Hom-action reviewer; and
- owner-position warning and inferred-slot audits before promotion.

It must not introduce runtime equations for generic `tapp*`, functoriality, or
naturality beyond the one constructor beta.

### Implemented owner-audit result

The audit confirmed that `Transf` is a primitive classifier and exposes no
record constructor from which arbitrary pointwise paths can be assembled.
The stable `set_path_pointwise_transf` owner is therefore required and has
been promoted in `emdash3_2_set_path_pointwise_transformation.lp`. Its sole
runtime rule is the component beta above, with every reconstructible implicit
LHS slot written as `_`.

The direct attempt to use pointwise unit paths as components of the restricted
functors also exposed a distinct, expected normal-form boundary:

```text
groupoidify_restrict_at(h)[x]
```

retains the stable Cat-level precomposition presentation and does not reduce
directly to `h(unit(x))`. No new precomposition rule was added. Instead,
`groupoidify_restrict_point_path` applies object evaluation by `eq_ap` to the
already existing whole `groupoidify_restrict_at_path`; this derives exactly
the needed point path and preserves the established runtime owner.

The whole `groupoidify_set_map_ext` construction then checks exactly as
planned. The focused warning comparison reports 1,274 baseline diagnostics
and 1,274 diagnostics with the new modules. Neither the new stable owner nor
the derived extensionality surface adds a critical-pair or replaceable-slot
warning. Strict LHS audits report zero unreviewed slots.

An attempted resumable health refresh in the fresh worktree found no complete
local resume state and began checking the broad registered corpus. It was
intentionally interrupted rather than violating the proportional-validation
boundary. No health result is claimed for that command; the generated health
snapshot remains assigned to `GSE-CLOSE-8A` after the substantive source set
is complete.

## Set-Target Groupoidification Extensionality

Given sethood evidence for `S`, maps

```text
h,k : Function_grpd(Groupoidify(C),S)
```

and pointwise generator paths

```text
p(x) : h(unit(x)) = k(unit(x)),
```

the intended whole construction is:

1. normalize the object observations of `groupoidify_restrict_at(h)` and
   `groupoidify_restrict_at(k)` to `h(unit(x))` and `k(unit(x))`;
2. assemble `p` into a whole transformation
   `eta : Transf(restrict(h),restrict(k))`;
3. apply the first Hom action of `groupoidify_extend_func` to `eta`, obtaining
   a path between `extend(restrict(h))` and `extend(restrict(k))`; and
4. compose that path with the existing eta/uniqueness paths
   `extend(restrict(h)) = h` and `extend(restrict(k)) = k`.

Schematically:

```text
h
  <- extend(restrict(h))
  -- extend[eta] -->
     extend(restrict(k))
  -> k.
```

The implementation should use explicit `eq_sym`/`eq_trans` over these named
whole paths rather than relying on unification transitivity. A theorem whose
only premise is `p` should expose the final path:

```text
groupoidify_set_map_ext_from_unit_paths(C,S,S_set,h,k,p) : h = k.
```

The first focused probe must check whether the existing transparent
`groupoidify_restrict_at` object projection already exposes `h(unit(x))`. If
it does not, add the smallest point observation/comparison at the existing
restriction owner; do not duplicate the whole restriction definition.

### Fallback boundary

If the whole transformation cannot be assembled cleanly even with sethood,
the fallback is a restricted proposition-valued `Groupoidify` induction
principle sufficient for this consumer. A general dependent eliminator is not
the automatic fallback. Any fallback must state exactly why the whole
extension/restriction construction failed and preserve the current HIT owner
boundary.

## Promotion Of Freyd Laws To Arbitrary Quotient Points

Every Freyd Hom is

```text
FreydHomSet(P,Q)
  := Trunc_0(Groupoidify(Agree(P,Q))).
```

The completed class laws cover points represented by raw presentation
morphisms. Promotion proceeds in two distinct stages:

1. set-target groupoidification extensionality proves equality of the relevant
   maps out of each raw agreement groupoidification from their values on the
   unit classes; and
2. `trunc_ind_ambient` extends the resulting proposition-valued statement
   from `trunc_intro` representatives to arbitrary 0-truncated points.

Use curried unary maps and repeated elimination rather than adding speculative
binary HIT machinery. Introduce binary or ternary extensionality helpers only
when a concrete law makes them materially clearer and they remain derived
from the unary theorem.

Promote, for arbitrary quotient points:

- additive right and left zero;
- additive associativity;
- additive commutativity;
- additive inverse, and the symmetric inverse law if not derived from
  commutativity;
- right distributivity of composition over addition; and
- left distributivity of composition over addition.

The target motives are equality types in sets and hence propositions. Their
truncation evidence should be constructed using existing sethood/path
lowering and `is_prop_pi`/`is_trunc_pi`, not declared opaquely.

### Implemented descent and law result

`emdash3_2_truncation_set_path_induction.lp` now packages exactly the unary,
curried-binary, and curried-ternary set-valued path induction used here. Each
operation is transparently derived from `trunc_ind_ambient`; no new eliminator
or runtime rule was added. Matching unary/binary/ternary groupoidification
helpers remain derived from repeated applications of the whole
`groupoidify_set_map_ext` theorem.

`emdash3_2_commutative_algebra_freyd_preadditive_laws.lp` uses those helpers in
two explicit stages and establishes on arbitrary quotient-Hom points:

- both additive zero orientations;
- associativity and commutativity;
- right inverse and the left inverse derived from commutativity;
- right distributivity; and
- left distributivity.

The sources for the ternary distributivity helpers may be different agreement
categories; the focused mixed-source probe checked this rather than relying
only on the equal-source associativity case.

## Generic Preadditive Category Package

After the arbitrary-point laws check, introduce the first honest generic
formal `PreadditiveCategory` structure. Its exact encoding must follow the
current record/Sigma conventions, but mathematically it supplies for every
`X,Y : Obj(C)`:

- `0 : Hom_C(X,Y)`;
- `+ : Hom_C(X,Y) -> Hom_C(X,Y) -> Hom_C(X,Y)`;
- unary `-`;
- abelian-group laws; and
- left and right bilinearity of categorical composition.

The package is evidence over the existing category and existing Hom carriers;
it does not introduce a parallel category grammar or replace generic
`id`/`comp_fapp0` owners. Construct:

```text
comm_ring_freyd_preadditive
  : PreadditiveCategory(CommRingFreydPresentation_cat(R)).
```

The resulting claim is preadditive, not additive. Zero objects and finite
biproducts are separate structure and remain the immediate successor goal.

### Implemented package result

`emdash3_2_preadditive_categories.lp` introduces reusable set-valued
`AbelianGroupStructure` and `PreadditiveCategory` packages with readable Hom
operation and bilinearity projections. The law basis is associativity,
commutativity, right zero, and right inverse, together with both composition
distributivity orientations. It is evidence over the existing category and
generic composition grammar.

`emdash3_2_commutative_algebra_freyd_preadditive.lp` constructs the Freyd
instance. A direct attempt to use semantic `comm_ring_freyd_comp` paths as
generic `comp_fapp0` laws correctly failed at the existing usability boundary.
The promoted construction instead composes the already checked
`comm_ring_freyd_comp_usability_path` at the outer composite and at both RHS
summands. No generic composition rewrite or new unifier was added.

The prior class-law target reports 1,300 warning instances and the completed
preadditive target also reports 1,300. The new descent, law, and packaging
modules contain no runtime or unification rules and add no diagnostics. Their
strict LHS audits are vacuously clean.

## TypeScript And Cross-Layer Boundary

The direct TypeScript Freyd category and matrix engine remain the computation
and conformance surface. This tranche may expose a preadditive capability or
formal symbol mirrors only when required by a concrete cross-layer consumer.
It must not replace direct algorithms with proof certificates or rerun a broad
TypeScript aggregate merely for reassurance.

Focused conformance should establish that direct zero/addition/negation and
composition agree with the now fully lawful formal package on selected
nontrivial and zero-rank cases. Existing recent green evidence may be carried
forward for untouched boundaries.

## Deliberate Non-Goals

This goal does not include:

- source-functorial `Groupoidify_func`;
- the `Groupoidify |- Path_cat` adjunction package;
- arbitrary dependent groupoidification;
- arbitrary pointwise-to-transformation assembly without a set-valued target;
- biproducts, zero objects, or an additive-category claim;
- weak kernels or the weak-kernel-to-Abelian theorem;
- Abelian-category structure;
- kernels, cokernels, exactness, or homology; or
- integration of the orthogonal path-cubical/global-strictness branch.

Source functoriality and the adjunction remain useful generic developments,
but they are orthogonal to the concrete Freyd blocker.

## Corrected Longer-Term Order

The selected dependency order is:

```text
set-target Groupoidify extensionality
  -> full Freyd preadditivity
  -> finite-free/presentation zero objects and biproducts
  -> additive-category packaging
  -> computable weak kernels
  -> weak-kernel-to-Abelian theorem
  -> kernels, cokernels, complexes, and homology.
```

The explicit biproduct/additive step is essential: the constructive Freyd
category theorem starts from an additive category with weak kernels, not
merely a preadditive one. The action-category/groupoidification/truncation
model remains the computational presentation of quotient Homs; later
Freyd/Abelian structure packages its consequences rather than replacing it.

## Implementation Sequence

1. Audit the exact restriction component normal form and available
   pointwise-to-whole constructors.
2. Probe the smallest set-valued whole pointwise transformation owner at its
   intended source position, including component, retained-action, and
   noncollapse consumers.
3. Promote the owner only after warning and inferred-slot classification.
4. Derive set-target groupoidification map extensionality from whole
   extension/restriction action and eta.
5. Add only the curried extensionality and proposition-valued truncation
   helpers required by concrete Freyd laws.
6. Promote every completed Freyd class law to arbitrary quotient points.
7. Introduce the generic `PreadditiveCategory` package and Freyd instance.
8. Extend focused formal reviewers and necessary TypeScript/Core/Lambdapi
   conformance.
9. Register new owners/reviewers and synchronize Foundations, current status,
   catalog, health, report index, and this ledger.
10. Run proportional final gates and checkpoint the completed boundary.

## Implementation Ledger

| Row | Status | Dependency | Deliverable and acceptance boundary |
| --- | --- | --- | --- |
| `GSE-PLAN-0` | complete; initial plan checkpoint recorded in branch history | completed Freyd checkpoint `0e8b390` | living plan, isolated branch/worktree, clean baseline, focused checks, Git limits, persistent goal |
| `GSE-AUDIT-1A` | complete; checkpoint `de9fcb9` | plan | exact restriction component and pointwise-whole owner audit with an explicit accept/reject observation |
| `GSE-SET-TRANSF-2A` | complete; checkpoint `de9fcb9` | owner audit | whole set-valued pointwise transformation, component beta, retained action, noncollapse, warnings and LHS audit |
| `GSE-MAP-EXT-3A` | complete; checkpoint `de9fcb9` | set transformation | generic set-target map extensionality constructed from extension/restriction and eta |
| `GSE-TRUNC-LIFT-4A` | complete; formal-preadditive checkpoint pending | generic extensionality | unary/binary/ternary derived helpers actually required to pass from generators to arbitrary quotient points |
| `GSE-FREYD-LAWS-5A` | complete; formal-preadditive checkpoint pending | class laws | arbitrary-point additive-group and both bilinearity laws for every Freyd Hom |
| `GSE-PREADDITIVE-6A` | complete; formal-preadditive checkpoint pending | Freyd laws | generic formal preadditive package and checked Freyd instance; no additive claim |
| `GSE-CONFORMANCE-7A` | ready | formal package | focused reviewers and only necessary TS/Core/Lambdapi conformance |
| `GSE-CLOSE-8A` | blocked by accepted/deferred rows | all rows | standing docs, catalog, health, proportional CI, final ledger and checkpoints |

Rows may be split, rejected, or deferred only with durable evidence and a
synchronized ledger. Difficulty alone is not evidence for an opaque axiom.

## Initial Decisions

| Decision | Status | Rationale |
| --- | --- | --- |
| `D-GSE-001` | accepted | Set-target map extensionality is the smallest concrete generic prerequisite; a full dependent Groupoidify eliminator is not selected. |
| `D-GSE-002` | accepted | The proof remains whole: pointwise unit paths assemble one transformation, whose extension action is composed with existing eta paths. |
| `D-GSE-003` | accepted after owner audit | `Transf` is primitive and has no exposed constructor; a narrow stable set-pointwise whole transformation owner is required. |
| `D-GSE-004` | accepted | Consumers never supply naturality squares; sethood makes the relevant coherence proposition-valued. |
| `D-GSE-005` | accepted | Any new runtime rule is limited to the stable owner's constructor-visible component; generic tapp/fapp computation remains globally owned. |
| `D-GSE-006` | accepted | Freyd promotion uses set-target map extensionality followed by existing truncation induction, with currying rather than speculative n-ary eliminators. |
| `D-GSE-007` | accepted | A full PreadditiveCategory claim waits for arbitrary quotient-point laws; the completed class evidence is not silently rebranded. |
| `D-GSE-008` | accepted | Preadditive is not additive; zero objects and biproducts are the next structural gate. |
| `D-GSE-009` | accepted | Groupoidify source action/adjunction and arbitrary dependent induction are orthogonal non-goals. |
| `D-GSE-010` | accepted | No repository-wide TypeScript or repository aggregate is required during the focused implementation loop. |
| `D-GSE-011` | accepted after projection probe | Restriction points are derived by applying `eq_ap` to the existing whole restriction path; no generic precomposition runtime rule is added. |
| `D-GSE-012` | accepted after warning comparison | The component beta adds no diagnostics: the focused baseline and candidate each report 1,274 warning instances, and strict LHS audits are clean. |
| `D-GSE-013` | accepted after arity probes | Only unary, binary, and ternary derived groupoidification/truncation helpers are promoted; no speculative n-ary or general dependent eliminator is introduced. |
| `D-GSE-014` | accepted after mixed-source probe | Ternary descent supports distinct source agreement categories and therefore covers both bilinearity orientations, not only Homwise associativity. |
| `D-GSE-015` | accepted after packaging probe | `PreadditiveCategory(C)` retains set-valued abelian-group structures on existing Homs and both laws for existing generic composition. |
| `D-GSE-016` | accepted after failed direct generic-composition probe | Semantic Freyd bilinearity does not definitionally inhabit generic `comp_fapp0` bilinearity; explicit existing usability paths reframe all three composite occurrences. |
| `D-GSE-017` | accepted after warning comparison | The class-law and completed preadditive targets both report 1,300 diagnostics; rule-free descent and packaging add no warning family. |

## Validation Matrix

For semantic owner changes:

- disposable owner-position probe with a positive typed consumer;
- component beta and retained higher-action reviewer;
- relevant noncollapse/wrong-endpoint reviewer;
- bounded quiet check;
- warning-enabled comparison and classification;
- strict inferred-slot audit for each changed Lambdapi source;
- affected reviewer example check;
- catalog and health synchronization after registration; and
- bounded `make ci` only at the final substantive semantic boundary.

For plan/documentation-only checkpoints, inspect the exact diff and use
Markdown/link hygiene only. Do not run unrelated TypeScript, print, book, or
repository aggregates.

## Persistent Goal Launch Prompt

Continue `TS-EMDASH-GROUPOIDIFY-SET-EXT-FREYD-PREADDITIVE` from the living
plan in
`docs/TYPESCRIPT_EMDASH_GROUPOIDIFY_SET_EXT_FREYD_PREADDITIVE_PLAN.md`.
Treat active source and the Lambdapi SOP as authority. Work only in
`/home/user1/emdash1-groupoidify-set-ext-freyd-v1` on branch
`goal/groupoidify-set-extensionality-freyd-preadditive-v3.2`, preserving
baseline `0e8b390060c926757dd8fae8cbf95dd49b90da09` as comparison evidence.
Resume the first dependency-ready ledger row, update the ledger and decisions
as experiments refine the design, and follow owner-position probes, warning
classification, LHS audits, focused reviewers, catalog/health synchronization,
and bounded-at-90-seconds Lambdapi checks. Avoid repo-wide long aggregates.
Local validated checkpoint commits are authorized after each bounded coherent
tranche is green and the exact staged diff is reviewed. Do not push, merge,
publish, release, create a PR, amend, rebase, reset, rewrite history, delete a
branch, or remove a worktree. The goal is complete only when every scoped row
is implemented, rejected with durable evidence, or explicitly deferred behind
a concrete prerequisite, and all affected authorities are synchronized.
