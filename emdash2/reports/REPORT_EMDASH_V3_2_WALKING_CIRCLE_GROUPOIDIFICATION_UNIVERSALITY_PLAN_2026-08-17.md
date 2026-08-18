# Emdash v3.2 WalkingEnd--Circle Groupoidification Universality Plan

Date: 2026-08-17 (America/Toronto)

Plan-ID: `WALKING-CIRCLE-GROUPOIDIFICATION-UNIVERSALITY-V3.2`

Status: **active consumer-first implementation plan**. `WCGU-00`,
`WCGU-RES-1`, `WCGU-EXT-2`, and `WCGU-EQUIV-3` are complete; `WCGU-MONO-4`
is complete and `WCGU-GENERIC-5` is the next dependency-ready row.
Local green checkpoint commits are authorized by the user's
standing instruction for this continuation. Push, merge, publication,
release, history rewrite, branch deletion, and worktree removal are not
authorized.

Parent:
`REPORT_EMDASH_V3_2_INTERNAL_LAXITY_AND_GROUPOIDAL_REALIZATION_CONTINUATION_PLAN_2026-08-17.md`,
row `ILGR-GROUPIFY-1`

Depends-On: active `emdash3_2.lp`; the completed Circle/Integer and
WalkingEnd comparison; completed internal-laxity, path-realized pseudo-laxity,
computational-truncation, and profiled right-Gray-closure tranches; active
`Path_cat_func`, generic whole precomposition, Circle and WalkingEnd
eliminators, `OmegaEquivAlong`, and strict pointwise-to-whole equivalence
owners; the current Foundations, SOP, and canonical-syntax reports

Supersedes: no completed implementation plan. It reopens only
`ILGR-GROUPIFY-1` through the consumer-first universality slice selected here.
The evolved ignored notebook
`emdash2/.scratchpad/groupoidal-closure-circle-analysis-2026-08-14.md`
remains recovery evidence and is not an active implementation ledger.

Side-Task-Ledger: `WCGU-00`, `WCGU-RES-1`, `WCGU-EXT-2`, `WCGU-EQUIV-3`,
`WCGU-CIRCLE-COMP-TODO`, `WCGU-MONO-4`, `WCGU-GENERIC-5`, and
`WCGU-CLOSE-1`

Infinity-Codex-Origin: session
`019ffe39-2eb9-7080-88e3-06b77d69b8d1`; selected continuation response
`01a0129f-2701-7bd1-84a9-c763381f2518`

Infinity-Codex-Decision-Responses: response `0045`, archived at
`/home/user1/emdash1/emdash2/tmp/ai-responses/sessions/2026-08-14_019ffe392eb9/responses/0045_2026-08-18T02-12-56Z_01a0129f-2701-7bd1-84a9-c763381f2518.md`.
Active code and SOP, then this plan and its parent decision record, outrank
the archive.

Baseline: completed profiled-Gray ledger checkpoint
`df8540ac53b36b4ac4901e8c8aa54e38ad7a7554`

Worktree: `/home/user1/emdash1-groupoidal-circle-v1`

Branch: `goal/walking-circle-groupoidification-v3.2`

## Objective

Strengthen the existing concrete comparison

```text
walking_to_circle_func : WalkingEnd_cat -> Circle_cat
```

from power-level group-completion evidence to a whole, iterable universal
mapping property against groupoidal targets.

For every `G : Grpd`, the selected forward map is restriction along the
comparison:

```text
walking_circle_restrict_func(G)
  : Hom_cat(Grpd_cat,Circle_grpd,G)
      -> Functor_cat(WalkingEnd_cat,Path_cat(G)).

walking_circle_restrict_func(G)[h]
  = path_map_func(h) o walking_to_circle_func.
```

The first full acceptance candidate is

```text
OmegaEquivAlong
  Cat_cat
  (Hom_cat Grpd_cat Circle_grpd G)
  (Functor_cat WalkingEnd_cat (Path_cat G))
  (walking_circle_restrict_func G).
```

This is the concrete hom-comparison expected if `Circle_grpd` realizes the
free groupoidal completion of `WalkingEnd_cat`. It is deliberately tested
before declaring a generic `Groupoidify_func : Cat_cat -> Grpd_cat`.

## Why This Is The Next Dependency-Ready Goal

The parent plan's implementation sequence completes generic internal-laxity
extraction, its path/pseudo realization, computational truncation, and one
profiled right Gray closure before returning to groupoidification. Those
prerequisites are now all green. The remaining `ILGR-GROUPIFY-1` reopening
condition is a new universal-property consumer rather than another concrete
power calculation.

This slice supplies that consumer while reusing all four completed lines:

```text
Circle and WalkingEnd recursors
    -> whole restriction by Path_cat_func and precomposition
    -> extension from the image of base and loop
    -> path-valued pseudo coherence on higher action
    -> whole beta/eta mapping-object equivalence.
```

The result distinguishes free inversion from truncation. Only after free
inversion may the already-computing truncation reflector form
`Trunc_ntype(n,Groupoidify(C))`.

## Scope Boundary

### In scope

- an anti-duplication audit of the exact whole restriction, Circle extension,
  WalkingEnd observation, transformation, next-action, and equivalence owners;
- the transparent whole restriction functor assembled from
  `Path_cat_func` and `comp_cat_con_func(walking_to_circle_func)`;
- its object computation to literal precomposition and its retained first
  hom action;
- a consumer-led extension operation taking a whole functor
  `WalkingEnd_cat -> Path_cat(G)` to the Circle function selected by its base
  object and generator path;
- the smallest whole action on transformations and higher cells necessary to
  make that extension a functor, reusing the internal-action/path-realization
  calculus rather than adding an independent coherence record;
- whole beta and eta evidence packaged, if feasible, as
  `OmegaEquivAlong Cat_cat` for the fixed restriction functor;
- a universe-valued monodromy reviewer: an automorphism/equivalence gives a
  Circle-indexed groupoid family whose WalkingEnd restriction recovers the
  selected generator; and
- a recorded decision whether the observed interface is sufficient to
  promote a generic computational groupoidification reflector.

### Explicitly out of scope

- postulating an opaque generic groupoidification adjunction before the
  concrete whole inverse and its higher action are understood;
- claiming a construction of free coherent inversion for every category when
  only the WalkingEnd consumer has been implemented;
- primitive mutually defined `Groupoidify_n` operations; the truncated tower
  is derived from generic groupoidification and `Trunc_ntype` if both exist;
- mirror Gray closure, complete Crans--Gray monoidal structure, or a global
  strict-cut migration;
- a generic HIT/declaration language, complete simplicial object, or generic
  all-dimensional coherence theorem;
- book, article, TypeScript, npm, browser, deployment, or publication work;
  and
- long repository-wide aggregates except at a genuinely affected closeout
  boundary.

## Settled Architectural Decisions

### 1. Restriction is semantic composition, not a new kernel primitive

The active kernel already supplies

```text
fapp1_func(Path_cat_func,Circle_grpd,G)
  : Hom_cat(Grpd_cat,Circle_grpd,G)
      -> Functor_cat(Circle_cat,Path_cat(G))
```

and

```text
comp_cat_con_func(walking_to_circle_func)
  : Functor_cat(Circle_cat,Path_cat(G))
      -> Functor_cat(WalkingEnd_cat,Path_cat(G)).
```

Their ordinary functor composite is the intended restriction owner. The first
probe must use this transparent semantic term. A new stable head or rule is
justified only if a real projection loses the object or next-hom action.

### 2. The extension must be whole, not merely objectwise

Given

```text
F : Functor WalkingEnd_cat (Path_cat G),
```

the object-level candidate is clear:

```text
x_F := F[walking_base],
p_F := F[walking_loop] : x_F = x_F,
extend(F) := circle_rec(G,x_F,p_F) : Circle_grpd -> G.
```

This is not yet a functor on the mapping category. `WCGU-EXT-2` must identify
how a transformation `F => H` and its next cells act on these selected Circle
functions. The recent whole laxity and path-realization work is relevant
precisely here. A capped object map does not meet the goal.

### 3. The concrete equivalence precedes generic abstraction

The consumer may reveal one of three honest outcomes:

1. the existing eliminators and whole action assemble the mapping-object
   equivalence transparently;
2. one narrow higher-recursion/projection owner is genuinely missing and can
   be added with focused computation and a negative consumer; or
3. generic uniqueness/coherence is not constructible at the present kernel
   boundary, in which case the exact prerequisite is recorded and generic
   groupoidification remains deferred.

Outcome 3 is not repaired by postulating `Adjunction` alone. The active
adjunction interface packages already constructed functors, unit, counit, and
triangle computation; it does not synthesize free coherent inversion.

### 4. Truncation follows free inversion

If a generic reflector is eventually promoted, its finite tower is derived:

```text
Groupoidify_le_ntype(n,C) := Trunc_ntype(n,Groupoidify(C)),
Groupoidify_le_carrier(n,C) := ElNType(n,Groupoidify_le_ntype(n,C)).
```

No truncation of the Circle may stand in for groupoidifying WalkingEnd: the
set truncation of the connected Circle is contractible, whereas its loop
group before set truncation is `Integer`.

## Initial Reuse And Gap Matrix (`WCGU-00`)

| Desired observation | Existing owner/evidence | Initial decision |
| --- | --- | --- |
| WalkingEnd-to-Circle comparison | `walking_to_circle_func`, base/loop betas, power theorem | Reuse unchanged. The new result strengthens its universal status rather than changing its computation. |
| Circle functions acting on paths | `Path_cat_func`, `path_map_func`, full next-hom action | Reuse the whole first action; do not rebuild a functor from pointwise `eq_ap`. |
| Restriction by the comparison | `comp_cat_con_func`, its generic precomposition action | Transparent composition is expected to own objects, transformations, and higher cells. Probe before adding any facade. |
| Extracted WalkingEnd base and loop | generic `fapp0`, `fapp1_fapp0`; WalkingEnd constructor observations | Reuse. The loop already lands in an equality because the target is `Path_cat(G)`. |
| Circle extension on objects | `circle_rec`, `circle_rec_beta_base`, `circle_rec_beta_loop_path` | Object-level construction is available. Whole variation in `F` remains the central gap audit. |
| WalkingEnd functor construction | `walking_end_rec_func` and constructor betas | Supplies the expected restricted object after extension; uniqueness as a whole mapping object is not yet active. |
| Pseudo coherence in path targets | `emdash3_2_path_pseudo_laxity.lp` | Reuse when the extension's action reaches transformations/higher cells. Do not declare a second pseudo hierarchy. |
| Pointwise-to-whole equivalence assembly | `emdash3_2_strict_pointwise_equivalences.lp`, `OmegaEquivAlong` | Candidate packaging after coherent inverse action exists; it cannot manufacture that action. |
| Generic adjunction packaging | `Adjunction`, unit/counit projections, triangle cut rules | Consumer-gated final packaging only; not the construction mechanism. |
| Universe-valued monodromy | univalence/`ua`, Circle recursor, existing `CircleCode` precedent | Use as the first named target-side reviewer after the generic-`G` boundary is understood. |

## Execution Ledger

| Row | Status | Deliverable and acceptance boundary |
| --- | --- | --- |
| `WCGU-00` | complete | The dedicated branch starts at `df8540a`; all worktrees were clean; the archive verifies from the original root; owning Circle/WalkingEnd/path modules pass their focused baselines; and the rule-free restriction probe is green. It established the stable precomposition object normal form, its proof-time raw-composition reading, base evaluation, dependent generator `PathOver`, retained first hom action, and a concrete mismatched-target rejection. |
| `WCGU-RES-1` | complete | `emdash3_2_walking_circle_restriction.lp` and its focused reviewer promote the whole forward map without a rule or unifier. Direct source/reviewer and affected central diagnostics pass. Its warning inventory is exactly `1122/159`, identical to the predecessor import; the strict LHS audit is zero; and the regenerated catalog contains 2,182 checks across 107 areas with zero unclassified checks. Source registration, active authority routing, and lightweight report/TOC/reference/script gates are synchronized. The replacement all-target health snapshot remains deferred to closeout. Checkpoint: `e240c3e`. |
| `WCGU-EXT-2` | complete | `emdash3_2_walking_circle_extension.lp` promotes the narrow whole categorical-HIT recursor missing from the object-only Circle interface. Its object projection computes to Circle recursion on the WalkingEnd base and generator; transformation action is compared propositionally with the path obtained from pointwise Path equivalences and functor-category univalence; generic `fapp1_func` retains the next action. The source and eight-check reviewer pass directly, including a mismatched-target rejection. The single object rule has exact zero warning delta against its import-only control (`1123/159` on both), and strict LHS audit remains zero. The already near-limit monolithic diagnostics target was restored unchanged after two clean 90-second import-graph timeouts; its previous green/catalog evidence is carried forward, while the focused reviewer owns this extension's regressions. Checkpoint: `2149219`. |
| `WCGU-EQUIV-3` | complete | `emdash3_2_walking_circle_universality.lp` adds exactly the two scoped categorical-HIT uniqueness clauses needed for `extend o restrict = id` and `restrict o extend = id` as paths between whole functors. It packages restriction as `walking_circle_groupoidification_hom_omega : OmegaEquivAlong Cat_cat`; both selected inverse projections compute to the whole extension, whose first and second hom actions remain available. Circle/WalkingEnd point and generator observations are derived by `eq_ap`/`eq_apd`, including both dependent loop boundaries. Direct source and 12-check reviewer pass with a mismatched-target rejection; the rule-free source has exact zero warning delta from extension (`1123/159`), and strict LHS audit remains zero. The focused reviewer owns regressions under the already-recorded monolithic-target budget decision. Checkpoint: `e0b20f7`. |
| `WCGU-CIRCLE-COMP-TODO` | deferred | Revisit judgmental computation for the Circle path constructor after `WCGU-EQUIV-3`, or earlier only if a concrete consumer shows that propositional loop beta materially obstructs computation. Any promotion is a separate normal-form migration with owner-position, subject-reduction, critical-pair, warning, and downstream audits; it is not silently bundled into universality. |
| `WCGU-MONO-4` | complete | `emdash3_2_walking_circle_monodromy.lp` specializes universality at `Grpd_grpd`. A self-`TypeEquiv(A,A)` is decoded to `grpd_equiv_path(e)`, forms the canonical WalkingEnd representation, and extends to the literal Circle recursor on that loop. Whole beta recovers the original representation after restriction; base and loop paths are derived, and transport around the actual family loop agrees with `type_equiv_to(e)`. The rule-free source and seven-check reviewer pass, including a mismatched-codomain rejection, with exact zero warning delta (`1123/159`) and zero LHS growth. Checkpoint: to be recorded after this green tranche commit. |
| `WCGU-GENERIC-5` | pending | Decide from the completed consumer whether a reusable `Groupoidify_func`, unit, transpose, higher action, and `Adjunction(Groupoidify_func,Path_cat_func)` can be promoted honestly. Implement only the validated generic layer, or record the exact free-inversion prerequisite and keep the generic reflector deferred. |
| `WCGU-CLOSE-1` | pending | Synchronize source/example ownership, master ledger, Foundations/SOP/canonical syntax, report index, catalog, warnings/LHS evidence, and proportional health/CI only for the boundary actually changed. Record remaining book, Gray-mirror, strict-cut, and HIT work separately. |

## First Focused Experiment

The initial probe asks only whether the following transparent term typechecks
and retains generic action:

```text
walking_circle_restrict_probe(G)
  := comp_cat_con_func(walking_to_circle_func)
       o fapp1_func(Path_cat_func,Circle_grpd,G).
```

It must check:

1. the whole functor type above;
2. object action on an arbitrary `h : Circle_grpd -> G`;
3. the base and generator observations of the resulting WalkingEnd functor;
4. `fapp1_func` on an arbitrary equality between two Circle functions; and
5. rejection at a distinct target groupoid or mismatched comparison endpoint.

The probe is rule-free. Failure is evidence about semantic composition or a
missing projection; it is not authority to add a broad rewrite.

### Completed `WCGU-00` / `WCGU-RES-1` result — 2026-08-17

The transparent whole term typechecks exactly as proposed. Its object action
does not reduce to raw `comp_cat_fapp0`; it correctly retains
`hom_precomp_along_fapp0` as the runtime owner. The existing narrowly typed
identity-family unifier validates the raw-composition reading through a typed
`eq_refl`, without selecting a second runtime normal form.

Projecting that whole functor path at `walking_base` yields
`walking_circle_restrict_base_path`. Projecting the generator requires
dependent rather than homogeneous action because the loop classifier depends
on the functor's base image. The promoted
`walking_circle_restrict_loop_pathover` is therefore an `eq_apd`/`PathOver`
whose target computes to `eq_ap(h,circle_loop)`. This is stronger and more
type-correct than forcing a pointwise loop equality after erasing endpoint
transport.

The source and reviewer are rule-free and pass directly. The affected central
diagnostics pass, the warning-enabled source has exactly the predecessor's
`1122` critical-pair and `159` replaceable-slot diagnostics, the strict LHS
audit remains zero, and the strict catalog is current at 2,182 checks in 107
areas with no unclassified checks. No aggregate `make check`, `make examples`,
health, CI, TypeScript, print, book, or repository-wide test was rerun. The
next row must now solve the genuinely new question: whole variation of
`circle_rec` in a WalkingEnd functor and its transformations.

### Completed `WCGU-EXT-2` result — 2026-08-17

The object-level inverse candidate is the expected Circle recursion:

```text
extend(F)(x) := circle_rec(F[walking_base],F[walking_loop],x).
```

The missing structure was not another pointwise formula but one whole functor
owner varying this recursion over the mapping category. A transformation
`eta : F => H` into `Path_cat(G)` is pointwise an equality and hence a
pointwise `OmegaEquivAlong`. The existing strict pointwise-to-whole assembly
turns that data into `F = H`; applying the object extension function gives the
semantic path between the two selected Circle functions. The promoted
`walking_circle_extend_func(G)` owns that action at every hom level. Its
object projection computes at runtime, its first-arrow action is compared to
the semantic path by `walking_circle_extend_transf_agrees`, and
`walking_circle_extend_next_func` confirms that the generic action remains
iterable.

This deliberately preserves the active HIT computation policy. Circle point
beta is judgmental, while Circle loop beta and the extension's first-arrow
agreement remain propositional. WalkingEnd's contextual generator beta is
already judgmental. The deferred `WCGU-CIRCLE-COMP-TODO` row records a
separate reviewed migration toward judgmental Circle path-constructor
computation if `WCGU-EQUIV-3` or another concrete consumer demonstrates a
material payoff; universality does not silently change global normal forms.

Direct source and focused reviewer checks pass. The warning-enabled source and
its import-only control both report exactly `1123` critical-pair and `159`
replaceable-slot diagnostics, so the new object rule has zero warning delta;
strict LHS audit remains zero. Importing the extension and duplicating its
reviewer assertions in the already near-limit `emdash3_2_checks.lp` exceeded
the mandatory 90-second target ceiling twice without an assertion failure.
That redundant edit was removed, leaving the monolith byte-for-byte unchanged
and its prior green 2,182-check/107-area catalog evidence applicable. The
focused eight-check reviewer is therefore the executable regression owner for
this tranche. Source registration, authority routing, TOC, active-reference,
report-header, script-syntax, catalog-strictness, and diff-hygiene gates are
green. Health, CI, and all-target aggregates remain deferred to the affected
closeout boundary.

### Completed `WCGU-EQUIV-3` result — 2026-08-18

The anti-duplication audit found no existing whole uniqueness theorem for
either the object-only Circle recursor or the WalkingEnd recursor. Following
the already established categorical-HIT universality pattern, the promoted
module adds only two scoped equality owners:

```text
extend_G o restrict_G = id
restrict_G o extend_G = id.
```

These are paths in whole functor classifiers, not pointwise equations and not
runtime folds. They therefore retain the generic action on transformations
and all subsequent homs. Together with the already constructed whole
extension, they produce

```text
OmegaEquivAlong
  Cat_cat
  Hom(Circle,G)
  Functor(WalkingEnd,Path(G))
  restrict_G.
```

Both selected inverse projections reduce to `walking_circle_extend_func(G)`.
The reviewer checks its first hom action and one further action explicitly.
Evaluating the two whole cancellation paths yields arbitrary-object, base,
and generator observations on both sides. Generator observations use
`PathOver`, so endpoint transport is retained rather than erased by an
ill-typed homogeneous equality.

This probe also settles the immediate effect of the current HIT computation
policy: propositional Circle loop beta does **not** block universality. The
Circle-side loop boundary follows by dependent action on the whole uniqueness
path, without a new loop rewrite. `WCGU-CIRCLE-COMP-TODO` therefore remains a
separate deferred normal-form improvement, not a prerequisite for the next
consumer.

Direct source and focused 12-check reviewer checks pass. The universality
module is rule-free and has exactly the extension source's warning inventory,
`1123/159`; strict LHS audit remains zero. The central monolith remains
unchanged under the `WCGU-EXT-2` target-budget decision, and its prior strict
catalog evidence is carried forward. Health, CI, and all-target aggregates
remain deferred to closeout.

### Completed `WCGU-MONO-4` result — 2026-08-18

For a groupoid `A` and self-equivalence `e`, the selected univalence decoder
gives

```text
grpd_equiv_path(e) : A = A.
```

The ordinary WalkingEnd recursor makes this the generator of a whole
representation in `Path_cat(Grpd_grpd)`. Applying the newly established
inverse produces a Circle-indexed family which computes to

```text
circle_rec(Grpd_grpd,A,grpd_equiv_path(e)).
```

The result is not merely a familiar objectwise code construction. The whole
beta path proves that restricting this family recovers the original
WalkingEnd representation. Its projections recover the base and generator,
and applying the existing transport/univalence comparison proves that
transport around the actual Circle loop sends `a : A` to
`type_equiv_to(e,a)`.

The source and focused seven-check reviewer pass directly, including a
mismatched-codomain rejection. The module is rule-free and inherits exactly
the universality source's `1123/159` warning inventory; strict LHS audit
remains zero. It therefore validates the mapping-object theorem through a
mathematically meaningful local-system/monodromy consumer without adding a
second Circle code family, new univalence principle, or consumer-specific
computation rule.

## Validation Policy

Every Lambdapi target is bounded to 90 seconds. Use focused probes and direct
source/reviewer checks during each row. Compare warnings and run strict LHS,
subject-reduction, catalog, and health gates only when their owning artifacts
change. Carry forward the exact profiled-Gray closeout evidence for unchanged
boundaries and avoid repository-wide aggregates for reassurance.

Any new rule must be tested in a temporary full-file copy at its intended
owner position, use a minimal LHS with every retained inferred slot audited,
have a positive typed consumer and relevant negative/non-collapse case, and
receive warning/critical-pair classification before promotion.

## Git And Recovery Policy

- Work only in `/home/user1/emdash1-groupoidal-circle-v1` on
  `goal/walking-circle-groupoidification-v3.2`.
- Treat `df8540a` as the immutable comparison/backtracking anchor, never as
  permission to reset descendants.
- Inspect all worktrees, staged/unstaged state, ancestry, active plans, and
  current owners at every continuation.
- Commit only a bounded green tranche after synchronizing this ledger and
  reviewing the exact staged diff plus `git diff --cached --check`.
- Prefer correcting commits; do not amend, rebase, reset, or hide failed
  experiments.
- Do not push, merge, publish, release, remove the worktree, or delete either
  branch without separate user authorization.

## Persistent Goal Objective

Continue `EMDASH-V3.2-WALKINGEND-CIRCLE-GROUPOIDIFICATION-UNIVERSALITY` by
following this living plan and its parent master plan. Select only the next
dependency-ready row; use existing whole semantic owners before primitive
heads; keep every Lambdapi target under 90 seconds; avoid long aggregate
reruns unless an affected closeout cannot otherwise be qualified; obey the
rewrite/unification and checkpoint SOPs; and make only user-authorized local
green checkpoint commits in the dedicated branch/worktree. Complete the goal
only when every scoped row is implemented, rejected with durable evidence, or
explicitly deferred behind a concrete prerequisite.
