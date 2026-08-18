# Emdash v3.2 Generic Groupoidification And Free Inversion Preliminary Plan

Date: 2026-08-18 (America/Toronto)

Plan-ID: `GENERIC-GROUPOIDIFICATION-FREE-INVERSION-V3.2`

Status: **active living implementation plan with a bounded first-consumer
launch**. The current persistent goal owns only `GGFI-00` and
`GGFI-INTERVAL-1`; later rows remain proposed.

Parent:
`REPORT_EMDASH_V3_2_INTERNAL_LAXITY_AND_GROUPOIDAL_REALIZATION_CONTINUATION_PLAN_2026-08-17.md`

Depends-On: completed WalkingEnd--Circle whole universality; stable
path-realized pseudo-laxity; computational truncation; profiled Gray action;
the completed dependent Circle loop-computation tranche; active
`emdash3_2_walking_arrow.lp`; current generic functor/internal-action and
categorical-HIT patterns; current Foundations, SOP, and canonical syntax

Supersedes: no implementation plan. It supplies the concrete reopening design
required by completed decision row `WCGU-GENERIC-5`.

Side-Task-Ledger: `GGFI-00`, `GGFI-INTERVAL-1`, `GGFI-TRIANGLE-2`,
`GGFI-SIGNATURE-3`, `GGFI-HIT-4`, `GGFI-EQUIV-5`, `GGFI-SOURCE-6`,
`GGFI-ADJ-7`, and `GGFI-CLOSE-8`

Infinity-Codex-Origin: session
`019ffe39-2eb9-7080-88e3-06b77d69b8d1`; decision responses `0047` and `0049`

Infinity-Codex-Decision-Responses: response `0047`, archived at
`/home/user1/emdash1/emdash2/tmp/ai-responses/sessions/2026-08-14_019ffe392eb9/responses/0047_2026-08-18T04-34-51Z_01a01322-f029-7f01-9030-f0af5473569a.md`,
and response `0049`, archived at
`/home/user1/emdash1/emdash2/tmp/ai-responses/sessions/2026-08-14_019ffe392eb9/responses/0049_2026-08-18T06-12-24Z_01a0137e-a757-7393-a1b3-f9cd9b67e435.md`.
The latter selects the groupoidal interval as the bounded next goal. Active
code/SOP and this living plan outrank both archives.

Baseline: clean completed Circle closeout checkpoint
`29ff54dcea87082782592251abade27f1bc0fa78`

Worktree: `/home/user1/emdash1-groupoidification-interval-v1`

Branch: `goal/groupoidification-interval-v3.2`

Git authority: the user's explicit adoption of response `0049` authorizes
this dedicated descendant worktree and validated local checkpoint commits.
It does not authorize push, merge, publication, release, history rewrite,
branch deletion, or worktree removal.

## Current Launch Boundary

The active goal is the first non-endomorphism vertical slice only:

```text
GGFI-00 + GGFI-INTERVAL-1
```

It adopts the plan, reuses the existing directed walking arrow, constructs the
groupoidal interval and its dependent computation, and proves the whole
mapping-object equivalence against every groupoidal target. Completion of
this launch does **not** authorize `GGFI-TRIANGLE-2`, the generic indexed HIT,
`Groupoidify_func`, source functoriality, or the adjunction. Those later rows
require a subsequent explicit continuation after the interval evidence is
reviewed.

## Objective

Construct rather than merely postulate the computational left adjoint to the
groupoidal-path inclusion:

```text
Groupoidify_func : Cat_cat -> Grpd_cat
Groupoidify_func |- Path_cat_func.
```

For `C : Cat` and `G : Grpd`, its defining whole mapping property is

```text
Hom_Grpd(Groupoidify(C),G)
  ~=
Functor(C,Path_cat(G)).
```

The selected forward map is precomposition with a computing unit

```text
groupoidify_unit_func(C)
  : Functor C (Path_cat(Groupoidify(C))).
```

The inverse is a whole categorical-HIT recursor/extension. It must compute on
objects and on every represented cell level selected by the implementation,
retain higher action, and satisfy whole beta/eta uniqueness. Only after that
construction exists may the existing `Adjunction` package record
`Groupoidify_func |- Path_cat_func`.

## Mathematical Boundary

Groupoidification freely inverts directed arrows. It is not:

- `Core_cat(C)`, which retains only arrows already invertible and is the
  right-adjoint direction;
- homotopy truncation, whose input is already groupoidal and which lowers
  homotopy dimension;
- an opaque declaration of `Groupoidify`, a unit, and an adjunction record;
  or
- the one-source-shape theorem
  `Groupoidify(WalkingEnd) ~= Circle`, which is evidence for the intended
  interface but does not construct arbitrary endpoint, composition, or higher
  coherence.

Once generic free inversion exists, the truncation tower remains derived:

```text
Groupoidify_le_ntype(n,C) := Trunc_ntype(n,Groupoidify(C)).
```

Free inversion happens first; Postnikov truncation happens second.

## Anti-Duplication Findings

### Reuse the active directed walking arrow

`emdash3_2_walking_arrow.lp` already defines

```text
WalkingArrow_cat = Join_cat(Terminal_cat,Terminal_cat)
walking_arrow_src
walking_arrow_tgt
walking_arrow_generator : src -> tgt
walking_arrow_generator_func
walking_arrow_generator_next_func.
```

It is not a handcrafted interval: the generator is a projection of the whole
internally natural join-cross action and retains its next hom action. The
first generic-groupoidification consumer must reuse it unchanged.

### No active groupoidal interval exists

There is no `Interval_grpd`/groupoidal walking-isomorphism HIT in the active
source. A small groupoidal interval is therefore a legitimate first consumer,
not duplicate functionality. It should have two points and one path, with
dependent elimination and judgmental point plus dependent-path betas.

### No active composable-pair classifier exists

No active walking composable pair/2-simplex facade was found. Its directed
source should be derived, not postulated, from the same join infrastructure:

```text
WalkingPair_cat := Join_cat(WalkingArrow_cat,Terminal_cat).
```

The first and second edges, their composite, and retained next actions should
be projections from existing join/functor owners. A dedicated facade is
justified only to stabilize those selected observations.

### Existing owners package but do not synthesize free inversion

`Path_cat_func`, ordinary precomposition, `OmegaEquivAlong`, `Adjunction`,
strict pointwise-to-whole equivalence, internal laxity, and path-realized
pseudo-laxity are all reusable after an inverse has been constructed. None
creates inverse paths for arbitrary directed arrows. `Core_cat` and telescope
localization have the wrong source boundary.

## Consumer 1 — Walking Arrow To Groupoidal Interval

Introduce the smallest groupoidal HIT exposing endpoint variation:

```text
Interval_grpd : Grpd
i0 i1        : Interval_grpd
iseg         : i0 = i1.
```

Its dependent eliminator takes

```text
D    : Interval -> Grpd
b0   : D(i0)
b1   : D(i1)
ell  : PathOver(D,iseg,b0,b1)
```

and computes at both points and at the dependent path constructor. The stable
`eq_apd` owner and Circle rule supply the reviewed implementation pattern;
ordinary `eq_ap` need not become a new global owner.

Construct

```text
walking_arrow_to_interval_func
  : Functor WalkingArrow_cat (Path_cat Interval_grpd)
```

with endpoint and generator computation inherited from the HIT. For every
`G : Grpd`, prove the whole mapping-object equivalence

```text
Hom_Grpd(Interval_grpd,G)
  ~=
Functor(WalkingArrow_cat,Path_cat(G)).
```

The inverse extends `F` from the two endpoint objects and
`F[walking_arrow_generator]`. Whole beta/eta, retained first and next hom
action, mismatched-endpoint rejection, and a nontrivial two-endpoint consumer
are mandatory. Contractibility of the interval is a useful derived theorem,
not the construction mechanism or substitute for the mapping property.

This row tests what WalkingEnd could not: a generator whose source and target
differ.

## Consumer 2 — Composable Pair And Groupoidal 2-Simplex

The second source shape must make composition data visible. Derive a directed
three-object source from `Join_cat(WalkingArrow_cat,Terminal_cat)` and expose:

```text
f01 : 0 -> 1
f12 : 1 -> 2
f02 : 0 -> 2
composition observation relating f12 o f01 and f02.
```

The groupoidal target should not hide that relation by retaining only two
paths. Its explicit computational facade is a 2-simplex-shaped HIT:

```text
Delta2_grpd : Grpd
d0 d1 d2   : Delta2_grpd
p01        : d0 = d1
p12        : d1 = d2
p02        : d0 = d2
fill012     : p02 = eq_trans(p01,p12).
```

This presentation mirrors the generic indexed construction in which every
selected source arrow, including an already-formed composite, has an image
path, while a next-dimensional constructor records preservation of source
composition. Its eliminator must expose the point/path data and the dependent
image of `fill012`; the next `eq_apd`/PathOver action should own that higher
beta rather than a manually duplicated square.

The acceptance theorem is the whole mapping equivalence between functions
out of `Delta2_grpd` and functors from the directed walking pair into
`Path_cat(G)`, including an explicit projection of the composition coherence
and one retained next action. This row must document how today's globally
strict prototype supplies the selected compositor endpoint while preserving
the explicit higher witness needed by an eventual lax-profile migration.

This is a vertical test, not a claim that all simplicial identities or a
generic simplex object have been constructed.

## Generic Indexed Categorical-HIT Design

Only after both consumers pass should the recurring structure be abstracted.
The preferred primitive boundary is not an infinite handwritten family of
`Groupoidify_n` declarations. It is one groupoidal formation together with a
whole unit functor and a whole recursor:

```text
Groupoidify(C) : Grpd

groupoidify_unit_func(C)
  : Functor C (Path_cat(Groupoidify(C)))

groupoidify_extend_func(C,G)
  : Functor
      (Functor_cat C (Path_cat G))
      (Hom_cat Grpd_cat (Groupoidify(C)) G).
```

The unit's object projection is the point constructor. Its first hom action
is the path constructor for a directed arrow. Reapplying generic hom action
provides the constructors/observations for represented higher cells. Identity,
composition, and higher coherence must be visible through that iterable
whole owner and the already-extracted lax/pseudo action; they must not be an
ever-growing external record of equations.

Required computation and uniqueness:

```text
extend(F)[unit(x)]            --> F[x]
dependent action on unit(f)   --> F[f]
next action on a source cell  --> selected higher action of F

restrict o extend = id
extend o restrict = id
```

The exact runtime-versus-propositional boundary must be selected from the two
concrete consumers. At minimum, object and canonical dependent first-cell
betas should be judgmental. Whole beta/eta paths own uniqueness and preserve
iteration. Merely declaring the last two equalities without a computing
recursor is insufficient.

## Source Functoriality And Adjunction

For `H : Functor C D`, source action should be derived by extending the
composite unit

```text
groupoidify_unit_func(D) o H
  : Functor C (Path_cat(Groupoidify(D))).
```

This gives

```text
Groupoidify(H) : Groupoidify(C) -> Groupoidify(D).
```

Identity/composition paths should follow from whole HIT uniqueness; no
constructor-specific source-functoriality registry is planned. Only after
this action and its next hom are checked should the facade

```text
Groupoidify_func : Functor Cat_cat Grpd_cat
```

and the adjunction with `Path_cat_func` be assembled. Unit/counit observations
must reduce to the already-checked unit, restriction, and extension owners.

## Execution Ledger

| Row | Status | Deliverable and acceptance boundary |
| --- | --- | --- |
| `GGFI-00` | complete | The authorized worktree/branch descends cleanly from Circle checkpoint `29ff54d`; bootstrap and workspace contract pass. The anti-duplication scan finds the existing join-derived `WalkingArrow_cat`, distinct endpoints, whole generator, and retained next action, but no active `Interval_grpd`, interval eliminator, or walking-arrow/interval mapping theorem. Focused walking-arrow, Circle-computation, and WalkingEnd--Circle universality baselines pass in 2.6--3.0 seconds; no aggregate ran. |
| `GGFI-INTERVAL-1` | in progress | The public `emdash3_2_groupoidal_interval_hit.lp` and `examples/groupoidal_interval_hit.lp` now validate formation, distinct endpoints, the generating path, both point betas, judgmental dependent path beta, constant-family recursion, the propositional ordinary-`eq_ap` view, and arbitrary-section/nonjudgmental-`eq_ap` negatives. The source is registered and the focused checks pass in 2.5--2.6 seconds. Next: reuse `WalkingArrow_cat` for the comparison functor, whole mapping equivalence, retained higher action, and further endpoint-sensitive reviewers. Do not declare generic groupoidification yet. |
| `GGFI-TRIANGLE-2` | proposed | Derive the walking composable pair from join; implement the explicit groupoidal 2-simplex/composition filler and whole mapping equivalence; retain one next-dimensional coherence and document the strict/lax profile boundary. |
| `GGFI-SIGNATURE-3` | proposed | Compare the two consumers and record the smallest uniform indexed categorical-HIT signature. Reject an opaque adjunction or a cell-by-cell handwritten infinite record. |
| `GGFI-HIT-4` | proposed | Promote `Groupoidify(C)`, its whole unit, and target-varying whole extension with object/first-cell computation and iterable higher action. Include wrong-source/target rejection and warning/LHS/subject-reduction audits. |
| `GGFI-EQUIV-5` | proposed | Derive restriction along the unit and package whole beta/eta as `OmegaEquivAlong Cat_cat` for arbitrary `C` and groupoidal `G`; reinstantiate WalkingEnd/Circle, interval, and triangle consumers without duplicating their proofs. |
| `GGFI-SOURCE-6` | proposed | Derive source-functorial action by extension, including identity/composition paths and retained next hom action; promote `Groupoidify_func` only after those checks pass. |
| `GGFI-ADJ-7` | proposed | Package `Groupoidify_func |- Path_cat_func`, with unit/counit/triangle observations routed through the existing computation and uniqueness owners. Distinguish it explicitly from `Core_cat`. |
| `GGFI-CLOSE-8` | proposed | Synchronize sources/reviewers, Foundations/SOP/syntax, catalog/health and any publication-facing boundary; record remaining higher-cell/profile limitations honestly. |

## First Interval Owner Probe — 2026-08-18

The ignored owner-position probe
`tmp/probes/groupoidal_interval_hit_owner.lp` validates the intended smallest
HIT boundary before any public module is added. It declares two distinct
points, one generating path, a dependent eliminator, two point rules, and the
selected higher-constructor computation

```text
eq_apd(
  (lambda x, interval_ind(D,b0,b1,ell,x)),
  interval_seg)
    --> ell.
```

Typed reflexivity proves the dependent path beta. An arbitrary dependent
section over the same generating path remains non-convertible to `ell`, and
the two endpoint constants remain distinct. The quiet probe passes in 2.127
seconds; its warning-enabled owner-position run passes in 2.249 seconds. It
adds no critical-pair family or broad replaceable-slot warning: the imported
inventory remains `1112/159`.

The nested eliminator arguments require a measured guard policy. Replacing
all of `D`, `b0`, and `b1` by `_` fails subject reduction. Retaining only `D`,
only `b1`, both endpoint data without `D`, or `D` with `b0` also fails.
Retaining `D` with `b1` typechecks, but omitting `b0` introduces a new
decision-tree arity-mapping warning. The clean candidate therefore retains
all three nested arguments and records the compiler's three localized
"need not be named" advisories as intentional guard diagnostics. The final
candidate has no arity warning and no new unjoinable critical pair.

That probe established formation/elimination feasibility only. The next
subsection records its public promotion; the WalkingArrow comparison functor,
whole restriction/extension equivalence, retained higher action, and further
endpoint-sensitive reviewers remain outstanding.

## Public Interval Formation And Elimination — 2026-08-18

`emdash3_2_groupoidal_interval_hit.lp` promotes the probed boundary under the
stable names `Interval_grpd`, `interval_i0`, `interval_i1`, `interval_seg`,
and `interval_ind`. Both point reductions and the selected dependent
`eq_apd(interval_ind,interval_seg)` constructor beta are judgmental. Named
typed views expose those reductions without introducing a second normal form.

The constant-family specialization `interval_rec` computes at both endpoints
and inherits the dependent path beta. Its ordinary `eq_ap` comparison remains
propositional and reuses `const_pathover_path_eq_apd` plus
`const_pathover_path_const`; those generic observations are currently owned
by the Circle HIT module, so this first interval file imports that reviewed
implementation rather than duplicating it or changing the global `eq_ap`
boundary.

The focused source and reviewer each pass in approximately 2.6 seconds. The
warning-enabled source check retains the imported `1112` unjoinable critical
pairs and introduces none. As measured in the probe, the public path rule has
three localized named-pattern advisories (`D`, `b0`, and `b1`), no arity-map
warning, and an explicit nested-guard comment. The strict rule audit reports
zero unreviewed compound slots. `scripts/check.sh` now registers the source;
the check-catalog strict consistency gate remains green. No aggregate ran.

The remaining `GGFI-INTERVAL-1` work starts at the directed comparison and
whole mapping equivalence. This checkpoint does not imply interval
universality, generic free inversion, or any later source-shape row.

## Acceptance And Stop Conditions

Promotion of generic names is blocked unless both source-shape consumers are
green. A failure of the interval mapping equivalence means endpoint-varying
extension is not understood. A failure of the 2-simplex row means composition
coherence is not understood. Either failure should revise or defer the
generic signature rather than be hidden by opaque unit/counit constants.

The generic goal is complete only when:

- `Groupoidify(C)` is computationally formed for arbitrary `C`;
- its unit and target extension retain at least one nontrivial higher action;
- restriction is a whole mapping-object equivalence for every groupoidal
  target;
- source functoriality is derived and checked;
- the adjunction is assembled from those owners; and
- the interval, triangle, and WalkingEnd/Circle instances are recovered.

## Validation Policy

Every Lambdapi target remains bounded to 90 seconds. Each row begins with a
focused owner-position probe, a positive real consumer, and an endpoint or
non-collapse negative. Warning comparisons and strict LHS audits are required
for every new rule. Catalog and health evidence are refreshed only at affected
checkpoints/closeout, reusing exact successes for unchanged boundaries. Long
root, TypeScript, browser, print, book, or package aggregates are outside this
kernel goal unless a changed cross-layer contract makes one strictly
necessary.

## Current Persistent Goal Objective

```text
Complete the bounded first-consumer launch of
GENERIC-GROUPOIDIFICATION-FREE-INVERSION-V3.2 according to
emdash2/reports/REPORT_EMDASH_V3_2_GENERIC_GROUPOIDIFICATION_FREE_INVERSION_PRELIMINARY_PLAN_2026-08-18.md,
through rows GGFI-00 and GGFI-INTERVAL-1 only. Reuse WalkingArrow_cat;
construct the groupoidal interval HIT with judgmental dependent constructor
betas; establish its whole mapping-object equivalence, retained higher action,
and positive/negative reviewer. Do not begin GGFI-TRIANGLE-2 or declare
generic Groupoidify. Use the authorized dedicated branch/worktree and local
green checkpoints; avoid unnecessary aggregates; do not push, merge, publish,
release, rewrite history, delete branches, or remove worktrees.
```
