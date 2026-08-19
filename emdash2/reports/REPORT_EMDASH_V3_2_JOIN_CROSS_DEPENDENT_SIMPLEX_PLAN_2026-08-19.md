# Emdash v3.2 Join-Cross Dependent-Simplex Plan

Date: 2026-08-19 (America/Toronto)

Plan-ID: `JOIN-CROSS-DEPENDENT-SIMPLEX-V3.2`

Status: **completed implementation plan**. The completed dependent-hom simplex
foundations plan isolates one exact prerequisite: compatibility between the
primitive cross datum supplied to join elimination and the cross cell obtained
by applying the resulting functor to the source join-cross transformation.
This plan resolves that prerequisite only as far as needed to construct the
canonical ordinal dimension-two dependent filler.

Branch: `goal/join-cross-dependent-simplex-v3.2`

Worktree: `/home/user1/emdash1-join-cross-simplex-v1`

Baseline: completed dependent-hom simplex checkpoint
`c5300b3a9b54b93f98e5ff626ec461b1d2edba68`.

Parent-Plan:
`REPORT_EMDASH_V3_2_DEPENDENT_HOM_SIMPLEX_FOUNDATIONS_PLAN_2026-08-19.md`

Depends-On:

- `emdash3_2.lp`, especially `join_cross_transf`, `join_elim_func`,
  `join_elim_cross_transf`, the left/right whole and point betas,
  `Prof_transf_cat`, `Prof_cell_eval`, and whole ordinary/displayed action;
- `emdash3_2_join_mapping_recursion.lp`, especially
  `join_map_observe_cross`, `join_map_observe_cross_at`,
  `join_map_extend_object`, and `join_map_extend_cross`;
- `emdash3_2_dependent_simplex_bridge.lp` for the canonical
  Hom/Sigma/`homd_` triangle and iterable next action;
- `emdash3_2_dependent_simplex_ordinal_adequacy.lp` for
  `OrdinalDependentSimplex2CanonicalFiller` and the conditional
  `ordinal_dependent_simplex2_observe`; and
- active Foundations, canonical notation, current SOP, report index, and the
  persistent-goal Git workflow.

Side-Task-Ledger: `JCDS-00`, `JCDS-BASE-1`, `JCDS-OWNER-2`,
`JCDS-WHOLE-3`, `JCDS-PROJECT-4`, `JCDS-SOURCE-5`, `JCDS-FILLER-6`,
`JCDS-OBSERVE-7`, `JCDS-PROFILE-8`, `JCDS-NEXT-9`, `JCDS-DOC-10`, and
`JCDS-CLOSE-11`.

Infinity-Codex-Origin: session
`019ffe39-2eb9-7080-88e3-06b77d69b8d1`; selected recommendation response
`0071_2026-08-19T15-45-39Z_01a01ab1-ffb1-78d0-98a1-12ae5ddf8280.md`.
That response is recovery evidence only. Active code/SOP and this evolving
ledger are authoritative.

## 1. Objective

Construct, rather than postulate, the canonical dependent triangle filler of
an arbitrary ordinal triangle functor:

```text
ordinal_dependent_simplex2_canonical_filler
  (H : Functor(DirectedSimplex_cat(2),C))
  : OrdinalDependentSimplex2CanonicalFiller(C,H).
```

Then remove the explicit filler argument from the public dimension-two
observation:

```text
ordinal_dependent_simplex2_observe_canonical(H)
  : DependentSimplexObservation(C,2).
```

The construction must be obtained through the source join-cross action and
the existing dependent-hom owners. An opaque filler constant or a separate
triangle record does not satisfy the goal.

## 2. Exact Missing Comparison

For object-level join mapping data

```text
d : JoinMapObjectData(A,B,C),
```

the current library exposes two cross cells with the same intended meaning:

```text
primitive(d)
  := join_map_extend_cross(d)

observed(d)
  := join_map_observe_cross(join_map_extend_object(d)).
```

`primitive(d)` reduces through `join_elim_cross_transf` to the cross field
stored in `d`. `observed(d)` applies the extended functor's hom action to the
source `join_cross_transf`. They are not currently connected.

The first task is to determine their exact typed relationship at the whole
`Prof_transf_cat` owner:

- definitional equality after one missing projection bridge;
- an equality/Path between whole cross objects;
- a directed higher cell dictated by the current lax profile; or
- a comparison living in a minimal Cat-valued coherent-square total.

Do not choose the answer by notation. Probe the owners and endpoint actions,
then promote the strongest computationally justified form.

## 3. Ownership Requirements

The comparison must satisfy this ladder:

```text
whole join-cross compatibility
  -> shaped component at arbitrary a:I->A and b:I->B
  -> terminal/walking-arrow component
  -> native dependent triangle filler
  -> retained next hom action.
```

Prefer the whole owner. A capped equality at the unique terminal component is
insufficient if it cannot be projected from an internally natural cell or
retain the action needed by the dimension-three follow-up.

The implementation must reuse:

```text
join_map_observe_cross
join_map_extend_cross
Prof_cell_eval
fdapp1_int_*
fapp1_func
DependentTriangle_catd.
```

It must not introduce a second profunctor-transformation semantics.

## 4. Source Triangle Specialization

After the generic compatibility is active, specialize it to

```text
DirectedSimplex_cat(2) = Join_cat(WalkingArrow_cat,Terminal_cat).
```

The selected source triangle must expose:

```text
edge 01
edge 02
edge 12
source dependent filler.
```

The generic join-eliminator point betas already make the three shared
vertices compute. The new comparison must supply the remaining cross/naturality
cell, not replace those point betas or add selected endpoint rewrites.

Construct the source filler at the native
`DependentTriangle_catd`/`Fibre_cat` type. If a readable endpoint conversion
is required, carry it propositionally through the existing endpoint-view
discipline rather than adding a broad join eta.

## 5. Mapping Under An Arbitrary Ordinal Triangle

For

```text
H : Functor(DirectedSimplex_cat(2),C),
```

map the canonical source triangle through the existing whole functor action.
The resulting term must inhabit exactly

```text
OrdinalDependentSimplex2CanonicalFiller(C,H).
```

The component should compute through the established functor compositor and
dependent-hom action. Keep the ambient directed/lax reading primary:

- for a general `H`, the filler need not be identity;
- for a decoded strict profile, only already-justified compositor cells may
  collapse;
- for `C = Path_cat(X)`, the filler should be an equality and admit `eq_sym`;
  and
- none of those profile specializations may replace the generic construction.

## 6. Unconditional Observation

Once the filler is canonical, define the public facade

```text
ordinal_dependent_simplex2_observe_canonical(H)
```

by applying the existing conditional constructor to that filler. Preserve the
conditional API as the explicit general interface unless a separate consumer
justifies retirement.

Reviewer acceptance requires:

1. the code is the intrinsic dimension-two code selected by edge 01;
2. faces 01, 02, and 12 compute through the promoted face action;
3. the top dependent component is the mapped source cross cell;
4. one next hom action remains available; and
5. a wrong source edge, target edge, or filler endpoint is rejected.

## 7. Dimension-Three Handoff

This plan does not implement full dimensions three and four ordinal
adequacy. It must, however, demonstrate that the canonical dimension-two
construction retains the whole next action required by the follow-up.

The closeout decision must state one of:

- the dimension-three source tetrahedron is directly the next action and a
  separate child plan may promote it;
- one precisely named higher join-cross compatibility remains; or
- the supposed whole comparison was too capped and must be redesigned before
  this plan can complete.

Dimension four remains the next plan's recursion test, not scope silently
added here.

## 8. Escalation Ladder

Use the smallest architecture that meets the objective:

1. derive the comparison from existing transparent owners;
2. if projection order blocks it, add one scoped bridge at the semantic owner;
3. if equality is mathematically wrong, expose the directed higher cell;
4. only if the whole cell cannot be typed otherwise, introduce the minimal
   Cat-valued coherent-square total required by this consumer.

Every escalation must retain a positive consumer and a corresponding
negative/non-collapse check. Do not jump directly to a generic collage,
equipment, double-category, or all-join equivalence framework.

## 9. Explicit Nonclaims

This plan does not claim or construct:

- a broad join eta or a mapping-category equivalence for every join;
- functor extensionality or proof irrelevance;
- a global mixed-variance category of dependent simplexes;
- full dimensions three/four ordinal adequacy;
- a complete semisimplicial nerve, degeneracies, Kan, Segal, Rezk, or
  complicial structure;
- a migration of historical global strict endpoint rules;
- a duplicate `FaceCode`, dependent-simplex code, or Hom/Sigma semantics;
- TypeScript/parser work; or
- integration, publication, deployment, or cleanup.

## 10. Module Strategy

Expected one-way modules are:

```text
emdash3_2_join_cross_compatibility.lp
  whole primitive/action-derived join-cross comparison and projections

emdash3_2_join_generator_compatibility.lp
  whole reindex/observation component paths and derived walking-generator beta

emdash3_2_dependent_simplex_ordinal_filler.lp
  source triangle, arbitrary-H filler, and unconditional observation.
```

Edit `emdash3_2.lp` only if an owner-position probe proves that the missing
computation is genuinely generic and belongs beside join elimination. Do not
mix a core normal-form migration with the dependent filler module.

## 11. Implementation Order

```text
baseline and owner inventory
  -> exact whole cross types and endpoint audit
  -> smallest whole compatibility probe
  -> shaped/terminal projections and retained action
  -> canonical source triangle
  -> arbitrary-H canonical filler
  -> unconditional dimension-two observation
  -> strict/Path/non-collapse review
  -> dimension-three next-action handoff
  -> authority synchronization and closeout.
```

At most one ledger row may be `in progress`.

## 12. Validation Policy

Follow `emdash2/AGENTS.md` exactly:

- keep every Lambdapi target within 90 seconds;
- place candidate rules at their semantic owner in a full-file probe;
- minimize inferred LHS slots and annotate any measured guard;
- compare quiet and warning-enabled runs;
- exercise unifiers with typed `eq_refl` if any are proposed;
- test both projection orders for every commuting bridge;
- retain whole and next-hom action rather than stopping at a component;
- pair positive computation with wrong-endpoint/non-collapse checks;
- run affected source/reviewer checks, strict LHS audit, catalog, and
  source-only health before local checkpoints; and
- eagerly avoid long aggregate checks unless omitting one would block
  trustworthy promotion or final closeout.

Warnings are diagnostic evidence, not an automatic veto. No promoted code may
use `--no-sr-check`.

## 13. Git And Authorization Boundary

The user's instruction to proceed with the recommended child goal authorizes:

- this dedicated local branch/worktree;
- implementation within this plan's scope; and
- SOP-compliant local checkpoint commits after bounded green tranches.

No push, merge, PR, tag, release, npm/Zenodo publication, deployment, history
rewrite, branch/worktree deletion, or unrelated mutation is authorized.

## 14. Execution Ledger

| Row | Status | Deliverable and acceptance boundary |
| --- | --- | --- |
| `JCDS-00` | complete | Dedicated child branch/worktree created from clean checkpoint `c5300b3`; scope, nonclaims, validation, and Git boundaries are recorded in this linked living plan. |
| `JCDS-BASE-1` | complete | Bootstrap and focused quiet checks of the core, join observation/extension source/reviewer, ordinal-adequacy source/reviewer, source TOC, active references, and report headers are green. No aggregate was run. |
| `JCDS-OWNER-2` | complete | The primitive and action-derived cross objects inhabit the same `Prof_transf_cat` after existing branch/point betas align endpoints. Direct conversion is false. A runtime rule cannot head the transparent defined observation alias; the next justified candidate is one whole equality/path computation principle at the join-recursion semantic owner, not a Cat-valued total. |
| `JCDS-WHOLE-3` | complete | `emdash3_2_join_cross_compatibility.lp` adds one propositional higher-constructor beta between the whole observed and primitive cross objects. `path_to_hom` turns it into a whole displayed transformation; direct conversion remains false and a wrong target is rejected. No runtime rule or stable-head migration is added. |
| `JCDS-PROJECT-4` | complete | The whole path projects to arbitrary shaped equality by `Prof_cell_eval`, to endpoint components by `tdapp0_fapp0`, and retains canonical `tdapp1_int_cell` base-arrow action. No duplicate expanded naturality wrapper or Cat-valued total is needed. |
| `JCDS-SOURCE-5` | complete | `emdash3_2_dependent_simplex_ordinal_filler.lp` reindexes the source join cross by the exact strict terminal profile used by selected edges 02 and 12. Its `fdapp1_int_cell` along the opposite walking generator is conjugated only by whole-derived edge paths and inhabits the canonical source filler; no filler constant is introduced. |
| `JCDS-FILLER-6` | complete | The source filler is packaged once as the existing native two-simplex, mapped through `dependent_simplex2_map(H)`, and projected at its top component. This constructs `ordinal_dependent_simplex2_canonical_filler(H)` in the exact `OrdinalDependentSimplex2CanonicalFiller(C,H)` type. |
| `JCDS-OBSERVE-7` | complete | `ordinal_dependent_simplex2_observe_canonical(H)` applies the existing explicit observation to the constructed filler. The reviewer verifies the code/edge-01 flag, visible normalized 02/12 faces, and top component. |
| `JCDS-PROFILE-8` | complete | The generic endpoints remain non-convertible; selected strict input uses the same construction with only existing compositor reductions; for `Path_cat(A)` the filler elaborates as equality and `eq_sym` supplies its inverse. A wrong final base edge is rejected. |
| `JCDS-NEXT-9` | complete | `ordinal_dependent_simplex2_native_map(H)` remains the whole `dependent_simplex2_map`, and `ordinal_dependent_simplex2_next_func(H)` exposes its next hom action. Dimension three may consume that action; dimension four is not implemented here. |
| `JCDS-DOC-10` | complete | Foundations, syntax, current status, root/package READMEs, AGENTS, report index, source/check registries, focused reviewers, catalog, and source-only health are synchronized to the constructive dimension-two result. |
| `JCDS-CLOSE-11` | complete | Every scoped row is implemented and validated; implementation/authority checkpoint `023a1c2` is clean and reviewable. No long aggregate or unauthorized integration, publication, deployment, history rewrite, or cleanup was performed. |

### 14.1 Launch And Whole-Type Audit — 2026-08-19

The dedicated worktree was created from clean checkpoint `c5300b3` and
bootstrapped with the pinned pnpm workspace. Focused quiet checks are green for
the core, join mapping source/reviewer, ordinal-adequacy source/reviewer, source
TOC, active references, and report headers. No aggregate was run.

The first ignored probe

```text
tmp/probes/join_cross_compatibility.lp
```

shows that

```text
join_map_observe_cross(join_map_extend_object(d))
join_map_extend_cross(d)
```

both elaborate in the same whole `Prof_transf_cat` after the existing join
branch and point betas align their endpoint functors. The equality type
`JoinCrossCompatibility(d)` is therefore well formed, while a direct
conversion assertion is correctly rejected. Evidence:

```text
logs/probes/join_cross_compatibility-20260819-115617.log.
```

A second ignored probe attempted the most direct runtime beta at the public
`join_map_observe_cross` surface. Lambdapi rejected the rule before semantic
checking because that surface is already a transparent defined alias:

```text
logs/probes/join_cross_runtime_beta-20260819-115802.log.
```

Changing the alias to an injective stable head would be a normal-form migration
and would force a competing generic-unfold/specialized-beta pair. There is no
current evidence that such a migration is required. The next candidate is a
single whole equality/path computation principle for join elimination,
analogous to a higher-constructor beta. Its equality-induced arrow can retain
component and next-hom projections without postulating the eventual ordinal
triangle filler. `JCDS-OWNER-2` is complete and `JCDS-WHOLE-3` is active.

### 14.2 Whole Propositional Cross Beta — 2026-08-19

The promoted module

```text
emdash3_2_join_cross_compatibility.lp
```

selects the propositional higher-constructor policy already used by other
categorical/HIT boundaries. `join_map_extend_cross_beta(d)` is a path from the
action-derived whole cross to the primitive cross supplied to join
elimination. It does not make those terms runtime-convertible.

The path induces

```text
join_map_extend_cross_cell(d)
  : observedCross(extend(d)) -> primitiveCross(d)
```

inside their common `Prof_transf_cat`. This is a whole displayed
transformation, not a capped component. Consequently:

- `join_map_extend_cross_shaped_beta` is obtained by `eq_ap` through
  `Prof_cell_eval` for arbitrary shape `I`;
- `join_map_extend_cross_component` is the canonical `tdapp0_fapp0`
  projection at an endpoint pair; and
- the next base-arrow action remains the direct generic
  `tdapp1_int_cell(join_map_extend_cross_cell(d),p,u)`.

An attempted named wrapper for that last action was rejected during promotion
because its expanded handwritten return type selected a competing projection
normal form. The generic owner itself checks and is retained; no duplicate
facade is introduced.

Quiet and warning-enabled source/reviewer checks are green with the unchanged
`1150/159` import-closure inventory:

```text
logs/probes/emdash3_2_join_cross_compatibility-20260819-120943.log
logs/probes/join_cross_compatibility-20260819-120946.log
logs/probes/emdash3_2_join_cross_compatibility-20260819-120948.log
logs/probes/join_cross_compatibility-20260819-120951.log.
```

The source adds no rule or unifier; strict LHS audit is vacuous. The reviewer
keeps direct nonconversion and wrong-target rejection. `JCDS-WHOLE-3` and
`JCDS-PROJECT-4` are complete. The active row now specializes the retained
base-arrow action to the canonical source triangle.

### 14.3 Whole Generator Bridge And Canonical Filler — 2026-08-19

The source specialization exposed two genuine whole projection boundaries,
not a missing pointwise simplex axiom:

```text
Fibre(Prof_reindex_transf(r,F,G),a,b)
  = Fibre(r,F(a),G(b))

Fibre(join_map_observe_cross(H),*)
  = fapp1_func(H) o walking_arrow_generator_func.
```

`emdash3_2_join_generator_compatibility.lp` records these as propositional
paths between whole functors. An attempted generic runtime reindex-component
rule did reduce the term but failed the dependent endpoint/subject-reduction
boundary, so it was rejected rather than promoted. The equality-induced whole
component cell retains another hom action. Combining the two paths with the
already-promoted `join_map_extend_cross_beta` derives
`join_map_generator_beta(F,G)`; no independent point or generator beta is
postulated.

The selected source construction fixes the exact terminal strict profile used
by both new triangle edges. Its reindexed whole cross has two components which
the derived generator beta identifies with edges 02 and 12. The opposite
walking generator supplies the raw naturality cell. The retained
terminal-coordinate action is compared propositionally with identity, and
equality-induced arrows conjugate the raw cell to the selected edge endpoints.
The resulting term checks directly as

```text
ordinal_simplex2_source_canonical_filler
  : OrdinalDependentSimplex2CanonicalFiller(Delta[2],id).
```

That source is then packaged through the existing native visible constructor.
For arbitrary `H : Functor(Delta[2],C)`, the whole existing
`dependent_simplex2_map(H)` maps this one object; its top Sigma projection is

```text
ordinal_dependent_simplex2_canonical_filler(H)
  : OrdinalDependentSimplex2CanonicalFiller(C,H).
```

The unconditional observation is the existing conditional constructor applied
to that term. Reviewer checks compute the intrinsic code/edge-01 flag, visible
02 and 12 faces, and the top filler. The generic source and target generator
functors remain runtime-distinct; a wrong base edge is rejected. A
`Path_cat(A)` target makes the filler an equality with `eq_sym` inverse, while
selected strict data uses the same construction and only the already-active
strict compositor reductions.

The whole mapped native object remains public and
`ordinal_dependent_simplex2_next_func(H)` exposes its next hom action. This is
the exact dimension-three handoff: a later child plan may inspect the image of
the source tetrahedral action, but this plan adds neither dimension-three
ordinal adequacy nor dimension four.

Focused quiet and warning-enabled source/reviewer checks are green:

```text
logs/probes/emdash3_2_join_generator_compatibility-20260819-141653.log
logs/probes/emdash3_2_dependent_simplex_ordinal_filler-20260819-140639.log
logs/probes/join_generator_compatibility-20260819-140936.log
logs/probes/dependent_simplex_ordinal_filler-20260819-141206.log
logs/probes/emdash3_2_join_generator_compatibility-20260819-141435.log
logs/probes/emdash3_2_dependent_simplex_ordinal_filler-20260819-141435.log
logs/probes/join_generator_compatibility-20260819-141435.log
logs/probes/dependent_simplex_ordinal_filler-20260819-141435.log.
```

The raw warning-marker inventory is unchanged at `1315` for sources and
`1316` for reviewers relative to the immediate predecessor closure. Both new
sources are rule-free, so strict LHS audit remains vacuous for this tranche.
`JCDS-SOURCE-5` through `JCDS-NEXT-9` are complete; documentation and final
closeout remain active.

### 14.4 Authority And Validation Synchronization — 2026-08-19

The two new sources are registered in both `scripts/check.sh` and
`scripts/check_metrics.py`; their two focused reviewers are discovered by the
standard examples runner. Foundations, canonical syntax, current status,
root/package READMEs, AGENTS, and the report index now distinguish the
constructed dimension-two theorem from the still-deferred higher-dimensional
and mapping-category claims.

Proportional gates are green:

- registered focused source checks for both new modules;
- focused quiet and warning-enabled checks for both sources and reviewers;
- unchanged predecessor warning-marker inventory (`1315/1316`);
- strict LHS audit (both new sources contain no rules or unifiers);
- check catalog strict verification;
- source TOC, active-reference, and report-header checks;
- `git diff --check` and Python compilation of the edited metrics registry;
- source-only health snapshot for `255` files, hash
  `sha256:3b45e3c9610c92b88de90848c201290dc26871bd0351cbb692b241a8b6e7fac4`.

No long aggregate was rerun: the new files and their complete import closures
were checked directly, while unchanged boundaries retain their recent green
evidence. At checkpoint preparation, `JCDS-DOC-10` was complete and
`JCDS-CLOSE-11` remained active only long enough to create and record the
authorized local implementation checkpoint and verify the final committed
boundary.

### 14.5 Local Checkpoint And Closeout — 2026-08-19

Implementation, focused reviewers, registries, authority prose, generated
source-only health, and the synchronized living ledger were committed locally
as

```text
023a1c2 feat(emdash2): construct canonical ordinal simplex filler
```

The checkpoint contains exactly the 15 scoped files reviewed by the staged
diff; the worktree had no unstaged overlap. Its parent is the earlier whole
join-cross checkpoint `a56def2`. No push, merge, PR, tag, release, publication,
deployment, history rewrite, branch/worktree deletion, or unrelated mutation
occurred. The final plan-only checkpoint records this hash and closes
`JCDS-CLOSE-11`.

The bounded result is complete. A future child goal may consume
`ordinal_dependent_simplex2_next_func(H)` to investigate dimension-three
ordinal adequacy. It should not reopen the completed dimension-two bridge or
silently include dimension four unless a new living plan explicitly does so.

## 15. Completion Definition

This goal is complete when:

1. primitive and action-derived join-cross data have a checked whole
   relationship, or the exact stronger owner required is demonstrated;
2. the source ordinal triangle filler is constructed through that relationship
   rather than postulated;
3. arbitrary `H` yields a canonical inhabitant of
   `OrdinalDependentSimplex2CanonicalFiller(C,H)`;
4. unconditional dimension-two observation computes on its code, faces, and
   dependent filler and retains higher action;
5. general/strict/Path claims are separated honestly;
6. the dimension-three next-action handoff is explicit;
7. affected authorities and evidence are synchronized; and
8. the worktree is reviewable with no unauthorized integration, publication,
   history rewrite, or cleanup.

Nearness to a context, token, or elapsed-time limit is not completion.
