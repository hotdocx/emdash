# Emdash v3.2 Ordinal Dimension-Four And Recursive-Source Plan

Date: 2026-08-21 (America/Toronto)

Plan-ID: `ORDINAL-DEPENDENT-SIMPLEX-DIMENSION-FOUR-RECURSIVE-SOURCE-V3.2`

Status: **active implementation plan**. This child plan first constructs the
ordinal dimension-four dependent simplex from the completed dimension-three
whole action. It then extracts and implements the smallest genuinely internal
Nat-indexed source package and successor operation justified by the checked
dimensions, rather than extrapolating an unverified all-dimensional theorem.

Branch: `goal/ordinal-dependent-simplex4-v3.2`

Worktree: `/home/user1/emdash1-ordinal-simplex4-v1`

Baseline: completed ordinal dimension-three closeout checkpoint
`f19fb44cf9b3248d5e59ff4209a3e1aad3eff787`.

Parent-Plan:
`REPORT_EMDASH_V3_2_ORDINAL_DEPENDENT_SIMPLEX_DIMENSION_THREE_PLAN_2026-08-19.md`

Depends-On:

- `emdash3_2_dependent_simplex_ordinal_dimension3.lp` for the one canonical
  ordinal tetrahedron, its arbitrary-target image, four face observations,
  whole post-laxity transformation, and retained next hom action;
- `emdash3_2_dependent_simplex_dimension4.lp` for `DependentSimplex4_cat`,
  `dependent_simplex4_map`, constructor-visible fourth-level objects, the
  first readable split, and the deliberately retained 1234/top frame;
- `emdash3_2_dependent_simplex_codes.lp` and
  `emdash3_2_dependent_simplex_code_map.lp` for intrinsically indexed flag
  codes and whole mapped decoding in arbitrary finite dimension;
- `emdash3_2_dependent_simplex_faces.lp` for variable-dimensional whole
  nonempty-face action and its retained higher action;
- `emdash3_2_shaped_pathout.lp`, the active join-cross compatibility stack,
  and the ordinary/displayed internal-action owners for the successor cell;
  and
- active Foundations, canonical notation, current SOP, report index, and the
  persistent-goal Git workflow.

Side-Task-Ledger: `ODS4R-00`, `ODS4R-BASE-1`, `ODS4R-OWNER-2`,
`ODS4R-SOURCE-3`, `ODS4R-MAP-4`, `ODS4R-FACES-5`, `ODS4R-PROFILE-6`,
`ODS4R-NEXT-7`, `ODS4R-REC-DESIGN-8`, `ODS4R-REC-IMPLEMENT-9`,
`ODS4R-REC-COMPUTE-10`, `ODS4R-DOC-11`, and `ODS4R-CLOSE-12`.

Infinity-Codex-Origin: session
`019ffe39-2eb9-7080-88e3-06b77d69b8d1`; dimension-three completion response
`0094_2026-08-21T15-35-00Z_01a024a4-09bc-74c0-9446-d83fdec4a23a.md`.
That response is recovery evidence only. Active code/SOP and this evolving
ledger are authoritative.

## 1. Objective

The goal has two ordered parts.

First, construct the intrinsic dimension-four observation of every ordinal
four-simplex functor

```text
H : Functor(DirectedSimplex_cat(4),C)
```

as the image of one canonical native source

```text
ordinal_dependent_simplex4_source
  : Obj(DependentSimplex4_cat(Delta[4],...)).
```

The five tetrahedral faces `0123`, `0124`, `0134`, `0234`, and `1234`, the
dependent top component, and one further whole hom action must be observable
from that one object. No opaque four-simplex filler or flat five-face record
satisfies this part.

Second, use the checked dimensions zero through four to implement a genuine
variable-dimensional source interface. The intended public object package is
initially

```text
OrdinalDependentSimplexSource(n)
  := Sigma c : DependentSimplexCode(Delta[n],n), Obj(decode(c)).
```

This signature is provisional until the dimension-four owner audit decides
whether source construction must additionally retain a whole action or typed
endpoint-view field. The final interface must reuse the existing intrinsic
code, mapped decoder, face action, `PathOut_cat`, and internal-action tower. It
must not duplicate their semantics in a parallel code grammar.

## 2. Why Dimension Four Comes First

The completed dimension-three source is strong evidence for iteration, not an
all-dimensional theorem. Its final public handoff is

```text
ordinal_simplex3_top_whole
ordinal_simplex3_top_next_action(u,v).
```

The next action is indexed by higher arrows between two source cells. The
first audit must determine whether the ordinal four-simplex supplies the
required concrete higher input directly from the next join-cross action, or
whether another whole fixed-source/internal-action projection is missing.

Dimension four is also where the native readable boundary stops flattening:
after face `0234`, the existing implementation retains a recursive frame
containing face `1234` and the top filler. A correct ordinal construction must
carry that frame through its existing typed endpoint views. Adding a Sigma
eta, endpoint normalization rule, or dimension-specific projection would hide
the very recursive structure this plan is meant to identify.

## 3. Exact Dimension-Four Boundary

Present the standard shape recursively:

```text
Delta[4] = Join_cat(Delta[3],Terminal_cat).
```

For arbitrary `H : Functor(Delta[4],C)`, restriction along the five selected
cofaces gives five ordinal tetrahedra. Their already-constructed
dimension-three observations must form one native fourth-level object:

```text
flag       = tetrahedron 0123
target     = tetrahedron 0124
base       = tetrahedron 0134
first fibre projection = tetrahedron 0234
recursive residual      = tetrahedron 1234 plus top cell.
```

The source should be constructed first for `id : Delta[4] -> Delta[4]` and
then mapped under arbitrary `H` by the existing `dependent_simplex4_map`.
Face observations should use the variable-dimensional
`dependent_simplex_face_func` wherever it provides the relevant whole owner;
dimension-specific aliases may expose readable names but must not own a
second face semantics.

## 4. Dimension-Four Owner Audit

The first implementation tranche must relocate, not assume, the following
ladder:

```text
whole join/internal action at the Delta[3] successor
  -> concrete higher input for ordinal_simplex3_top_next_action
  -> arrow between native tetrahedra 0123 and 0124
  -> DependentSimplex4_cat source object
  -> dependent_simplex4_map(H)
  -> five face observations and recursive final frame
  -> one retained next hom action.
```

Audit whether `ordinal_simplex3_top_next_action` is exactly the required
distinct-endpoint action. If its public endpoints are too specialized, expose
a transparent projection of the underlying whole owner rather than adding a
new action semantics. If the concrete input belongs to the next join-cross
beta, project it there and retain its own action.

The audit must distinguish:

1. a real missing higher input;
2. a stable-owner/projection-order mismatch;
3. the typed formal/readable endpoint comparison already represented by
   `DependentSimplexEndpointView`; and
4. a genuinely missing whole successor operator.

Only item 4 justifies a new generic owner.

## 5. Canonical Source And Arbitrary Mapping

The canonical source must be an actual object of the existing flagged
classifier. Schematically:

```text
omega01234
  : Hom(DependentSimplex3_cat(...),s0123,s0124)

ordinal_dependent_simplex4_source
  := dependent_simplex4(...,s0123,s0124,omega01234).
```

`omega01234` must come from the retained recursive action, including its base
cell and dependent fibre. It may be reframed propositionally by named whole
paths, but may not be replaced by an opaque filler.

For arbitrary `H`, define the whole map by the active owner:

```text
ordinal_dependent_simplex4_map(H)
  := dependent_simplex4_map(H,...),

ordinal_dependent_simplex4_observation(H)
  := ordinal_dependent_simplex4_map(H)
       [ordinal_dependent_simplex4_source].
```

All readable data must be projections of this object.

## 6. Profiles And Negative Evidence

The dimension-four construction must support:

```text
general C       directed/lax four-simplex;
strict profile  the same source under selected profile-local collapses;
Path_cat(A)     the same recursive object in a groupoidal target.
```

The current nested `PathOut` tower is not definitionally one Path category.
Do not add a normalization merely so that a capped `eq_sym` expression
elaborates. Use the strongest existing groupoidal/visible-Path-fibre reading
and record any broader closure prerequisite separately.

Focused negative evidence must include:

1. one wrong tetrahedral face or wrong recursive-frame endpoint rejected;
2. noncollapse of the extracted generic top cell;
3. no reliance on the historical global associativity rule as the source of
   the higher cell; and
4. one retained next action after the constructed four-simplex.

## 7. Variable-Dimensional Source Package

Mapped observation is already generic once a canonical source package is
available. Given

```text
S_n = (c_n,s_n)
  : OrdinalDependentSimplexSource(n)
```

and `H : Functor(Delta[n],C)`, define

```text
c_H := dependent_simplex_code_map_target(H,c_n)
s_H := dependent_simplex_code_map_func(H,c_n)[s_n].
```

This must be implemented as a whole reusable interface before introducing any
new recursion head. It proves that the existing mapped decoder already solves
the arbitrary-target half of the variable-dimensional problem.

The canonical source half is genuinely recursive. At successor dimension,
let

```text
i_n : Delta[n] -> Delta[n+1]
```

be the old-vertex join inclusion. Map `(c_n,s_n)` along `i_n` to `(c'_n,s'_n)`.
Then

```text
c_(n+1) := dependent_simplex_code_step(c'_n,s'_n)
```

decodes to `PathOut(decode(c'_n),s'_n)`. Constructing its canonical object
requires exactly one outgoing arrow from `s'_n` to the new target `n`-simplex.
That arrow is the variable-dimensional join/internal-action successor cell.

The dimension-four audit must decide whether `(c_n,s_n)` alone determines
this cell through the generic join owner, or whether a source stage must also
carry action provenance. If extra data are required, prefer a package such as

```text
OrdinalDependentSimplexStage(n)
  = code + source object + whole successor/action witness
```

over a primitive opaque canonical-source symbol.

## 8. Recursive Implementation Requirements

A completed variable-dimensional implementation must provide:

1. a Nat-indexed internal package type using the existing
   `DependentSimplexCode` and decoded category;
2. a base source at dimension zero;
3. one structural successor clause whose output code is the mapped-and-stepped
   intrinsic code and whose object is built from a whole join/internal-action
   cell;
4. a generic observation-under-`H` operation using only
   `dependent_simplex_code_map`;
5. generic nonempty face observation through `dependent_simplex_face`;
6. selected computations recovering the existing sources in dimensions zero,
   one, two, three, and four at the strongest justified form; and
7. one retained action witnessing that the recursion has not capped the
   omega-tower.

If ordinary Nat recursion cannot express the changing dependent result, use a
curated indexed inductive/recursor analogous to
`RawDependentSimplexCodeData`. This is permitted standard-library
infrastructure. It must be narrowly indexed by the active semantic categories
and must not become a user-facing general inductive-declaration mechanism.

Naming a possible very-dependent recursor without implementing either it or
an equivalent checked successor interface does not complete this goal.

## 9. Relationship To Earlier Deferred Rows

This plan reopens only the source-realization part of the former
`CNB-VERY-DEP-REC` boundary. Intrinsic codes, mapped decoding, and
variable-dimensional nonempty face action are already active and must be
reused.

This plan does not automatically reopen the full `CNB-JOIN-NORMALFORM`
mapping-category problem. A canonical source successor may use the existing
whole propositional join comparisons without making all join-map identity and
composition laws judgmental. Only a concrete failed successor construction
may justify a narrowly scoped additional join comparison.

## 10. Explicit Nonclaims

This plan does not claim or construct:

- an equivalence of whole mapping categories
  `Functor(Delta[n],C) ~= RecursiveSimplex(C,n)`;
- a single unflagged category of all simplices;
- degeneracies, a full simplicial object, horns, Kan, Segal, Rezk, complicial,
  or oriental structure;
- a broad join eta, functor extensionality, Sigma eta, or endpoint normalizer;
- a migration of historical global strict endpoint rules;
- an all-dimensional groupoidal-closure theorem for nested `PathOut`;
- TypeScript/parser work; or
- integration, publication, deployment, or cleanup.

## 11. Module Strategy

Expected modules are:

```text
emdash3_2_dependent_simplex_ordinal_dimension4.lp
  canonical source four-simplex, arbitrary-H image, five face observations,
  recursive final frame, and retained next action;

emdash3_2_dependent_simplex_ordinal_recursive.lp
  Nat-indexed source/stage package, generic mapped observation, structural
  successor, selected computations through dimension four, and generic face
  access.
```

If the dimension-four audit finds one reusable missing owner, place it in a
preceding narrowly named generic module. Edit `emdash3_2.lp` only if an
owner-position full-file probe proves that computation belongs next to an
active primitive owner.

## 12. Implementation Order

```text
baseline and exact retained-action inventory
  -> canonical dimension-four higher input
  -> native Delta[4] source
  -> arbitrary-H whole map and five faces
  -> profiles, negatives, recursive final frame, and next action
  -> generic source-package and mapped-observation interface
  -> structural successor and selected n=0..4 computations
  -> generic face/action handoff
  -> authority synchronization and closeout.
```

At most one ledger row may be `in progress`.

## 13. Validation Policy

Follow `emdash2/AGENTS.md` exactly:

- keep every Lambdapi target within 90 seconds;
- use owner-position full-file probes for any rule or unifier candidate;
- minimize inferred LHS slots and annotate every measured guard;
- validate unifiers with typed `eq_refl`, not only conversion assertions;
- compare quiet and warning-enabled runs for promoted source/reviewer files;
- test both projection orders for any commuting bridge;
- pair positive computation with wrong-endpoint/noncollapse evidence;
- run affected source/reviewer checks, strict LHS audit, catalog, registries,
  and source-only health before checkpoints; and
- eagerly avoid long aggregate checks unless omitting one would block
  trustworthy promotion or final closeout.

Warnings are diagnostic evidence, not an automatic veto. No promoted code may
use `--no-sr-check`.

## 14. Git And Authorization Boundary

The user's instruction to proceed with this next persistent goal authorizes:

- this dedicated local branch/worktree;
- implementation within this plan's scope; and
- SOP-compliant local checkpoint commits after bounded green tranches.

No push, merge, PR, tag, release, npm/Zenodo publication, deployment, history
rewrite, branch/worktree deletion, or unrelated mutation is authorized.

## 15. Execution Ledger

| Row | Status | Deliverable and acceptance boundary |
| --- | --- | --- |
| `ODS4R-00` | complete | Created the dedicated branch/worktree from clean checkpoint `f19fb44`; recorded the fixed dimension-four and variable-source objectives, nonclaims, validation policy, and Git boundary; indexed the plan; and created clean launch checkpoint `9155a73`. |
| `ODS4R-BASE-1` | complete | Native dimension-four, intrinsic code, mapped-decoder, and variable-face sources plus their focused reviewers are green in the new worktree. The immediately preceding dimension-three source/reviewer evidence is carried forward unchanged from checkpoint `7cfc7db`; no long aggregate was run. |
| `ODS4R-OWNER-2` | in progress | Audit the concrete higher input and endpoint ownership of `ordinal_simplex3_top_next_action` against the next parameter-natural join/internal action. The public action is genuinely iterable but is indexed by higher arrows between raw-to-stable source cells, not already by the distinct native tetrahedra 0123/0124. Identify the smallest whole projection and concrete input needed for the dimension-four source; no opaque cell or capped endpoint equation. |
| `ODS4R-SOURCE-3` | pending | Construct the identity-`Delta[4]` native source object in `DependentSimplex4_cat` from the retained recursive action and typed endpoint views. |
| `ODS4R-MAP-4` | pending | Map the one source under arbitrary `H` through `dependent_simplex4_map` and retain the whole map. |
| `ODS4R-FACES-5` | pending | Expose tetrahedral faces 0123, 0124, 0134, 0234, and 1234 plus the top component from the one mapped native object, reusing variable-dimensional face action and the recursive readable frame. |
| `ODS4R-PROFILE-6` | pending | Validate general, selected strict, and exact Path-target readings; reject a wrong recursive endpoint and verify generic top-cell noncollapse. |
| `ODS4R-NEXT-7` | pending | Retain one further whole hom action and record its exact dimension-five handoff without constructing dimension five. |
| `ODS4R-REC-DESIGN-8` | pending | Compare the checked dimension-two, -three, and -four source constructors. Settle the minimal Nat-indexed source/stage package and whether action provenance is required by the structural successor. |
| `ODS4R-REC-IMPLEMENT-9` | pending | Implement the generic source package, arbitrary-`H` mapped observation, and one genuine structural successor using existing code/map/join/internal-action owners or a narrowly curated indexed recursor. |
| `ODS4R-REC-COMPUTE-10` | pending | Check selected source/observation computations through dimensions zero to four, generic nonempty-face access, a wrong-index/endpoint negative, and one retained action. |
| `ODS4R-DOC-11` | pending | Synchronize focused reviewers, both source registries, Foundations, syntax/status, READMEs/AGENTS where affected, report index, catalog, and source-only health. |
| `ODS4R-CLOSE-12` | pending | Review exact evidence and diffs, create clean implementation and closeout checkpoints, and state the achieved variable-dimensional boundary. No long aggregate or unauthorized integration/publication/cleanup. |

## 16. Completion Definition

The fixed dimension-four portion is complete only when one canonical native
source four-simplex and its arbitrary-`H` observation are constructed; all
five tetrahedral faces and the dependent top are accounted for; profiles and
negative evidence pass; and another action remains available.

The whole goal is complete only when the variable-dimensional package and
mapped observation are internal, the canonical source successor is actually
implemented rather than merely proposed, selected dimensions zero through
four agree with the existing sources at the strongest justified form, generic
face access and a retained action pass, affected authorities are synchronized,
and the worktree is clean at green local checkpoints.

A dimension-four success followed only by the name of a future very-dependent
recursor does not satisfy this completion definition. If a genuine repeated
foundational blocker remains after all safe owner/projection alternatives are
exhausted, keep the goal active until the persistent-goal blocked-status rule
permits an explicit blocked closeout.

## 17. Launch And Baseline — 2026-08-21

The branch and worktree were created from clean completed checkpoint
`f19fb44`. Bootstrap installed the worktree-local pnpm link graph and passed
the workspace contract. A non-fatal pnpm update-metadata fetch failed; no
package resolution, lockfile, or workspace contract failed.

Focused Lambdapi baseline evidence and the first exact owner findings are
recorded below.

Launch checkpoint `9155a73` contains only this plan and its report-index
routing. The focused quiet baseline is green for:

```text
emdash3_2_dependent_simplex_dimension4.lp
examples/dependent_simplex_dimension4.lp
emdash3_2_dependent_simplex_codes.lp
examples/dependent_simplex_codes.lp
emdash3_2_dependent_simplex_code_map.lp
examples/dependent_simplex_code_map.lp
emdash3_2_dependent_simplex_faces.lp
examples/dependent_simplex_faces.lp
```

The parent goal checked
`emdash3_2_dependent_simplex_ordinal_dimension3.lp` and its reviewer at the
unchanged implementation checkpoint `7cfc7db`; that exact evidence is carried
forward rather than rerun. Source bytes and Lambdapi environment are unchanged.

The first owner audit distinguishes iterability from readiness. The public

```text
ordinal_simplex3_top_next_action(u,v)
```

is a whole functor on the hom-category between two cells
`u,v : Hom(rawObj,stableObj)`. It does not itself choose the concrete higher
arrow needed to connect native tetrahedra 0123 and 0124 in
`DependentSimplex3_cat`. The dimension-four implementation must therefore
recover that higher input from the next parameter-natural join/internal
action, then transport the resulting cell through the recursive readable
frame. No new native dimension-four classifier, map decoder, or face decoder
is needed.

The variable-dimensional split is also confirmed. For any supplied source
package `(c_n,s_n)`, mapping under arbitrary `H` is already expressible by
`dependent_simplex_code_map_target`, `dependent_simplex_code_map_func`, and
ordinary `fapp0`. The missing canonical recursion is only the successor object
in the outgoing-path category after mapping the previous stage along the old-
vertex join inclusion. `ODS4R-OWNER-2` now audits the dimension-four instance
of precisely that successor.

The first ignored implementation probe,
`tmp/probes/ordinal_simplex4_recursive_source_inventory.lp`, checks this split
inside Lambdapi. It defines the provisional package

```text
Sigma c : DependentSimplexCode(Delta[n],n), Obj(decode(c)),
```

packages `ordinal_dependent_simplex3_source` at `n=3`, and defines the generic
observation of an arbitrary supplied source under
`H : Functor(Delta[n],C)` solely by the existing mapped-code target, mapped
whole functor, and `fapp0`. The probe is green under the 90-second ceiling.
This is positive evidence that neither a new map decoder nor a new
variable-dimensional object package is needed. It does not construct the
canonical successor and therefore does not advance `ODS4R-REC-IMPLEMENT-9`;
the next audit remains the concrete dimension-four higher input.
