# Emdash v3.2 Ordinal Dimension-Four And Recursive-Source Plan

Date: 2026-08-21 (America/Toronto)

Plan-ID: `ORDINAL-DEPENDENT-SIMPLEX-DIMENSION-FOUR-RECURSIVE-SOURCE-V3.2`

Status: **completed implementation plan**. This child plan first constructs the
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
| `ODS4R-OWNER-2` | complete | The missing operation is the generic whole outgoing-path lift of an ordinary transformation, not a dimension-specific input to `ordinal_simplex3_top_next_action`. `emdash3_2_pathout_transformation_reframing.lp` connects the formal pre/right source to the constructor-visible Sigma source through existing typed paths; `emdash3_2_pathout_transformation_lift.lp` totalizes the existing pre/right laxity cell into `pathout_transf_lift`, computes its constructor component, and retains generic `tapp1_func`. Source, reviewer, warning, and LHS audits are green without a core edit, endpoint collapse, runtime normalization, or proof-time unifier. |
| `ODS4R-SOURCE-3` | complete | `emdash3_2_ordinal_join_pathout_successor.lp` packages the generic identity-join shaped comparison for arbitrary `A * 1`. `emdash3_2_dependent_simplex_ordinal_dimension4.lp` lifts it at the canonical source edge and triangle; the component at `ordinal_dependent_simplex3_source` is `ordinal_simplex4_omega`, and pairing it with its endpoints constructs one actual object of the existing `DependentSimplex4_cat`. The constructor beta identifies the cell with the generic `pathout_transf_component`; no filler is postulated. |
| `ODS4R-MAP-4` | complete | `ordinal_dependent_simplex4_map(H)` is the existing `dependent_simplex4_map`, and `ordinal_dependent_simplex4_observation(H)` is its action on the one canonical source. The mapped intrinsic code is exposed in parallel through the existing code-map target. |
| `ODS4R-FACES-5` | complete | Native projections expose 0123, 0124, 0134, the recursive readable cell, and top component. Five explicit coface codes and the one generic `ordinal_dependent_simplex4_face(H,alpha)` expose 0123, 0124, 0134, 0234, and 1234 through the existing variable-dimensional face action. Native and code-selected faces remain parallel whole presentations; no unqualified mapping-category equality is claimed. |
| `ODS4R-PROFILE-6` | complete | The focused reviewer checks the general observation, selected strict carrier, exact `Path_cat` target, wrong recursive source rejection, and generic top-cell noncollapse. No global associativity or new endpoint conversion is used. |
| `ODS4R-NEXT-7` | complete | `ordinal_simplex4_top_next_action(u,v)` retains `tapp1_func` of the second lifted transformation and records the exact dimension-five handoff without constructing a fifth-level source. |
| `ODS4R-REC-DESIGN-8` | complete | The minimal varying package reuses existing `DependentSimplexObservation(Delta[n],n)`. A nonzero raw intrinsic code determines `OrdinalJoinLiftStage`: target code, two whole maps `F,G`, and `epsilon : F => G`. The one-flag clause uses `ordinal_join_pathout_transf`; each further flag applies `pathout_transf_lift`. No separate source-code grammar or stored parallel omega-category data is required. |
| `ODS4R-REC-IMPLEMENT-9` | complete | `emdash3_2_dependent_simplex_ordinal_recursive.lp` implements the indexed stage fold, zero/nonzero source successor, `nat_elim` canonical source, arbitrary-`H` observation through the existing mapped decoder, generic nonempty-face access, canonical successor cell, and retained whole action. The successor is exactly `code' = step(d,F[s])`, `source' = (G[s],epsilon[s])`. |
| `ODS4R-REC-COMPUTE-10` | complete | The reviewer checks stage computation at one, two, and three stored flags; zero and generic successor beta; selected source-object computations through dimensions zero to four; variable-dimensional observation and face access; a wrong face-index negative; successor-cell noncollapse; and a retained generic next action. |
| `ODS4R-DOC-11` | complete | Registered the generic successor, fixed dimension four, and recursive sources in both source registries; added focused reviewers; synchronized AGENTS, emdash2 README, Foundations, syntax/status, report index, and this ledger; refreshed the assertion catalog and source TOC; and refreshed/verified the no-check source-health snapshot. |
| `ODS4R-CLOSE-12` | complete | Reviewed exact evidence and diffs; checkpointed the generic transformation lift at `5a6be0e`, fixed dimension four at `67296e9`, and the Nat-indexed recursive implementation plus synchronized authorities at `226097a`; refreshed the source-health snapshot; and prepared this clean closeout checkpoint. No long aggregate or unauthorized integration/publication/cleanup was performed. |

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

## 18. Generic Outgoing-Path Transformation Successor — 2026-08-21

The dimension-four owner audit found a more general successor than the
provisional direct use of `ordinal_simplex3_top_next_action`. For
`epsilon : F => G` and fixed `x : A`, the checked whole owner is

```text
pathout_transf_lift(epsilon,x)
  : pathout_map_func(F,x)
      => ((y,p) |-> (G[y],epsilon[p])).
```

Its component at `(y,p)` is one `sigma_arrow`. The base is `epsilon[y]`; the
fibre is the already-derived `tapp1_pre_laxity_cell(epsilon,p,id_y)`. The
formal source and target of that laxity cell do not become new runtime normal
forms. Instead, `emdash3_2_pathout_transformation_reframing.lp` composes the
existing first-class comparisons through stable postcomposition, raw
composition, general precomposition, the Cat-valued telescope, and whole
Functord transport. Equality-induced hom action then reframes the cell into
the literal Sigma endpoints.

The implementation has exactly one constructor-visible component beta for
`pathout_transf_lift`; its LHS uses inferred `_` slots and passes the strict
LHS audit. The whole transformation's generic `tapp1_func` is deliberately
unreduced and therefore supplies the next higher action. Focused quiet and
warning-enabled checks pass for both sources and the reviewer. The reviewer
checks both endpoint paths, the extracted fibre cell, the total component,
the component beta, and retained next action; it also rejects a wrong indexed
endpoint and an arbitrary replacement fibre.

No edit to `emdash3_2.lp`, primitive `piapp*` redesign, broad Sigma eta,
simplex-specific rule, endpoint equality, or proof-time unifier was needed.
This closes the generic owner prerequisite. `ODS4R-SOURCE-3` must now
instantiate this successor at the ordinal dimension-three stage and package
the resulting object in the existing `DependentSimplex4_cat`; it must not
copy the source-reframing chain or introduce another opaque filler.

The required source-health refresh was attempted after registering the two
files, but `make health --resume` did not reuse the prior aggregate evidence
as expected and began rechecking unrelated sources. It was interrupted rather
than allowed to become the long aggregate prohibited by this goal. No health
report was written. The two new sources and their focused reviewer were each
checked directly and are green; the stable health-report refresh remains
explicitly owned by `ODS4R-DOC-11` at the final affected-source boundary.

## 19. Fixed Dimension Four — 2026-08-21

The fixed dimension-four slice is complete. The implementation first factors
the join prelude out of the historical tetrahedron module. For every category
`A`, `ordinal_join_pathout_transf(A,x0)` is the shaped outgoing-path
comparison induced by the identity join extension of `A * 1`. It is generic
in both `A` and the fixed source `x0`.

For `A = Delta[3]`, the checked recursion is

```text
epsilon1 := ordinal_join_pathout_transf(Delta[3],x0)
epsilon2 := pathout_transf_lift(epsilon1,e01)
epsilon3 := pathout_transf_lift(epsilon2,t012)
omega01234 := epsilon3[s0123]
source4 := (s0124,omega01234).
```

Here `s0123` is the already-constructed canonical ordinal tetrahedron. The
last component beta reduces to the generic `pathout_transf_component`, so the
fourth-level cell is derived from the existing pre/right laxity action rather
than supplied by an opaque constant. The result inhabits the existing native
`DependentSimplex4_cat` without a cast.

The arbitrary-target observation is the image of this single source under
`dependent_simplex4_map(H)`. Its intrinsic `dependent_simplex_code4` view maps
through `dependent_simplex_code_map_target`. Five visible coface codes—one
skip at each of the five vertex positions—are interpreted by the existing
`dependent_simplex_face_func`; this gives whole observations named 0123,
0124, 0134, 0234, and 1234. Separately, the native Sigma projections retain
the source, target, base tetrahedron, readable residual, and dependent top
component.

The code-selected and native faces have compatible intended geometry but do
not become judgmentally equal merely because they describe the same coface:
their codomains retain different intrinsic-code and projection histories.
The failed stronger probe was therefore rejected rather than answered by a
normalization or extensionality rule. A future whole mapping-category
comparison may relate them; it is not required for the canonical source or
generic face observation.

Focused source and reviewer checks are green. The reviewer also checks the
selected strict and exact Path targets, wrong recursive endpoint rejection,
top-cell noncollapse, and `ordinal_simplex4_top_next_action`. The next active
row is `ODS4R-REC-DESIGN-8`: extract the generic iterator implicit in the
two-lift dimension-four construction and package its varying code/category
indices without duplicating the existing intrinsic-code semantics.

## 20. Nat-Indexed Source Recursion — 2026-08-21

The dimension-four pattern internalizes without a new general very-dependent
eliminator. The existing intrinsically indexed
`RawDependentSimplexCodeData(C,n,K)` is already the correct recursion spine.
For every nonzero code, the new `OrdinalJoinLiftStage(A,n,K)` packages:

```text
B       target decoded category,
d       raw target code in A * 1,
F,G     whole functors K -> B,
epsilon transformation F => G.
```

The base clause for a one-flag code is
`ordinal_join_pathout_transf(A,x0)`. The recursive clause for a new flag `x`
replaces

```text
(d,F,G,epsilon)
```

by

```text
(step(d,F[x]),
 pathout_map_func(F,x),
 pathout_transf_target_func(F,G,epsilon,x),
 pathout_transf_lift(epsilon,x)).
```

This fold is implemented by the constructor-scoped
`raw_ordinal_join_lift_stage` rules. Their inferred LHS slots pass the strict
audit, and warning-enabled checking reports no warning owned by the new file.

The generalized source package is not duplicated: the implementation reuses
the existing `DependentSimplexObservation(C,n)`. At dimension zero the
successor evaluates the primitive join cross on `(x0,id_x0)`. At every
nonzero dimension, if the stage is `(d,F,G,epsilon)` and the old source is
`s`, then

```text
new code   = step(d,F[s]),
new source = (G[s],epsilon[s]).
```

`OrdinalDependentSimplexSource(n)` is the specialization
`DependentSimplexObservation(Delta[n],n)`, and
`ordinal_dependent_simplex_source(n)` is a genuine `nat_elim` value with the
structural successor above. `ordinal_dependent_simplex_observation(H)` reuses
`dependent_simplex_code_map_func`; `ordinal_dependent_simplex_face(H,alpha)`
reuses `dependent_simplex_face_func`. The canonical nonzero stage exposes
both `ordinal_dependent_simplex_successor_cell` and
`ordinal_dependent_simplex_lift_next_action`.

The focused reviewer establishes constructor computation for stages with one,
two, and three stored flags, generic Nat successor beta, selected source
objects through dimensions zero to four, arbitrary-target mapping, generic
nonempty-face access, wrong-index rejection, noncollapse, and retained higher
action. The finite hand-built sources remain useful readable validation
slices; the new recursion does not claim judgmental equality with every
historical presentation or the still-deferred equivalence of whole mapping
categories.

## 21. Proportional Validation Boundary — 2026-08-21

The promoted recursive source and its reviewer check green directly under the
90-second ceiling. The recursive module also checks with warnings enabled and
introduces no warning at its own source path. Strict LHS audit reports zero
unreviewed reconstructible slots: the two constructor-scoped recursive rule
families are exercised through one-, two-, and three-flag reviewer
computations. The fixed dimension-four source/reviewer and its two generic
prerequisite modules retain their earlier green evidence.

`make catalog` and `make toc` pass. The source-health snapshot was refreshed
and verified with `scripts/check_metrics.py --no-check`; this matches the
report's existing blank-timing policy and records all 268 registered source
and reviewer files without launching an aggregate. No `make check`,
`make examples`, `make ci`, or repository-wide aggregate was run. The earlier
attempted resumable health aggregate remains explicitly interrupted evidence,
not a passing gate.

The achieved boundary is stronger than the original finite extrapolation:
the repository now contains both a checked ordinal four-simplex and an
internal canonical source at variable dimension. It still does not claim a
whole mapping-category equivalence, degeneracies, an all-dimensional Kan or
Segal theorem, or judgmental equality between every historical finite source
and the new uniform presentation.

## 22. Closeout — 2026-08-21

All ledger rows are complete. The fixed and variable-dimensional objectives
both satisfy the completion definition: a canonical native ordinal
four-simplex is checked with five faces, profiles, negatives, top component,
and retained action; and a genuine internal Nat-indexed source, successor,
arbitrary-target observation, generic face access, selected zero-through-four
computations, noncollapse, and retained action are checked.

The implementation checkpoints are:

```text
5a6be0e  generic whole PathOut transformation lift
67296e9  generic identity-join successor and ordinal four-simplex
226097a  Nat-indexed ordinal source recursion and synchronized authorities.
```

The branch remains local. No push, merge, publication, deployment, branch or
worktree removal, history rewrite, or unrelated mutation is included. Future
work may compare the uniform sources with historical finite presentations at
the whole mapping-category level, add degeneracies or Kan/Segal structure, or
develop broader nested-PathOut groupoidal closure; none is a missing item of
this completed bounded goal.
