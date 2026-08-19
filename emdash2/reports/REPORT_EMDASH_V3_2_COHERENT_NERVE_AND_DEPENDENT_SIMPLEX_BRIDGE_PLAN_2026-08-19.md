# Emdash v3.2 Coherent Nerve And Dependent-Simplex Bridge Plan

Date: 2026-08-19 (America/Toronto)

Plan-ID: `COHERENT-NERVE-DEPENDENT-SIMPLEX-V3.2`

Status: **completed bounded implementation plan**. The architecture, baseline
reuse audit, variable-level facade, four selected tetrahedral cofaces,
first-stage join observation, and variable-dimension face decoder are
complete at their recorded boundaries. The variance audit and recursive
dependent-simplex bridge are also complete, including their three scoped
profile readings. Whole nerve/bridge assembly and a uniform very-dependent
`RecursiveSimplex(C,n)` remain explicitly deferred behind the two named
prerequisites recorded below.

Active-Continuation:
`REPORT_EMDASH_V3_2_DEPENDENT_HOM_SIMPLEX_FOUNDATIONS_PLAN_2026-08-19.md`.
That child plan sharpens the former `CNB-VERY-DEP-REC` placeholder: it first
specifies native dimensions zero through four and the non-circular
Path/groupoidal source-coherence adapter, then derives an emdash-specific
dependent-frame code whose decoder exposes the existing
`Hom_cat`/`Sigma_cat`/`homd_` owners. The completed results in this parent
remain unchanged.

Branch: `goal/coherent-nerve-bridge-v3.2`

Worktree: `/home/user1/emdash1-coherent-nerve-v1`

Baseline: completed simplicial-substrate checkpoint
`e31a812850561f9a6717f11354fd512eaed17671`

Depends-On:

- `emdash3_2.lp`, especially `Functor_cat`, whole precomposition,
  `homd_`, `homd_int`, dependent Sigma, the ordinary/displayed internal
  action, `fapp1_compositor`, and the recursive second action;
- `emdash3_2_simplex_shapes.lp` for Nat-indexed join-built ordinal shapes,
  `join_map_func`, strict face dictionaries, and the selected cofaces through
  dimension two;
- `emdash3_2_semisimplicial_face_codes.lp`,
  `emdash3_2_semisimplicial_index.lp`, and
  `emdash3_2_semisimplicial_diagrams.lp` for the global combinatorial index,
  representable standard semisimplices, and category/groupoid-valued diagrams;
- the completed internal-laxity/groupoidal-realization plan for the
  no-associativity dependent tetrahedron and Path-realized pseudo
  specialization; and
- current Foundations, canonical notation, current SOP, and the persistent
  Git experimentation workflow.

Side-Task-Ledger: `CNB-00`, `CNB-BASE-1`, `CNB-LEVEL-2`,
`CNB-TETRA-FACE-3`, `CNB-JOIN-REC-4`, `CNB-FACE-GEN-5`, `CNB-NERVE-6`,
`CNB-VARIANCE-7A`, `CNB-CELL-7`, `CNB-BRIDGE-8`, `CNB-PROFILE-9`,
`CNB-GENERIC-10`, `CNB-DOC-11`, and `CNB-CLOSE-12`.

Infinity-Codex-Origin: session
`019ffe39-2eb9-7080-88e3-06b77d69b8d1`, especially archived decisions
`0060_2026-08-19T02-13-50Z_01a017c3-1ce8-7232-b9ca-a48584117ad9.md`
and
`0061_2026-08-19T03-03-43Z_01a017f5-0de5-7cc3-887e-90e254494f7f.md`.
Those responses are recovery evidence only. Active code/SOP and this evolving
ledger are authoritative.

## 1. Objective

Construct and validate the missing computational bridge between:

1. the combinatorial standard simplex represented by the internal
   semisimplicial index;
2. the ordinal mapping category `Functor_cat([n],C)`; and
3. the recursive base-cell-plus-dependent-cell presentation already computed
   by `homd_`, dependent Sigma, and the internal action.

The intended whole comparison is

```text
Hom(Delta[n],CoherentNerve(C))
  ~= CoherentNerve(C)[n]
  ~= RecursiveSimplex(C,n).
```

The first equivalence should be existing Yoneda after the nerve is assembled.
The second is the new mathematical content. It must preserve face action and
retain higher hom action, not merely compare object carriers.

The architecture is generic in `n`. Dimension three is the first decisive
acceptance test, because it forces an explicit base associator and a dependent
tetrahedral filler over that associator. It is not the permanent definition of
the generic construction.

## 2. The Four Distinct Current Presentations

Keep these meanings separate:

| Presentation | Current expression | Meaning |
| --- | --- | --- |
| ordinal shape | `DirectedSimplex_cat(n)` | the ordinary category `[n]` with `n+1` vertices |
| representable semisimplex | `StandardSimplex(succ n)` | Yoneda `Delta[n] = Hom(-,[n])` over the injective simplex index |
| category of coherent maps | `Functor_cat(DirectedSimplex_cat(n),C)` | candidate category of `n`-simplices in `C` and transfors between them |
| dependent cell presentation | second and later `homd_`/Sigma iterations | a base cell with a dependent cell above it, recursively |

`Sigma_cat(StandardSimplex(succ n))` is an already-expressible category of
faces and face factorizations, subject to the current Grothendieck orientation.
Because representable fibres are path-discrete, it captures combinatorial
incidence rather than the target-dependent nontrivial higher filler.

The bridge must relate the latter two presentations without identifying
either with the face-incidence total by a broad rewrite.

## 3. Intended Generic Nerve

In ordinary dimension notation, the level classifier is

```text
CoherentNerveLevel(C,n)
  := Functor_cat(DirectedSimplex_cat(n),C).
```

For an injective face code

```text
alpha : FaceCode(succ p,succ n),
```

the intended action is precomposition by a strict realization:

```text
realize_face(alpha)
  : DirectedSimplex_cat(p) -> DirectedSimplex_cat(n)

alpha^*
  : CoherentNerveLevel(C,n) -> CoherentNerveLevel(C,p).
```

When generic face realization and its composition computation exist, these
levels should assemble into

```text
CoherentNerveRaw(C)
  : Functor(Op_cat(SemiDeltaPlus_cat),Cat_cat).
```

The augmented object zero needs an honest empty ordinal shape. This is now a
concrete consumer for the previously deferred augmented-empty endpoint.
Before adding a new shape owner, audit `Path_cat(Empty_grpd)`, functors out of
it, and any existing initial-category facade. If the empty boundary cannot yet
retain the required whole action, a positive-dimension nerve facade may be
used temporarily, but it must not be mislabeled as a functor on all of
`SemiDeltaPlus_cat`.

The public Cat-valued presheaf facade remains distinct from the raw whole
functor-category owner, following the existing semisimplicial realization
policy.

## 4. Join Mapping Data Is The Recursive Step

The shape recursion is already

```text
[0]     = Terminal_cat
[n + 1] = [n] star Terminal_cat.
```

The current `join_elim_func` constructs a functor from `A star B` from:

```text
first  : Functor(A,C)
second : Functor(B,C)
cross  : one whole internally natural cross-cell first ==> second.
```

For `B = Terminal_cat`, this is precisely a cone over the old simplex. Define
or expose a reusable whole classifier schematically as

```text
JoinMapData(A,C)
  = (F : Functor(A,C),
     x : Functor(Terminal_cat,C),
     cross : WholeCross(F,x)).
```

The candidate recursion theorem is

```text
Functor_cat(Join_cat(A,Terminal_cat),C)
  ~= JoinMapData(A,C).
```

Construction from right to left is the existing join eliminator. The missing
left-to-right observation restricts a functor to both join branches and acts
on `join_cross_transf`. Beta/eta and retained hom action determine whether the
comparison is a transparent `DefIso`, an `OmegaEquivAlong Cat_cat`, or a
weaker first-stage observation interface.

Do not postulate a tuple of pointwise cross arrows or an external naturality
family. The cross datum must remain at the existing whole profunctor/transfor
owner.

## 5. Relation Of Join Data To `homd_`

For a fixed new vertex `x`, the whole cross-cell is a coherent family of
arrows from every point of the old simplex to `x`. Its component over an old
base arrow is exactly the kind of cell classified by `homd_`.

The recursive bridge should therefore factor as

```text
map out of [n+1]
  -> whole join-cone data
  -> base simplex plus internally represented dependent hom data.
```

At dimensions two and three, the observations must reduce to the already
selected owners:

```text
n = 2  -> fapp1_compositor
n = 3  -> explicit base associator
          plus the next fdapp1_int_hom_fapp0 dependent filler.
```

The completed no-associativity probe is the semantic and computational
baseline. Do not promote its diagnostic capped pre/post rules, a standalone
tetrahedron constant, or a manual pentagon record.

### 5.1 Variance And Orientation Gate

Before concluding that the ordinary ordinal shape is too weak and escalating
to Street orientals or another richer source, audit whether every missing
boundary is instead a missing variance projection.

The active ordinary contravariant infrastructure includes `hom_con_int`,
`tapp1_con_at_transf`, and `fapp1_con_at_transf`; these already recovered the
pre/right compositor as an opposite specialization of the same internal
action. Contrary to a possible remembered spelling, a displayed
`homd_con_int` is **not** active today. The earlier internal-laxity plan
explicitly classified it as a possible target-internalized displayed mirror
and deferred it because ordinary `hom_con_int` plus opposite specialization
was sufficient for the bounded tetrahedron.

At dimension three, classify any missing face in this order:

1. can it be projected through the active covariant `homd_int` ladder?
2. can its mirror be recovered by `Op`, `hom_con_int`, and the active
   fixed-target ordinary action?
3. does a concrete displayed consumer now require a whole `homd_con_int`
   mirror with retained next action?
4. only if both variance orientations are present and the required oriented
   boundary still cannot be represented should a richer source shape such as
   an oriental be considered.

Do not add `homd_con`, `homd_con_int`, or another mirror merely for notational
symmetry. A promoted mirror must have a concrete missing-face consumer,
projection betas, and retained whole action.

## 6. Why Dimension Three Is The Acceptance Test

The bounded observations are:

```text
n = 0  vertex
n = 1  arrow
n = 2  compositor triangle
n = 3  coherence between two triangle pastings.
```

The tetrahedron must expose all four triangle faces by restriction. Its top
cell must retain:

```text
kappa_assoc
  : h o (g o f) = (h o g) o f

Lambda
  : transport(kappa_assoc,right_pasting) -> left_pasting.
```

The dependent component must be the existing recursive internal-action
projection. Global proof-time associativity may remain installed for the
prototype, but the acceptance probe must not rely on it; use the established
no-associativity comparison technique when the endpoint distinction matters.

Passing dimension three demonstrates one genuinely recursive step. It does
not alone establish a variable-`n` theorem. The variable-`n` row opens only
after the dimension-three data comes from the same join/cone owners intended
for induction.

## 7. Strict, Lax, And Path Profiles

The same bridge should have three readings:

```text
general target Hom   -> directed lax simplex
selected strict map  -> ordinary commuting simplex
Path_cat target      -> invertible pseudo simplex.
```

The selected face realizations themselves are strict-profile maps. The target
simplex classifier should reuse the ambient functor/transfor tower; do not
duplicate it for each profile.

The current kernel remains a documented prototype in which historical global
strict functoriality/naturality endpoint comparisons coexist with nonidentity
laxity cells. This plan does not perform the large profile-aware migration.
Every promoted claim must distinguish endpoint conversion from collapse of
the laxity cell itself.

## 8. Lean/Mathlib Baseline And Adaptation Boundary

Lean/Mathlib already provides:

- the full simplex category as finite monotone maps;
- face and degeneracy generators, normal forms, and epi-mono factorization;
- the semisimplex inclusion;
- the ordinary nerve `N_C[n] = Functor([n],C)`;
- strict Segal and quasicategory results for that nerve; and
- a homotopy-coherent nerve of simplicial categories via enriched functors
  from simplicial thickenings.

These are reference semantics and engineering baselines, not evidence that
emdash should copy their proof-record architecture. The intended emdash
contribution is computational ownership:

```text
one whole internal action
  -> compositor
  -> next coherence
  -> later coherence,
```

with groupoidal specialization obtained by landing in `Path_cat`.

Do not claim that Lean cannot formalize the mathematics. The narrower claim to
test is whether emdash can make the nerve and its coherent-cell reading
compute through one recursively iterable functorial-type-theory mechanism,
where ordinary Lean normally uses structures, propositional laws, and
proof-producing simplification.

Useful primary/current references include:

- Mathlib `SimplexCategory.Basic`, `GeneratorsRelations.NormalForms`, and
  `SemiSimplexCategory`;
- Mathlib ordinary `Nerve`, `StrictSegal`, and `Quasicategory.Nerve`;
- Mathlib `SimplicialNerve` for the enriched homotopy-coherent nerve;
- Street and Johnson--Walters on orientals and the higher nerve;
- Riehl--Shulman on directed shapes, Segal types, and Rezk types; and
- Kolomatskaia--Shulman on display/cone presentations of semisimplicial
  types.

No Lean source is copied into the active kernel. If the ordinary ordinal plus
internal-action approach fails at dimension three, document the exact failure
before considering an emdash oriental or simplicial thickening.

## 9. Explicit Nonclaims

This plan does not initially construct or claim:

- the full simplex category or degeneracies;
- a generic boundary, horn, spine, Segal, Rezk, Kan, or complicial interface;
- a Street oriental or a simplicial thickening;
- a coinductive `SST` facade;
- a complete omega-coherence theorem;
- a broad join eta rewrite or category-head identification;
- a migration of the historical global strict endpoint rules;
- a TypeScript or text-parser surface; or
- integration, publication, or deployment.

Degeneracies are not fundamentally blocked. They are postponed because the
current bridge needs only injective face restriction, and because unitors add
a separate normal-lax/strict-profile question. A later full-simplex plan
should prefer normalized finite monotone maps or another computational normal
form over an unnormalized quotient of face/degeneracy words.

## 10. Proposed Module Strategy

Do not place this bridge in `emdash3_2.lp` unless a focused probe proves a
genuinely missing generic owner.

Candidate one-way modules are:

```text
emdash3_2_coherent_nerve_levels.lp
  variable-n ordinal mapping-category facade and augmented-shape audit

emdash3_2_tetrahedron_faces.lp
  four selected triangle cofaces and their join-built realization

emdash3_2_join_mapping_recursion.lp
  whole restriction/extension interface for maps out of A star 1

emdash3_2_coherent_nerve.lp
  raw semisimplicial nerve, only after generic face realization

emdash3_2_dependent_simplex_bridge.lp
  recursive cell observation and dimension-three comparison.
```

Names may be consolidated after probes show the actual dependency boundary.
Keep examples one-way and reviewer-facing. Do not create a public module for a
failed candidate or a facade whose claimed whole action is absent.

## 11. Validation Policy

Follow the nested Lambdapi SOP:

- inspect staged and unstaged changes separately at every continuation;
- use ignored owner-position probes before active rules;
- keep every Lambdapi target under 90 seconds;
- write inferred rule slots as `_` unless a measured subject-reduction guard
  requires a rigid term, then add the adjacent `lhs-audit` annotation;
- compare quiet and warning-enabled runs for each candidate rewrite family;
- exercise every unifier with typed `eq_refl` and both-order probes;
- pair positive computations with direction/index/non-collapse negatives;
- retain at least one next hom action for every claimed whole owner;
- run source/reviewer checks and the strict LHS audit before each checkpoint;
- update check registries, current status, source inventories, and this ledger
  only for promoted owners; and
- avoid long aggregate checks unless omitting one would genuinely block
  trustworthy promotion.

The focused baseline on 2026-08-19 is green for
`emdash3_2_simplex_shapes.lp`, `emdash3_2_semisimplicial_diagrams.lp`, and
`examples/dependent_hom_laxity.lp`. No aggregate baseline was run.

## 12. Git And Authorization Boundary

The user authorized this dedicated branch/worktree, implementation,
persistent goal, and SOP-compliant local checkpoints. Every checkpoint must:

- contain one bounded green tranche;
- synchronize this ledger and affected active authorities;
- stage only reviewed plan-owned paths; and
- preserve all other branches and worktrees.

No push, merge, PR, tag, npm/Zenodo publication, deployment, history rewrite,
branch/worktree deletion, or unrelated repository mutation is authorized.

## 13. Execution Ledger

| Row | Status | Deliverable and acceptance boundary |
| --- | --- | --- |
| `CNB-00` | complete | Promoted the generic architecture, dimension-three acceptance boundary, Lean comparison, nonclaims, module order, validation policy, and Git boundary into this living plan. |
| `CNB-BASE-1` | complete | Dedicated worktree forked from clean `e31a812`; workspace bootstrap and focused shape/diagram/dependent-hom baselines are green. |
| `CNB-LEVEL-2` | complete | Promoted variable-`n` `CoherentNerveLevel_cat(C,n)`, the separate augmented empty/successor shape, and the augmented mapping-category level. Dimensions 0--3, mapping Homs, retained off-diagonal transfor action, and the dimension/vertex-count noncollapse are checked without a rule or unifier. |
| `CNB-TETRA-FACE-3` | complete | Promoted four strict-profile triangle cofaces `Delta[2] -> Delta[3]`. All six shared edges compute by `FaceCode`; the three old-base comparisons also compute as whole functors. The three new-vertex functor comparisons remain explicit negative conversion checks and route to generic join-map composition rather than a local rule. |
| `CNB-JOIN-REC-4` | complete at first-stage boundary; stronger collage comparison deferred | Whole branch restriction, internally derived cross observation, shaped evaluation, and object-level join extension are active in `emdash3_2_join_mapping_recursion.lp`. A full mapping-category equivalence is the previously named join-as-collage/dependent-elimination research boundary and requires a Cat-valued total of mixed-variance coherent squares, compatibility between action-derived and primitive recursor cross observations, and scoped propositional join uniqueness. The object Sigma is not substituted for that category, and no broad eta rewrite is added. |
| `CNB-FACE-GEN-5` | complete at decoder boundary | `emdash3_2_face_realization.lp` recursively realizes every nonempty raw/public face code in variable dimension. Raw sethood enables public descent; skip/keep and selected low-dimensional branches compute. Whole identity and the first new-vertex composition stop exactly at scoped join identity/composition, so the decoder is not mislabeled as a functor on `SemiDeltaPlus_cat`. |
| `CNB-NERVE-6` | deferred behind `CNB-JOIN-NORMALFORM` | Assemble `CoherentNerveRaw(C)` by precomposition only after `face_realize_func` has owner-aligned whole identity/composition. The current transparent recursion reaches `join_map_func(id,id)` and nested join-map composition; exposing it as an ordinary functor action before those routes join would conflict with the generic strict functor laws. |
| `CNB-VARIANCE-7A` | complete; no new mirror or oriental | All four tetrahedral face functors and their precomposition restrictions exist. Post/left uses `homd_int`/`fapp1_at_transf`; pre/right is recovered through `Op`, `hom_con_int`, and `fapp1_con_at_transf`. The established no-associativity tetrahedron retains the mirrored face, so `homd_con_int` is not a concrete requirement. New-vertex failures are join composition, not orientation. |
| `CNB-CELL-7` | complete | `emdash3_2_dependent_simplex_bridge.lp` exposes the first `homd_`/Sigma triangle, identifies its map with the first hom action of `Sigma(FF)`, and takes its iterable next hom action. A visible `(kappa,lambda)` maps to the same base cell and `fdapp1_int_hom_fapp0(...,lambda)`; the ordinary triangle specializes to `fapp1_compositor`. No standalone tetrahedron is added. |
| `CNB-BRIDGE-8` | deferred behind `CNB-JOIN-NORMALFORM` and `CNB-VERY-DEP-REC` | All four tetrahedral faces and the recursive top-cell action exist, but a whole mapping-category equivalence requires both the join mapping-data/coherent-square uniqueness boundary and a uniform code for the changing recursive boundary type. An object-only Sigma coincidence is explicitly rejected. |
| `CNB-PROFILE-9` | complete with explicit strict scope | `examples/dependent_simplex_profiles.lp` checks a noncollapsed general compositor, the existing strict-code identity fold for that same triangle cell, the Path equality/inverse reading, and an equality/inverse reading of the recursive tetrahedron whenever target fibres are path categories. Strict collapse beyond the selected binary compositor is not claimed without a future higher strict-profile consumer. |
| `CNB-GENERIC-10` | complete decision | Face realization is genuinely generic in `(p,n)`, and the triangle/tetrahedron action is one iterable recursive step. A single Nat-indexed `RecursiveSimplex(C,n)` is not fabricated: its boundary classifier changes dependently with `n` and requires a universe-coded/very-dependent recursor (`CNB-VERY-DEP-REC`). This is independent of the join normal-form gate and does not trigger orientals. |
| `CNB-DOC-11` | complete | Foundations, canonical notation, root/kernel READMEs, current status, nested authority inventory, report index, source/check registries, health snapshot, and this ledger are synchronized to the promoted boundary. |
| `CNB-CLOSE-12` | complete | Seven green local checkpoints are recorded; focused quiet/warning evidence has zero owned diagnostic deltas, strict audit and documentation gates pass, the health snapshot is source-only by explicit aggregate waiver, and no excluded Git/publication operation occurred. |

### 13.1 Variable-Dimension Mapping Levels — 2026-08-19

`emdash3_2_coherent_nerve_levels.lp` now distinguishes ordinary dimension from
augmented vertex count:

```text
CoherentNerveLevel_cat(C,n)
  = Functor_cat(DirectedSimplex_cat(n),C)

AugmentedDirectedSimplex_cat(0)
  = Path_cat(Empty_grpd)

AugmentedDirectedSimplex_cat(succ n)
  = DirectedSimplex_cat(n).
```

The augmented mapping category is defined levelwise from that shape but is not
advertised as a semisimplicial functor. The focused reviewer checks ordinary
dimensions zero through three, the augmented empty level, Functor-category
Homs as transfors, one retained `tapp1_func` action, and noncollapse of empty
vertex count with ordinary dimension zero.

The ignored quiet and warning-enabled probes pass:

```text
logs/probes/coherent_nerve_levels-20260818-231924.log
logs/probes/coherent_nerve_levels-20260818-231945.log
```

Source and reviewer pass quietly and with warnings. Both warning streams
contain the same 1,315 inherited headers and no source/reviewer-owned
diagnostic. The strict LHS audit is empty because the module adds no rule.
This row establishes only a variable-level classifier; generic face
realization, whole nerve action, recursive cell data, and their comparison
remain later rows.

### 13.2 Four Triangle Cofaces Of The Tetrahedron — 2026-08-19

`emdash3_2_tetrahedron_faces.lp` constructs the four inclusions

```text
012, 013, 023, 123 : Delta[2] -> Delta[3].
```

Face `012` is the left join inclusion. The other three are `join_map_func`
applied to old edges `01`, `02`, and `12` together with the identity on the
new terminal vertex. Each is packaged by the existing
`SelectedFaceRealization`, so its `FaceCode` and strict whole functor remain
paired without a generic decoder.

The reviewer checks every shared edge. All six face-code composites compute
to the same code. The three edges `01`, `02`, and `12` wholly inside the old
triangle also agree as composite realized functors. The three edges `03`,
`13`, and `23` do not currently convert as whole functors: each side is a
different nested `join_map_func` presentation of the same computing code.
These are explicit `assertnot` conversion boundaries, not claims that the
functors are mathematically unequal.

The result identifies a precise generic consumer for `CNB-JOIN-REC-4`:
composition/naturality of the whole join mapping operation. No local fold,
functor extensionality axiom, or appeal to orientals is added. The source and
reviewer pass quietly and with warnings; both warning streams contain the
same 1,315 inherited headers and no owned diagnostic. The strict LHS audit is
empty because the module adds no rule.

Ignored probe evidence:

```text
logs/probes/tetrahedron_faces-20260818-232805.log
logs/probes/tetrahedron_faces-20260818-233414.log
logs/probes/tetrahedron_faces-20260818-233436.log
```

### 13.3 First-Stage Join Mapping Observation — 2026-08-19

`emdash3_2_join_mapping_recursion.lp` promotes the part of the join mapping
comparison already supported by generic owners. Precomposition with the two
join inclusions gives whole functors

```text
Functor_cat(Join_cat(A,B),C) -> Functor_cat(A,C)
Functor_cat(Join_cat(A,B),C) -> Functor_cat(B,C),
```

and both retain their generic hom action. The cross observation of an
arbitrary `H` is not postulated: it composes `Prof_func_hom(H)`,
`Prof_reindex_transf`, and `join_cross_transf`. `Prof_cell_eval` therefore
still supplies every shaped component while naturality in the two join
endpoints remains internal. Explicit equality paths relate each whole branch
owner to its readable direct precomposition view without selecting another
runtime normal form.

The module names the nested Sigma only `JoinMapObjectData`. Its projections,
observation, and extension compute, and the extension reduces on both join
branches and at the primitive `join_elim_cross_transf` owner. The reviewer
also checks two intentional negative boundaries:

```text
join_map_observe_cross(join_map_extend_object(d))  !=conv  cross(d)
join_map_extend_object(join_map_observe_object(H)) !=conv  H.
```

These failures isolate, rather than conceal, the remaining architecture. A
morphism between two `(first,second,cross)` triples contains endpoint
transformations together with a mixed-variance coherent square. An ordinary
Sigma family cannot retain that square. The full row therefore requires a
Cat-valued coherent-square total, a comparison between the action-derived and
primitive recursor cross observations, and scoped propositional join
uniqueness. A probe that attempted to install a stable cross owner before that
comparison was available failed its typed semantic check and was discarded;
no rule or unifier was promoted.

Focused source and reviewer checks pass quietly and with warnings. Both
warning streams contain the same 1,315 inherited diagnostic headers and no
owned diagnostic; the source adds no rewrite or unification rule. Evidence:

```text
logs/probes/join_mapping_observation-20260819-002356.log
logs/probes/join_mapping_observation-20260819-002409.log
logs/probes/emdash3_2_join_mapping_recursion-20260819-003913.log
logs/probes/emdash3_2_join_mapping_recursion-20260819-003924.log
logs/probes/join_mapping_recursion-20260819-003919.log
logs/probes/join_mapping_recursion-20260819-003930.log
```

The registered health report was refreshed in source-metrics-only mode. Its
long all-source/all-example timing sweep was deliberately waived under the
goal's aggregate-avoidance policy; the exact focused checks above are the
behavioral evidence for this additive tranche.

### 13.4 Variable-Dimension Face Decoder — 2026-08-19

`emdash3_2_face_realization.lp` resolves the construction half of the generic
face-realization gate. For every nonempty raw code it computes recursively:

```text
realize(skip f) = join_fst o realize(f)
realize(keep f) = join_map(realize(f),id_1).
```

The one-vertex identity and final-vertex cases compute to the ordinary
identity and right join inclusion. `RawFaceCode` is finite indexed skip/keep
syntax and therefore set-valued; the module records that curated evidence and
uses `trunc_rec_ambient`, rather than a new eliminator, to decode public
`FaceCode`. Public visible constructors retain the same computations. The
result is variable in both source and target dimension and is not a
hard-coded tetrahedron dictionary.

The reviewer identifies the exact functoriality boundary. At dimension zero,
the all-keep realization is identity. At the directed edge it is the retained
presentation `join_map_func(id,id)`, not definitionally `id`. A selected
left-branch composition still computes through the join recursor beta, while
the first new-vertex tetrahedral composite does not definitionally equal the
composite of its two realized faces. Thus raw/public realization is active,
but assembling it as a whole functor on `SemiDeltaPlus_cat` requires scoped
propositional join-map identity and composition. No face-specific rule,
unifier, generic strict code, or claim of whole nerve action is added.

Focused source and reviewer checks pass quietly and with warnings. Both
warning streams contain the same 1,315 inherited diagnostic headers and no
owned diagnostic. The four rules have inferred outer slots and pass the
strict LHS audit. Evidence:

```text
logs/probes/raw_face_realization-20260819-005145.log
logs/probes/emdash3_2_face_realization-20260819-005323.log
logs/probes/emdash3_2_face_realization-20260819-005353.log
logs/probes/face_realization-20260819-005333.log
logs/probes/face_realization-20260819-005404.log
```

The health snapshot was again refreshed in source-metrics-only mode; no long
registered aggregate was rerun for this additive decoder tranche.

### 13.5 Variance And Orientation Audit — 2026-08-19

The orientation gate closes without a new owner. The four geometric faces
`012`, `013`, `023`, and `123` are all present as covariant whole functors;
restriction of mapping levels reverses them by the existing whole
precomposition functor. On the dependent-cell side, the matrix is:

| Boundary | Active whole source | Fixed projection |
| --- | --- | --- |
| post/left | `homd_int`, `fapp1_at_transf` | `tapp1_post_laxity_*` |
| pre/right | `Op`, `hom_con_int`, `fapp1_con_at_transf` | `tapp1_pre_laxity_*` |

The earlier current-source no-associativity tetrahedron already constructed
both pasting boundaries and the dependent filler through that matrix. The
current focused `dependent_hom_laxity`, tetrahedral-face, and face-realization
reviewers remain green. In particular, the three new-vertex face-code
composites agree while their functor presentations stop at nested
`join_map_func`; that is positive evidence for a join-composition failure and
negative evidence for a missing variance projection.

Therefore a displayed `homd_con_int` has no concrete missing-face consumer,
and the ordinary ordinal source has not failed its orientation test. Street
orientals or another thickened source are not triggered. Evidence:

```text
logs/probes/dependent_hom_laxity-20260819-010034.log
logs/probes/tetrahedron_faces-20260819-010046.log
logs/probes/face_realization-20260819-010057.log
```

### 13.6 Recursive Dependent Triangle And Tetrahedron — 2026-08-19

`emdash3_2_dependent_simplex_bridge.lp` promotes the reusable part of the
earlier no-associativity experiment rather than naming its selected
three-arrow filler. For fixed total endpoints it exposes

```text
DependentTriangle_catd = homd_(id_E,x,u,y,v)
DependentTriangle_cat  = Op(Sigma(DependentTriangle_catd)).
```

The whole `dependent_triangle_map(FF)` is definitionally the first hom action
of `Sigma(FF)`, with displayed action owned by
`fdapp1_int_presheaf_arrow`. Its next hom action is
`dependent_tetrahedron_map(FF)`. Applying it to the visible second-Sigma
constructor `(kappa,lambda)` computes to

```text
(kappa, fdapp1_int_hom_fapp0(...,kappa,...,lambda)).
```

The reviewer checks both projections and retains the map's next hom action,
so the interface is not capped at dimension three. In the ordinary
specialization based at `X0`, the canonical source triangle over `(g,f)` maps
through the direct internal-action component, and
`fapp1_compositor(F,g,f)` is the same `fdapp1_int_cell`. This satisfies the
dimension-two and dimension-three owner requirements without a manual
tetrahedron, pentagon, external face record, rule, or unifier.

Focused source and reviewer checks pass quietly and with warnings. Each
warning stream has the same 1,315 inherited diagnostic headers and no owned
diagnostic. Evidence:

```text
logs/probes/dependent_simplex_bridge-20260819-011307.log
logs/probes/dependent_simplex_bridge-20260819-011334.log
logs/probes/emdash3_2_dependent_simplex_bridge-20260819-011713.log
logs/probes/emdash3_2_dependent_simplex_bridge-20260819-011750.log
logs/probes/dependent_simplex_bridge-20260819-011723.log
logs/probes/dependent_simplex_bridge-20260819-011800.log
```

The registered health snapshot is refreshed source-only under the standing
aggregate-avoidance policy.

### 13.7 Directed-Lax, Strict, And Path Profiles — 2026-08-19

The profile gate reuses existing classifiers and adds only the reviewer
`examples/dependent_simplex_profiles.lp`.

- For an opaque ambient functor, the bridge's dimension-two
  `fapp1_compositor` does not convert to identity. This preserves the general
  directed-lax reading.
- For a decoded `StrictFunctorData`, that exact compositor reduces to the
  identity at the established strict owner. The claim is intentionally scoped
  to the selected binary compositor: no higher strict-profile code or blanket
  collapse of the shared tetrahedron map is inferred.
- For `path_map_func`, the same compositor is the existing equality between
  paths and `eq_sym` supplies its inverse. More generally, when the target
  fibres of `dependent_tetrahedron_map` are `Path_cat(B)`, the dependent
  tetrahedron component computes as an equality and `eq_sym` again constructs
  its inverse.

Thus the generic bridge is shared rather than duplicated into lax, strict,
and pseudo simplex records. The focused reviewer passes quietly and with
warnings; the warning run has 1,315 inherited diagnostic headers and no owned
diagnostic:

```text
logs/probes/dependent_simplex_profiles-20260819-012806.log
logs/probes/dependent_simplex_profiles-20260819-012815.log
```

### 13.8 Variable-Dimension Decision And Named Prerequisites — 2026-08-19

The implementation establishes two genuinely generic axes:

1. `face_realize_func` is recursive in arbitrary nonempty source and target
   dimensions; and
2. `dependent_triangle_map` followed by
   `dependent_tetrahedron_map` demonstrates that the same internal action can
   be iterated without capping its next hom action.

They do not yet combine into one Nat-indexed theorem. The blockers are now
separated precisely.

`CNB-JOIN-NORMALFORM` is the whole-shape prerequisite. At the directed edge,
the all-keep code realizes to `join_map_func(id,id)` rather than the ordinary
identity. At the first new-vertex tetrahedral composite, recursive realization
and composition produce distinct nested join-map presentations. Declaring
these as the hom action of an ordinary functor would make the kernel's generic
strict functor laws demand exactly those missing identity/composition joins.
A future task must choose and audit a stable join-map owner plus narrowly
scoped identity/composition computation, or a profile-aware coherent-map
classifier. It must not install a broad join eta or hide the issue under a
face-specific fold.

`CNB-VERY-DEP-REC` is the recursive-boundary prerequisite. The type of an
`n+1`-simplex contains the entire `n`-boundary together with a cell in a
family whose classifier depends on that boundary. Although every fixed
triangle/tetrahedron step is now executable, ordinary Nat recursion into a
single fixed category cannot express this changing telescope directly. A
future universe-coded boundary description, or another curated
very-dependent recursion interface, must internalize that changing type
before the repository can claim a uniform `RecursiveSimplex(C,n)`.

Neither failure is a variance failure. Both orientations needed at dimension
three are active, and the ordinary ordinal tetrahedron supplied all four faces
and the top dependent action. Therefore Street orientals, simplicial
thickenings, degeneracies, and codata remain untriggered research options, not
repairs for the current bounded result.

### 13.9 Checkpoints And Closeout — 2026-08-19

The bounded history is:

```text
7793f4f  Plan the coherent nerve bridge
102c8e5  Add coherent nerve level classifiers
bcfa5aa  Add the tetrahedron triangle cofaces
9a0665c  Add first-stage join mapping observation
61f5d8c  Realize semisimplex faces in variable dimension
6adb5ba  Expose the recursive dependent simplex bridge
d98ea6c  Validate dependent simplex profiles
```

Every behavioral tranche has focused quiet and warning-enabled source/
reviewer evidence recorded in its subsection. Promoted modules add four
owner-local face-realization rules in a fresh head and no other rewrite or
unification rule; the strict inferred-slot audit is green. Active-reference,
report-header, source-TOC, catalog, and health-snapshot checks pass. The health
report is deliberately source-metrics-only because the user explicitly
waived the long all-source/all-example aggregate unless it became necessary;
the focused checks were sufficient for these additive boundaries.

No push, merge, PR, tag, publication, deployment, history rewrite,
branch/worktree removal, or unrelated repository mutation was performed.

## 14. Completion Definition

This goal is complete when every row is complete or explicitly deferred
behind a named, evidence-backed prerequisite; the variable-`n` interface has
not been replaced by a hard-coded tetrahedron API; every promoted whole owner
retains the action it claims; dimension three either computes the four faces
and dependent top filler from generic owners or records a precise architectural
failure; strict and Path specializations state their exact scope; the living
ledger and active documentation agree; the worktree is clean at green local
checkpoints; and no excluded Git/publication/aggregate operation has occurred.

This definition is satisfied at the bounded boundary above. The two deferred
rows name exact prerequisites rather than incomplete hidden work; reopening
either requires a new plan that explicitly selects `CNB-JOIN-NORMALFORM` or
`CNB-VERY-DEP-REC`.
